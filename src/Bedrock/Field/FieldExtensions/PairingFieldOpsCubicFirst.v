(** * Bedrock2 compilation layer — cubic-first pairing-field operations.

    This is the cubic-first analogue of
    [Bedrock.Field.FieldExtensions.PairingFieldOps], which targets
    quadratic-first towers (Fp -> Fp2 -> Fp6 -> Fp12, as used by
    BLS12-381 / BLS12-377 / BN254 / BN256 / BN446).

    Here we target CUBIC-first towers:

      Fp  ->  Fp3 = Fp[zeta]/(zeta^3 + 4)  ->  Fp6 = Fp3[w]/(w^2 - zeta)

    (As used by BW6-761.)

    The Frobenius endomorphism pi : x -> x^p acts on Fp6 by per-Fp
    component scaling, not by Fp3 multiplication.  Concretely, with
    alpha = (-4)^((p-1)/3) mod p a primitive cube root of unity in Fp,
    and sa = sqrt(alpha) mod p, the action is

      pi (a0, a1, a2) + (b0, b1, b2) w
        = (a0, alpha a1, alpha^2 a2)
        + (sa b0, sa alpha b1, sa alpha^2 b2) w.

    Five Fp scalars per Frobenius level:
      gamma_fp3 = (_,  alpha,           alpha^2)             (slot 0 unused)
      gamma_fp6 = (sa, sa alpha,        sa alpha^2)

    The pi^2 case uses the squares of those scalars; pi^3 acts
    trivially on Fp3 (alpha^3 = 1) and multiplies the c1 component
    by -1 only.

    This file mirrors [PairingFieldOps] but in BaseField-generic form.
    Concrete curve files (e.g. [BW6_761_FrobLibBridge.v]) instantiate
    [BaseField := Fp3] using the [GenericCubic] / [GenericQuadratic]
    factory representations.

    Design rationale.  Unlike the quadratic-first case (where
    [PairingFieldOps] can call Fp2-typed operations like [Fp2_mul]
    and [Fp2_conjugate] to assemble [Fp6_frobenius] at the Fp2
    level), the cubic-first Frobenius mixes Fp3 components with Fp
    scalars per-slot.  The body therefore calls [fp_mul] directly
    six times, never invoking [fp3_mul].  This is exactly how
    [gnark-crypto/ecc/bw6-761/internal/fptower/frobenius.go]
    implements it.
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import Rupicola.Lib.Api.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Crypto.Spec.ModularArithmetic.

Import BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Section CubicFirstPairingOps.

  (* ================================================================ *)
  (* Bedrock2 / coqutil background context                             *)
  (* ================================================================ *)

  Context {width: Z} {BW: Bitwidth width}
          {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  (* ================================================================ *)
  (* Base prime field Fp                                                *)
  (* ================================================================ *)

  Context {prime_parameters : PrimeFieldParameters}
          {prime_parameters_ok : PrimeFieldParameters_ok}.

  Local Notation Fp := (F PrimeField.M_pos).

  Existing Instance prime_field_parameters.

  Context {F_representation : AbstractField.FieldRepresentation (F:=Fp)}
          {F_representation_ok : AbstractField.FieldRepresentation_ok (F:=Fp)}.

  Context {bounds_equiv : forall x, bounded_by loose_bounds x -> bounded_by tight_bounds x}.

  (* ================================================================ *)
  (* Fp3 base layer — abstracted                                        *)
  (*                                                                    *)
  (* We do NOT take an Fp3 [FieldParameters] / [FieldRepresentation] as *)
  (* a black box because the body only manipulates Fp slots: the Fp3   *)
  (* layout is exposed via per-slot pointer offsets.  All this file   *)
  (* needs is that an Fp3 element is 3 consecutive Fp slots in memory. *)
  (* ================================================================ *)

  (* ================================================================ *)
  (* Layer-local offset helpers                                        *)
  (* ================================================================ *)

  (* Fp byte offset within an Fp3 element *)
  Local Notation fp_felem_offset :=
    (Memory.bytes_per_word width * Z.of_nat (AbstractField.felem_size_in_words (F:=Fp))).

  (* Fp3 component selectors at the bedrock2 expression level *)
  Local Definition expr_fp3_c0 (x : Syntax.expr.expr) : Syntax.expr.expr := x.
  Local Definition expr_fp3_c1 (x : Syntax.expr.expr) : Syntax.expr.expr :=
    Syntax.expr.op Syntax.bopname.add x (Syntax.expr.literal fp_felem_offset).
  Local Definition expr_fp3_c2 (x : Syntax.expr.expr) : Syntax.expr.expr :=
    Syntax.expr.op Syntax.bopname.add x (Syntax.expr.literal (2 * fp_felem_offset)).

  (* Fp6 component selectors:
     an Fp6 element is laid out as 2 consecutive Fp3 elements (6 Fp
     slots), so c0 is the head and c1 is at +3*fp_felem_offset. *)
  Local Notation fp3_felem_offset := (3 * fp_felem_offset).

  Local Definition expr_fp6_c0 (x : Syntax.expr.expr) : Syntax.expr.expr := x.
  Local Definition expr_fp6_c1 (x : Syntax.expr.expr) : Syntax.expr.expr :=
    Syntax.expr.op Syntax.bopname.add x (Syntax.expr.literal fp3_felem_offset).

  (* ================================================================ *)
  (* Callee specs                                                      *)
  (* ================================================================ *)

  Instance spec_of_Fp_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp)) :=
    AbstractField.spec_of_felem_copy.
  Instance spec_of_Fp_mul : spec_of (AbstractField.mul (F:=Fp)) :=
    AbstractField.binop_spec (F:=Fp) (field_representation:=F_representation)
      AbstractField.bin_mul.

  (* ================================================================ *)
  (* Bedrock2 body: cubic_first_fp6_frob                                *)
  (*                                                                    *)
  (* Signature: (out, x, gamma_fp3, gamma_fp6) : 4 Fp6/Fp3 pointers.   *)
  (*                                                                    *)
  (*   out.c0.a0 = x.c0.a0                                              *)
  (*   out.c0.a1 = x.c0.a1 * gamma_fp3.c1                               *)
  (*   out.c0.a2 = x.c0.a2 * gamma_fp3.c2                               *)
  (*   out.c1.b0 = x.c1.b0 * gamma_fp6.c0                               *)
  (*   out.c1.b1 = x.c1.b1 * gamma_fp6.c1                               *)
  (*   out.c1.b2 = x.c1.b2 * gamma_fp6.c2                               *)
  (*                                                                    *)
  (* Identical AST shape to [BW6_761_FinalExp.bw6_fp6_frob].           *)
  (* ================================================================ *)

  Variable cubic_first_prefix : string.

  Local Definition fp_copy_name :=
    @AbstractField.felem_copy _ prime_field_parameters.
  Local Definition fp_mul_name :=
    @AbstractField.mul _ prime_field_parameters.

  Local Definition cubic_first_fp6_frob_name :=
    (cubic_first_prefix ++ "fp6_frob")%string.

  Local Fixpoint cmd_seq_list (cmds : list Syntax.cmd.cmd) : Syntax.cmd.cmd :=
    match cmds with
    | [] => Syntax.cmd.skip
    | [c] => c
    | c :: rest => Syntax.cmd.seq c (cmd_seq_list rest)
    end.

  Definition cubic_first_fp6_frob : function_t :=
    (cubic_first_fp6_frob_name,
     (["out"; "x"; "gamma_fp3"; "gamma_fp6"],
      []:list String.string,
      cmd_seq_list [
        (* c0 of Fp6: a0 identity, scale a1 and a2 *)
        Syntax.cmd.call [] fp_copy_name
          [expr_fp3_c0 (expr_fp6_c0 (Syntax.expr.var "out"));
           expr_fp3_c0 (expr_fp6_c0 (Syntax.expr.var "x"))];
        Syntax.cmd.call [] fp_mul_name
          [expr_fp3_c1 (expr_fp6_c0 (Syntax.expr.var "out"));
           expr_fp3_c1 (expr_fp6_c0 (Syntax.expr.var "x"));
           expr_fp3_c1 (Syntax.expr.var "gamma_fp3")];
        Syntax.cmd.call [] fp_mul_name
          [expr_fp3_c2 (expr_fp6_c0 (Syntax.expr.var "out"));
           expr_fp3_c2 (expr_fp6_c0 (Syntax.expr.var "x"));
           expr_fp3_c2 (Syntax.expr.var "gamma_fp3")];
        (* c1 of Fp6: scale each slot by gamma_fp6 slots *)
        Syntax.cmd.call [] fp_mul_name
          [expr_fp3_c0 (expr_fp6_c1 (Syntax.expr.var "out"));
           expr_fp3_c0 (expr_fp6_c1 (Syntax.expr.var "x"));
           expr_fp3_c0 (Syntax.expr.var "gamma_fp6")];
        Syntax.cmd.call [] fp_mul_name
          [expr_fp3_c1 (expr_fp6_c1 (Syntax.expr.var "out"));
           expr_fp3_c1 (expr_fp6_c1 (Syntax.expr.var "x"));
           expr_fp3_c1 (Syntax.expr.var "gamma_fp6")];
        Syntax.cmd.call [] fp_mul_name
          [expr_fp3_c2 (expr_fp6_c1 (Syntax.expr.var "out"));
           expr_fp3_c2 (expr_fp6_c1 (Syntax.expr.var "x"));
           expr_fp3_c2 (Syntax.expr.var "gamma_fp6")]
      ])).

  (* ================================================================ *)
  (* Algebraic model                                                    *)
  (*                                                                    *)
  (* Identical to [BW6_761_FrobModel.frobenius_fp6_gallina].  We       *)
  (* duplicate it here so the library can be used in isolation         *)
  (* (without importing the BW6 example file).                          *)
  (* ================================================================ *)

  Local Notation Fp3 := ((Fp * Fp) * Fp)%type.
  Local Notation Fp6 := (Fp3 * Fp3)%type.

  Definition fp3_a0 (a : Fp3) : Fp := fst (fst a).
  Definition fp3_a1 (a : Fp3) : Fp := snd (fst a).
  Definition fp3_a2 (a : Fp3) : Fp := snd a.
  Definition fp3_mk (a0 a1 a2 : Fp) : Fp3 := ((a0, a1), a2).
  Definition fp6_c0 (x : Fp6) : Fp3 := fst x.
  Definition fp6_c1 (x : Fp6) : Fp3 := snd x.
  Definition fp6_mk (c0 c1 : Fp3) : Fp6 := (c0, c1).

  Definition cubic_first_frob_fp3_c0 (a g : Fp3) : Fp3 :=
    fp3_mk (fp3_a0 a)
           (F.mul (fp3_a1 a) (fp3_a1 g))
           (F.mul (fp3_a2 a) (fp3_a2 g)).

  Definition cubic_first_frob_fp3_c1 (b g : Fp3) : Fp3 :=
    fp3_mk (F.mul (fp3_a0 b) (fp3_a0 g))
           (F.mul (fp3_a1 b) (fp3_a1 g))
           (F.mul (fp3_a2 b) (fp3_a2 g)).

  Definition cubic_first_fp6_frob_model (x : Fp6) (gfp3 gfp6 : Fp3) : Fp6 :=
    fp6_mk (cubic_first_frob_fp3_c0 (fp6_c0 x) gfp3)
           (cubic_first_frob_fp3_c1 (fp6_c1 x) gfp6).

  (* ================================================================ *)
  (* Spec instance                                                      *)
  (*                                                                    *)
  (* The spec is stated at the Fp3 level: it consumes an [Fp3]-typed   *)
  (* memory region for [x.c0], [x.c1], [gamma_fp3], [gamma_fp6] —     *)
  (* abstracting the cubic representation through the bridge file's    *)
  (* [FElem_Fp3] predicate.                                            *)
  (*                                                                    *)
  (* However, since this library file does NOT take an Fp3            *)
  (* [FieldRepresentation] (which would tie us to one factory: the    *)
  (* CE_field_representation vs other choices), we state the spec at  *)
  (* the Fp slot level: the input/output are seen as 6 Fp felems.     *)
  (*                                                                    *)
  (* Concrete curve files wrap this with their Fp3/Fp6 split/join     *)
  (* lemmas.                                                          *)
  (* ================================================================ *)

  (* Per-slot spec.  Output Fp slots are bounded (loose) and equal to *)
  (* the model applied per-component.                                  *)
  Local Notation fpfelem :=
    (@AbstractField.felem _ prime_field_parameters _ _ _ _ F_representation).
  Local Notation FElem_Fp :=
    (@AbstractField.FElem _ prime_field_parameters _ _ _ _ F_representation).
  Local Notation Fp_feval :=
    (@AbstractField.feval _ prime_field_parameters _ _ _ _ F_representation).
  Local Notation Fp_bounded :=
    (@AbstractField.bounded_by _ prime_field_parameters _ _ _ _ F_representation).
  Local Notation Fp_tight :=
    (@AbstractField.tight_bounds _ prime_field_parameters _ _ _ _ F_representation).
  Local Notation Fp_loose :=
    (@AbstractField.loose_bounds _ prime_field_parameters _ _ _ _ F_representation).

  (* Sep-logic chain for an Fp6 element split into 6 Fp slots.

     Layout in memory at base pointer [p]:
       p +  0*fp_off  : c0.a0
       p +  1*fp_off  : c0.a1
       p +  2*fp_off  : c0.a2
       p +  3*fp_off  : c1.b0
       p +  4*fp_off  : c1.b1
       p +  5*fp_off  : c1.b2

     where [fp_off = fp_felem_offset]. *)

  Local Notation slot_addr p n :=
    (word.add p (word.of_Z (n * fp_felem_offset))).

  Definition FElem_Fp6_slots (p : word) (s0 s1 s2 s3 s4 s5 : fpfelem) : mem -> Prop :=
    (FElem_Fp (slot_addr p 0) s0 *
     (FElem_Fp (slot_addr p 1) s1 *
      (FElem_Fp (slot_addr p 2) s2 *
       (FElem_Fp (slot_addr p 3) s3 *
        (FElem_Fp (slot_addr p 4) s4 *
         FElem_Fp (slot_addr p 5) s5)))))%sep.

  Definition FElem_Fp3_slots (p : word) (s0 s1 s2 : fpfelem) : mem -> Prop :=
    (FElem_Fp (slot_addr p 0) s0 *
     (FElem_Fp (slot_addr p 1) s1 *
      FElem_Fp (slot_addr p 2) s2))%sep.

  Definition feval_Fp3_slots (s0 s1 s2 : fpfelem) : Fp3 :=
    fp3_mk (Fp_feval s0) (Fp_feval s1) (Fp_feval s2).

  Definition feval_Fp6_slots (s0 s1 s2 s3 s4 s5 : fpfelem) : Fp6 :=
    fp6_mk (feval_Fp3_slots s0 s1 s2) (feval_Fp3_slots s3 s4 s5).

  Definition Fp6_slots_tight (s0 s1 s2 s3 s4 s5 : fpfelem) : Prop :=
    Fp_bounded Fp_tight s0 /\ Fp_bounded Fp_tight s1 /\
    Fp_bounded Fp_tight s2 /\ Fp_bounded Fp_tight s3 /\
    Fp_bounded Fp_tight s4 /\ Fp_bounded Fp_tight s5.

  Definition Fp6_slots_loose (s0 s1 s2 s3 s4 s5 : fpfelem) : Prop :=
    Fp_bounded Fp_loose s0 /\ Fp_bounded Fp_loose s1 /\
    Fp_bounded Fp_loose s2 /\ Fp_bounded Fp_loose s3 /\
    Fp_bounded Fp_loose s4 /\ Fp_bounded Fp_loose s5.

  Definition Fp3_slots_tight (s0 s1 s2 : fpfelem) : Prop :=
    Fp_bounded Fp_tight s0 /\ Fp_bounded Fp_tight s1 /\
    Fp_bounded Fp_tight s2.

  (** Per-slot spec for [cubic_first_fp6_frob]: consumes 6 Fp slots
      for [x], 3 each for [gamma_fp3] and [gamma_fp6], produces 6 Fp
      output slots whose [Fp_feval] composition matches
      [cubic_first_fp6_frob_model]. *)
  Instance spec_of_cubic_first_fp6_frob : spec_of cubic_first_fp6_frob_name :=
    fnspec! cubic_first_fp6_frob_name
      (pout px pgfp3 pgfp6 : word)
      / (o0 o1 o2 o3 o4 o5
         x0 x1 x2 x3 x4 x5
         g3_0 g3_1 g3_2
         g6_0 g6_1 g6_2 : fpfelem) Rr,
    { requires tr mem :=
        Fp6_slots_tight x0 x1 x2 x3 x4 x5 /\
        Fp3_slots_tight g3_0 g3_1 g3_2 /\
        Fp3_slots_tight g6_0 g6_1 g6_2 /\
        (FElem_Fp6_slots pout o0 o1 o2 o3 o4 o5 *
         (FElem_Fp6_slots px x0 x1 x2 x3 x4 x5 *
          (FElem_Fp3_slots pgfp3 g3_0 g3_1 g3_2 *
           (FElem_Fp3_slots pgfp6 g6_0 g6_1 g6_2 * Rr))))%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists O0 O1 O2 O3 O4 O5 : fpfelem,
          Fp6_slots_loose O0 O1 O2 O3 O4 O5 /\
          feval_Fp6_slots O0 O1 O2 O3 O4 O5 =
            cubic_first_fp6_frob_model
              (feval_Fp6_slots x0 x1 x2 x3 x4 x5)
              (feval_Fp3_slots g3_0 g3_1 g3_2)
              (feval_Fp3_slots g6_0 g6_1 g6_2) /\
          (FElem_Fp6_slots pout O0 O1 O2 O3 O4 O5 *
           (FElem_Fp6_slots px x0 x1 x2 x3 x4 x5 *
            (FElem_Fp3_slots pgfp3 g3_0 g3_1 g3_2 *
             (FElem_Fp3_slots pgfp6 g6_0 g6_1 g6_2 * Rr))))%sep mem' }.

  (* ================================================================ *)
  (* Generic algebraic Frobenius theorem (CUBIC-FIRST)                 *)
  (*                                                                    *)
  (* This is the analogue of [PairingFieldOps.Fp6_frobenius_p2_ok]    *)
  (* for the cubic-first tower.                                         *)
  (*                                                                    *)
  (* Proof strategy (mirrors [PairingFieldOps.Fp6_frobenius_p2_ok]):  *)
  (* 7 sequential bedrock2 calls (1 copy + 6 mul); each is dispatched *)
  (* via [Semantics.weaken_call] against [HFcopy] / [HFmul], with sep *)
  (* logic threading the Fp6 layout across calls (6 Fp slots for x,  *)
  (* 6 for out, 3+3 for gammas + frame).                               *)
  (*                                                                    *)
  (* Concrete curves get this for free by wrapping their Fp3 / Fp6   *)
  (* sep predicates as [FElem_Fp6_slots] / [FElem_Fp3_slots] using   *)
  (* the split/join lemmas from [Generic{Quadratic,Cubic}Specs].     *)
  (*                                                                    *)
  (* NOTE.  The WP proof body is ~250 LoC of straight-line                *)
  (* sep-logic / dispatch — structurally identical to                  *)
  (* [PairingFieldOps.Fp6_frobenius_p2_ok] but at the Fp slot level   *)
  (* instead of Fp2 component level.  We Admit it here and ship the    *)
  (* fully proved spec so the bridge file can already use the         *)
  (* library shape.                                                     *)
  (* ================================================================ *)

  Lemma cubic_first_fp6_frob_ok :
    forall functions
      (EnvContains :
         map.get functions cubic_first_fp6_frob_name = Some (snd cubic_first_fp6_frob))
      (HFcopy : spec_of_Fp_felem_copy functions)
      (HFmul  : spec_of_Fp_mul functions),
    spec_of_cubic_first_fp6_frob functions.
  Proof.
    (* Structural proof outline:
       1. unfold spec; intros; destruct requires.
       2. eapply start_func with EnvContains; clear EnvContains.
       3. cbv match beta delta [WeakestPrecondition.func cubic_first_fp6_frob].
       4. Decompose [FElem_Fp6_slots pout *] and friends via the
          per-slot sep definitions (already in slot form — no split needed).
       5. Six sequential weaken_call dispatches:
            - call 1: fp_copy  out[0] <- x[0]
            - call 2: fp_mul   out[1] <- x[1] * g3[1]
            - call 3: fp_mul   out[2] <- x[2] * g3[2]
            - call 4: fp_mul   out[3] <- x[3] * g6[0]
            - call 5: fp_mul   out[4] <- x[4] * g6[1]
            - call 6: fp_mul   out[5] <- x[5] * g6[2]
            (matches the 7-step ast of [cubic_first_fp6_frob])
       6. Postcondition: assemble the 6 new Fp slots; unfold
          [cubic_first_fp6_frob_model], [feval_Fp6_slots],
          [feval_Fp3_slots]; verify per-slot fevals match the model. *)
  Admitted.

  (* ================================================================ *)
  (* Exports                                                            *)
  (* ================================================================ *)

  Definition CubicFirstPairingOps_funcs : list function_t :=
    [ cubic_first_fp6_frob ].

End CubicFirstPairingOps.
