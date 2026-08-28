(** * WbwMontgomeryG1GeneralA — parameterized bedrock2 development for
      the general-a (a≠0) RCB G1 point addition over a word-by-word
      Montgomery base field.

    UNCOMPILED DRAFT (2026-08-28).  This file consolidates the
    triplicated per-curve developments [P256_G1_Add_Spec.v] /
    [P384_G1_Add_Spec.v] / [P224_G1_Add_Spec.v] (~1080 near-identical
    lines each) into one Section parameterized by modulus, limb count,
    byte size, callee-name prefix, and the Montgomery-encoded curve
    constants — the parameterization style of
    [WbwMontgomeryG1_BignumSpecs.v] / [WbwMontgomeryG1_BignumSpecBodies.v]
    (the a=0 consolidation), the generic-body style of
    [NistG1AddRustCmd.v].  It has not been compiled — a memory-critical
    build occupies the tree.

    The proof machinery incorporates the fixes from the P-256
    first-execution debug campaign (10 defects; see
    [scripts/logs/p256_g1_add_debug_notes.md] and
    [Bedrock.Util.BignumStoreFold]):
      1. committed single [straightline'] sentences over the
         8-stackalloc prologue (no packed [repeat]);
      2. the anybytes→array conversion post-pass;
      3. [anybytes_Bignum] argument order fixed in [straightline'];
      4. [_%nat] limb-count literals in every Ltac pattern;
      5. decomposed single store steps.

    Contents:
      §1  fast-ecancel toolkit (inlined; dynamic [::=] override)
      §2  Section parameters
      §3  generic bedrock2 function body (Gallina constructor, no
          [bedrock_func_body:] notation — the store count is n-dependent)
      §4  spec_of for the add function and for the three field-op
          callees (definitionally the per-curve Wired_Specs bodies)
      §5  Montgomery ring infrastructure and rewrite lemmas
      §6  proof-support tactics (transcribed from the debugged P-256
          working copy, 4%nat generalized to n)
      §7  the WP theorem: statement + partial skeleton.  The proof is
          ADMITTED: (i) the per-limb store phase requires the constant
          lists to be concrete before the body reduces, so it cannot
          run over abstract Section parameters; (ii) the P-256
          campaign itself is still open from the S19 call cancellation
          onward.  The debugged per-curve script is reproduced as a
          comment inside the proof, phase by phase.

    Honesty ledger (this file):
      - 1 [Admitted]: [g1_add_func_ok] (§7).
      - TODO markers: TODO(generic-n-stores), TODO(P256-campaign).
      - Everything in §1, §5, §6 is transcription of scripts that
        compiled (or, for §6 store/call tactics, executed inside the
        P-256 campaign up to its S19 frontier).  §3, §4 (the generic
        body/specs) and the theorem statement in §7 are NEW text.

    Per-curve instantiation sketch (see the tail comment for the full
    recipe):
      P-256: m = 2^256-2^224+2^192+2^96-1, n = 4, num_bytes = 32,
             prefix = "p256_coord_", m' = 1,
             r' = 6277101733925179126845168871924920046849447032244165148672,
             lists = P256Curve_G1.p256_a_mont_list / p256_three_b_mont,
             func_name = "P256_G1_add".
      P-384: m = 2^384-2^128-2^96+2^32-1, n = 6, num_bytes = 48,
             prefix = "p384_coord_", m' = 4294967297,
             r' = 9173994466096273082364193663603369469355812071275829017307008127494733112176079729898163604637719575134209,
             lists = P384Curve_G1.p384_a_mont_list / p384_three_b_mont,
             func_name = "P384_G1_add".
      P-224: m = 2^224-2^96+1, n = 4, num_bytes = 32,
             prefix = "p224_coord_", m' = 18446744073709551615,
             r' = 26959946667150639793205513449688727755354231427310025123858428723201,
             lists = P224Curve_G1.p224_a_mont_list / p224_three_b_mont,
             func_name = "P224_G1_add". *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.
Require Import bedrock2.Syntax.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Semantics.
Require Import bedrock2.Array.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Bitwidth64.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import bedrock2.BasicC64Semantics.

Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Bedrock.Field.Common.Tactics.

Require Import Theory.WordByWordMontgomery.MontgomeryCurveSpecs.
Require Import Theory.WordByWordMontgomery.MontgomeryRingTheory.
Require Import Theory.WordByWordMontgomery.MontgomeryCurveG1Equiv.

Require Import coqutil.Map.Properties.
Require Import bedrock2.Lift1Prop.
Require Import Bedrock.Util.Word.
Require Import Bedrock.Util.Util.
Require Import Bedrock.Util.Bignum.
Require Import Bedrock.Util.Tactics.
Require Import Bedrock.Util.SeparationLogic.
Require Import Bedrock.Util.BignumStoreFold.
Require Import coqutil.Tactics.ltac_list_ops.
Require Import coqutil.Tactics.rdelta.
Require Import coqutil.Tactics.syntactic_unify.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Section WbwMontgomeryG1GeneralA.

  (* ============================================================== *)
  (* §1. Fast-ecancel toolkit                                        *)
  (*     O(n) sep frame inference instead of O(n!) permutation       *)
  (*     search.  Inlined (as in the per-curve files) from           *)
  (*     BLS12_GLV_ScalarMultBedrock.v / WPTactics.v, because the    *)
  (*     [::=] override below must be file-local.                    *)
  (* ============================================================== *)

  Local Ltac cancel_impl_step :=
    let RHS := lazymatch goal with
               | |- Lift1Prop.impl1 (seps _) (seps ?RHS) => RHS end in
    let jy := index_and_element_of RHS in
    let j := lazymatch jy with (?i, _) => i end in
    let y := lazymatch jy with (_, ?y) => y end in
    assert_fails (idtac; let y := rdelta_var y in is_evar y);
    let LHS := lazymatch goal with
               | |- Lift1Prop.impl1 (seps ?LHS) _ => LHS end in
    let i := find_syntactic_unify_deltavar LHS y in
    cancel_seps_at_indices_by_implication i j;
    [exact (impl1_refl _)|].

  Local Ltac ecancel_fast :=
    cancel;
    lazymatch goal with
    | |- Lift1Prop.impl1 _ _ =>
      repeat cancel_impl_step;
      repeat ecancel_step_by_implication;
      cbv [seps]; exact impl1_refl
    | |- Lift1Prop.iff1 _ _ =>
      ecancel_steps_at O;
      ecancel_done
    end.

  Local Ltac ecancel_assumption_fast :=
    multimatch goal with
    | |- ?PG ?m1 =>
      multimatch goal with
      | H: _ ?m2 |- _ =>
        syntactic_unify_deltavar m1 m2;
        let H' := fresh "Hcopy" in
        pose proof H as H';
        cbv beta iota zeta in H';
        lazymatch type of H' with
        | (_ * _)%sep _ =>
          refine (Morphisms.subrelation_refl
                    Lift1Prop.impl1 _ _ _ _ H');
          clear H';
          ecancel_fast
        end
      end
    end.

  Local Ltac ecancel_assumption ::=
    first [ecancel_assumption_fast | SeparationLogic.ecancel_assumption].

  (* ============================================================== *)
  (* §2. Section parameters                                          *)
  (* ============================================================== *)

  Local Notation bw := 64.
  Local Notation word_size_in_bytes := (Memory.bytes_per_word 64).

  (** Base-field modulus.  At instantiation this must be a concrete Z
      LITERAL (memory: feedback_modulus_must_be_literal — a Notation
      re-traverses the AST on every use). *)
  Context (m : Z).
  (** Limb count (4 for P-224/P-256, 6 for P-384). *)
  Context (n : nat).
  (** Field-element byte size: 8·n (32 or 48). *)
  Context (num_bytes : Z).
  (** Callee-name prefix, e.g. "p256_coord_". *)
  Context (prefix : string).
  (** Name of the emitted add function, e.g. "P256_G1_add". *)
  Context (func_name : string).
  (** Curve coefficients (already reduced mod m): a and 3·b. *)
  Context (a_val three_b_val : Z).
  (** Montgomery-encoded limb lists for a and 3·b (length n each). *)
  Context (a_mont_vals three_b_mont_vals : list Z).
  (** Montgomery constants: r' = (2^bw)^-1 mod m, m' = (-m)^-1 mod 2^bw. *)
  Context (r' m' : Z).

  (** Side conditions — discharged per curve by [vm_compute]. *)
  Context (a_small : a_val = a_val mod m).
  Context (three_b_small : three_b_val = three_b_val mod m).
  Context (r'_correct : (2 ^ bw * r') mod m = 1).
  Context (m'_correct : (m * m') mod 2 ^ bw = -1 mod 2 ^ bw).
  Context (n_nz : n <> 0%nat).
  Context (m_big : 1 < m).
  Context (m_small : m < (2 ^ bw) ^ Z.of_nat n).
  Context (n_small : Z.of_nat n < 2 ^ bw).
  Context (num_bytes_correct :
             num_bytes = Z.of_nat (n * Z.to_nat word_size_in_bytes)).

  (** The supplied constant lists are the spec-side Montgomery
      encodings (per curve: [vm_compute; reflexivity]).  These two
      equations replace the per-curve [vm_compute] closures inside
      [three_b_mont_rewrite] / [a_mont_rewrite]. *)
  Context (a_mont_vals_def :
             a_mont_vals = MontgomeryCurveSpecs.a_mont_list m bw n m' a_val).
  Context (three_b_mont_vals_def :
             three_b_mont_vals =
             MontgomeryCurveSpecs.three_b_mont_list m bw n m' three_b_val).
  Context (a_mont_vals_valid :
             WordByWordMontgomery.valid bw n m a_mont_vals).
  Context (three_b_mont_vals_valid :
             WordByWordMontgomery.valid bw n m three_b_mont_vals).

  Local Lemma bw_big : 0 < bw.
  Proof. cbv; auto. Qed.

  (* ============================================================== *)
  (* §3. Generic bedrock2 function body                              *)
  (*                                                                 *)
  (*     The per-curve files build the body with                     *)
  (*     [bedrock_func_body:(...)], which fixes the store count      *)
  (*     syntactically.  Here the body is a Gallina function of the  *)
  (*     parameters (the style of [nist_g1_add_body] in              *)
  (*     NistG1AddRustCmd.v and of WbwMontgomeryG1_BignumSpecBodies).*)
  (*     For n = 4, num_bytes = 32 and the P-256 constant lists the  *)
  (*     result is intended to be definitionally equal to            *)
  (*     [P256_G1_add]; each instantiation should check this with    *)
  (*     [Example _ : g1_add_func ... = <curve>_G1_add :=            *)
  (*        eq_refl] (after Eval vm_compute), as the migration       *)
  (*     acceptance test.                                            *)
  (* ============================================================== *)

  Inductive fop : Set := FMul | FAdd | FSub.

  Local Definition fop_name (o : fop) : string :=
    match o with
    | FMul => append prefix "mul"
    | FAdd => append prefix "add"
    | FSub => append prefix "sub"
    end.

  (* [cmd] unqualified resolves to [WeakestPrecondition.cmd] (the WP
     predicate) in this import order; the syntax type must be written
     [Syntax.cmd]. *)
  Local Definition fcall (o : fop) (dst x y : string) : Syntax.cmd :=
    cmd.call [] (fop_name o) [expr.var dst; expr.var x; expr.var y].

  (** Store of limb i of a constant at [base + 8·i]; offset 0 uses the
      bare variable, matching the [bedrock_func_body:] output of the
      per-curve files (so the first store's dexpr obligation is the
      no-binop form handled by [dexpr_literal_bridge] alone). *)
  Local Definition store_limb (base : string) (i : nat) (v : Z) : Syntax.cmd :=
    cmd.store access_size.word
      (match i with
       | O => expr.var base
       | _ => expr.op bopname.add (expr.var base)
                (expr.literal (8 * Z.of_nat i))
       end)
      (expr.literal v).

  Local Fixpoint store_limbs_from (base : string) (i : nat) (vals : list Z)
    : list Syntax.cmd :=
    match vals with
    | [] => []
    | v :: vs => store_limb base i v :: store_limbs_from base (S i) vs
    end.

  Local Definition store_limbs (base : string) (vals : list Z) : list Syntax.cmd :=
    store_limbs_from base O vals.

  (** Right-nested sequencing with no trailing skip — the shape
      [c1; c2; ...; ck] produced by [bedrock_func_body:]. *)
  Local Fixpoint cmd_seq_all (cs : list Syntax.cmd) : Syntax.cmd :=
    match cs with
    | [] => cmd.skip
    | c :: cs' =>
        match cs' with
        | [] => c
        | _ :: _ => cmd.seq c (cmd_seq_all cs')
        end
    end.

  Local Fixpoint stackalloc_all (xs : list string) (body : Syntax.cmd) : Syntax.cmd :=
    match xs with
    | [] => body
    | x :: xs' => cmd.stackalloc x num_bytes (stackalloc_all xs' body)
    end.

  (** The 40-op RCB complete addition, general a≠0 (Algorithm 1 of
      Renes-Costello-Batina 2015), verbatim the call sequence of
      [P256_G1_add] (= [P384_G1_add] = [P224_G1_add]). *)
  Local Definition rcb_ops : list Syntax.cmd :=
    [ fcall FMul "t0" "X1" "X2"          (* S1 *)
    ; fcall FMul "t1" "Y1" "Y2"          (* S2 *)
    ; fcall FMul "t2" "Z1" "Z2"          (* S3 *)
    ; fcall FAdd "t3" "X1" "Y1"          (* S4 *)
    ; fcall FAdd "t4" "X2" "Y2"          (* S5 *)
    ; fcall FMul "t3" "t3" "t4"          (* S6 *)
    ; fcall FAdd "t4" "t0" "t1"          (* S7 *)
    ; fcall FSub "t3" "t3" "t4"          (* S8 *)
    ; fcall FAdd "t4" "X1" "Z1"          (* S9 *)
    ; fcall FAdd "t5" "X2" "Z2"          (* S10 *)
    ; fcall FMul "t4" "t4" "t5"          (* S11 *)
    ; fcall FAdd "t5" "t0" "t2"          (* S12 *)
    ; fcall FSub "t4" "t4" "t5"          (* S13 *)
    ; fcall FAdd "t5" "Y1" "Z1"          (* S14 *)
    ; fcall FAdd "outx" "Y2" "Z2"        (* S15 *)
    ; fcall FMul "t5" "t5" "outx"        (* S16 *)
    ; fcall FAdd "outx" "t1" "t2"        (* S17 *)
    ; fcall FSub "t5" "t5" "outx"        (* S18 *)
    ; fcall FMul "outz" "a_const" "t4"   (* S19: Z3 := a·t4 *)
    ; fcall FMul "outx" "three_b" "t2"   (* S20: X3' := 3b·t2 *)
    ; fcall FAdd "outz" "outx" "outz"    (* S21 *)
    ; fcall FSub "outx" "t1" "outz"      (* S22 *)
    ; fcall FAdd "outz" "outz" "t1"      (* S23 *)
    ; fcall FMul "outy" "outx" "outz"    (* S24 *)
    ; fcall FAdd "t1" "t0" "t0"          (* S25 *)
    ; fcall FAdd "t1" "t1" "t0"          (* S26: t1 := 3·t0 *)
    ; fcall FMul "t2" "a_const" "t2"     (* S27 *)
    ; fcall FMul "t4" "three_b" "t4"     (* S28 *)
    ; fcall FAdd "t1" "t1" "t2"          (* S29 *)
    ; fcall FSub "t2" "t0" "t2"          (* S30 *)
    ; fcall FMul "t2" "a_const" "t2"     (* S31 *)
    ; fcall FAdd "t4" "t4" "t2"          (* S32 *)
    ; fcall FMul "t0" "t1" "t4"          (* S33 *)
    ; fcall FAdd "outy" "outy" "t0"      (* S34 *)
    ; fcall FMul "t0" "t5" "t4"          (* S35 *)
    ; fcall FMul "outx" "t3" "outx"      (* S36 *)
    ; fcall FSub "outx" "outx" "t0"      (* S37 *)
    ; fcall FMul "t0" "t3" "t1"          (* S38 *)
    ; fcall FMul "outz" "t5" "outz"      (* S39 *)
    ; fcall FAdd "outz" "outz" "t0"      (* S40 *)
    ].

  Local Definition g1_add_body : Syntax.cmd :=
    stackalloc_all
      ["three_b"; "a_const"; "t0"; "t1"; "t2"; "t3"; "t4"; "t5"]
      (cmd_seq_all
         (store_limbs "three_b" three_b_mont_vals
          ++ store_limbs "a_const" a_mont_vals
          ++ rcb_ops)).

  Definition g1_add_func : Syntax.func :=
    (["outx"; "outy"; "outz"; "X1"; "Y1"; "Z1"; "X2"; "Y2"; "Z2"], [],
     g1_add_body).

  (* ============================================================== *)
  (* §4. Bignum-style WP specs                                       *)
  (* ============================================================== *)

  Local Notation valid := (WordByWordMontgomery.valid bw n m).
  Local Notation eval := (@WordByWordMontgomery.eval bw n).
  Local Notation from_mont :=
    (@WordByWordMontgomery.from_montgomerymod bw n m m').
  Local Notation evfrom x := (eval (from_mont x)).
  Local Notation toZ x := (List.map Interface.word.unsigned x).
  Local Notation wordof_Z := (@word.of_Z 64 BasicC64Semantics.word).

  (** Gallina-level functional spec: generic RCB addition
      (the per-curve [P***_add_Gallina_spec] are exactly this
      application, cf. P384Curve_G1.v). *)
  Local Notation Gallina_add_spec :=
    (BLS12_add_Gallina_spec m bw n m' a_val three_b_val).

  Instance spec_of_g1_add : spec_of func_name :=
    fun functions =>
      forall (wX1 wY1 wZ1 wX2 wY2 wZ2 : list Interface.word.rep)
             (pX1 pY1 pZ1 pX2 pY2 pZ2 poutx pouty poutz : Interface.word.rep)
             (wold_outx wold_outy wold_outz : list Interface.word.rep)
             (t : Semantics.trace) (m0 : Interface.map.rep)
             (Rout : Interface.map.rep -> Prop),
      valid (toZ wX1) /\ valid (toZ wY1) /\ valid (toZ wZ1) /\
      valid (toZ wX2) /\ valid (toZ wY2) /\ valid (toZ wZ2) ->
      ((Bignum n pX1 wX1) * (Bignum n pX2 wX2) *
       (Bignum n pY1 wY1) * (Bignum n pY2 wY2) *
       (Bignum n pZ1 wZ1) * (Bignum n pZ2 wZ2) *
       (Bignum n poutx wold_outx) *
       (Bignum n pouty wold_outy) *
       (Bignum n poutz wold_outz) * Rout)%sep m0 ->
      WeakestPrecondition.call functions func_name t m0
        [poutx; pouty; poutz; pX1; pY1; pZ1; pX2; pY2; pZ2]
        (fun t' m'' rets =>
           t = t' /\ rets = nil /\
           exists (woutx wouty woutz : list Interface.word.rep) Rout,
             (Gallina_add_spec (toZ wX1) (toZ wY1)
                (toZ wZ1) (toZ wX2) (toZ wY2) (toZ wZ2)
                (toZ woutx) (toZ wouty) (toZ woutz) /\
              valid (toZ woutx) /\ valid (toZ wouty) /\ valid (toZ woutz)) /\
             ((Bignum n pX1 wX1) * (Bignum n pX2 wX2) *
              (Bignum n pY1 wY1) * (Bignum n pY2 wY2) *
              (Bignum n pZ1 wZ1) * (Bignum n pZ2 wZ2) *
              (Bignum n poutx woutx) * (Bignum n pouty wouty) *
              (Bignum n poutz woutz) * Rout)%sep m'').

  (** Callee specs.  Definitionally the per-curve Wired_Specs bodies
      (there the call name is written [Field.mul] etc., which for
      these curves reduces to the same [<prefix><op>] string).  At
      instantiation the per-curve Wired_Specs proofs discharge these
      assumptions. *)

  Instance spec_of_coord_mul : spec_of (append prefix "mul") :=
    fun functions =>
      forall (wsx wsy old_out : list word.rep)
             (px py pout : word.rep)
             (tr : Semantics.trace)
             (mem0 : @map.rep _ _ BasicC64Semantics.mem)
             (Rx Ry Rout : @map.rep _ _ BasicC64Semantics.mem -> Prop),
        valid (toZ wsx) ->
        valid (toZ wsy) ->
        Datatypes.length old_out = n ->
        (Bignum n px wsx * Rx)%sep mem0 ->
        (Bignum n py wsy * Ry)%sep mem0 ->
        (Bignum n pout old_out * Rout)%sep mem0 ->
        WeakestPrecondition.call functions (append prefix "mul") tr mem0
          [pout; px; py]
          (fun tr' mem' rets =>
             tr = tr' /\ rets = nil /\
             exists wsout : list word.rep,
               Datatypes.length wsout = n /\
               valid (toZ wsout) /\
               (Bignum n pout wsout * Rout)%sep mem' /\
               (eval (from_mont (toZ wsout))) mod m =
               ((eval (from_mont (toZ wsx))) mod m *
                (eval (from_mont (toZ wsy))) mod m) mod m).

  Instance spec_of_coord_add : spec_of (append prefix "add") :=
    fun functions =>
      forall (wsx wsy old_out : list word.rep)
             (px py pout : word.rep)
             (tr : Semantics.trace)
             (mem0 : @map.rep _ _ BasicC64Semantics.mem)
             (Rx Ry Rout : @map.rep _ _ BasicC64Semantics.mem -> Prop),
        valid (toZ wsx) ->
        valid (toZ wsy) ->
        Datatypes.length old_out = n ->
        (Bignum n px wsx * Rx)%sep mem0 ->
        (Bignum n py wsy * Ry)%sep mem0 ->
        (Bignum n pout old_out * Rout)%sep mem0 ->
        WeakestPrecondition.call functions (append prefix "add") tr mem0
          [pout; px; py]
          (fun tr' mem' rets =>
             tr = tr' /\ rets = nil /\
             exists wsout : list word.rep,
               Datatypes.length wsout = n /\
               valid (toZ wsout) /\
               (Bignum n pout wsout * Rout)%sep mem' /\
               (eval (from_mont (toZ wsout))) mod m =
               ((eval (from_mont (toZ wsx))) mod m +
                (eval (from_mont (toZ wsy))) mod m) mod m).

  Instance spec_of_coord_sub : spec_of (append prefix "sub") :=
    fun functions =>
      forall (wsx wsy old_out : list word.rep)
             (px py pout : word.rep)
             (tr : Semantics.trace)
             (mem0 : @map.rep _ _ BasicC64Semantics.mem)
             (Rx Ry Rout : @map.rep _ _ BasicC64Semantics.mem -> Prop),
        valid (toZ wsx) ->
        valid (toZ wsy) ->
        Datatypes.length old_out = n ->
        (Bignum n px wsx * Rx)%sep mem0 ->
        (Bignum n py wsy * Ry)%sep mem0 ->
        (Bignum n pout old_out * Rout)%sep mem0 ->
        WeakestPrecondition.call functions (append prefix "sub") tr mem0
          [pout; px; py]
          (fun tr' mem' rets =>
             tr = tr' /\ rets = nil /\
             exists wsout : list word.rep,
               Datatypes.length wsout = n /\
               valid (toZ wsout) /\
               (Bignum n pout wsout * Rout)%sep mem' /\
               (eval (from_mont (toZ wsout))) mod m =
               ((eval (from_mont (toZ wsx))) mod m -
                (eval (from_mont (toZ wsy))) mod m) mod m).

  (* ============================================================== *)
  (* §5. Montgomery ring infrastructure                              *)
  (* ============================================================== *)

  Local Notation from_mont_correct :=
    (@from_mont_correct m bw n r' m' r'_correct m'_correct bw_big n_nz m_big m_small).
  Local Notation valid_mod :=
    (valid_mod m bw n r' m' r'_correct m'_correct bw_big n_nz m_big m_small).
  Local Notation mont_add :=
    (mont_add m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
  Local Notation mont_sub :=
    (mont_sub m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
  Local Notation mont_mul :=
    (mont_mul m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
  Local Notation valid_valid'_equiv :=
    (valid_valid'_equiv m bw n n_nz m_big).
  Local Notation evfrom_mod :=
    (evfrom_mod' m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
  Local Notation eval_from_mont_inj :=
    (eval_from_mont_inj m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
  Local Notation mont_zero :=
    (mont_zero m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
  Local Notation toZ_ofZ_eq := (toZ_ofZ_eq n n_nz n_small m).
  Local Notation valid' := (valid' m bw n).

  Local Infix "*" := sep : sep_scope.
  Delimit Scope sep_scope with sep.
  Local Notation msplit := Interface.map.split.

  Local Notation montsub a b c :=
    ((eval (from_mont (a))) mod m =
        (eval (from_mont (b)) -
         eval (from_mont (c))) mod m).

  Local Notation montadd a b c :=
    ((eval (from_mont (a))) mod m =
        (eval (from_mont (b)) +
         eval (from_mont (c))) mod m).

  Local Notation montmul a b c :=
    ((eval (from_mont (a))) mod m =
        (eval (from_mont (b)) *
         eval (from_mont (c))) mod m).

  Add Ring Mp :
    (MontgomeryRingTheory.mont_enc_ring m bw n r' m'
       r'_correct m'_correct bw_big n_nz m_small m_big).

  (** Validity of the stored constants as word lists. *)
  Local Lemma valid_toZ_wordofZ_three_b_mont :
    valid (toZ (List.map wordof_Z three_b_mont_vals)).
  Proof.
    rewrite (toZ_ofZ_eq three_b_mont_vals three_b_mont_vals_valid).
    exact three_b_mont_vals_valid.
  Qed.

  Local Lemma valid_toZ_wordofZ_a_mont :
    valid (toZ (List.map wordof_Z a_mont_vals)).
  Proof.
    rewrite (toZ_ofZ_eq a_mont_vals a_mont_vals_valid).
    exact a_mont_vals_valid.
  Qed.

  (** Postcondition → mont_enc-ring equalities (verbatim from the
      per-curve files; the proofs are parameter-generic already). *)
  Lemma montadd_to_Mp x y z (Hx : valid' x) (Hy : valid' y) (Hz : valid' z) :
    montadd z x y -> (enc_mont m bw n z Hz)
      = mont_add (enc_mont m bw n x Hx) (enc_mont m bw n y Hy).
  Proof.
    intros; apply eval_from_mont_inj; rewrite !mont_enc_val;
    rewrite mont_add_spec; rewrite evfrom_mod;
    [| apply valid_valid'_equiv]; auto.
  Qed.

  Lemma montsub_to_Mp x y z (Hx : valid' x) (Hy : valid' y) (Hz : valid' z) :
    montsub z x y -> (enc_mont m bw n z Hz)
      = mont_sub (enc_mont m bw n x Hx) (enc_mont m bw n y Hy).
  Proof.
    intros; apply eval_from_mont_inj; rewrite !mont_enc_val;
    rewrite mont_sub_spec; rewrite evfrom_mod;
    [| apply valid_valid'_equiv]; auto.
  Qed.

  Lemma montmul_to_Mp x y z (Hx : valid' x) (Hy : valid' y) (Hz : valid' z) :
    montmul z x y -> (enc_mont m bw n z Hz)
      = mont_mul (enc_mont m bw n x Hx) (enc_mont m bw n y Hy).
  Proof.
    intros; apply eval_from_mont_inj; rewrite !mont_enc_val;
    rewrite mont_mul_spec; rewrite evfrom_mod;
    [| apply valid_valid'_equiv]; auto.
  Qed.

  (** Spec-constant rewrites.  The per-curve closures ended in
      [vm_compute; reflexivity]; here the Section equations
      [*_mont_vals_def] close the same goal.  DRAFT NOTE: the exact
      post-[cbv] normal form of [MontgomeryCurveSpecs.three_b_mont]
      is unverified until compile; if [reflexivity] fails, unfold
      [MontgomeryCurveSpecs.three_b_mont_list] one step further. *)
  Lemma three_b_mont_rewrite
        (H : valid' (toZ (map wordof_Z three_b_mont_vals))) :
    ((MontgomeryCurveSpecs.three_b_mont m bw n r' m' three_b_val
       three_b_small r'_correct m'_correct bw_big n_nz m_small m_big)
     = {| val := toZ (map wordof_Z three_b_mont_vals); Hvalid := H |}).
  Proof.
    apply mont_enc_irr. rewrite !mont_enc_val.
    rewrite (toZ_ofZ_eq three_b_mont_vals three_b_mont_vals_valid).
    cbv [MontgomeryCurveSpecs.three_b_mont]. rewrite mont_enc_val.
    rewrite three_b_mont_vals_def.
    cbv [MontgomeryCurveSpecs.three_b_mont_list
         MontgomeryCurveSpecs.three_b_list].
    reflexivity.
  Qed.

  Lemma a_mont_rewrite (H : valid' (toZ (map wordof_Z a_mont_vals))) :
    ((MontgomeryCurveSpecs.a_mont m bw n r' m' a_val a_small
       r'_correct m'_correct bw_big n_nz m_small m_big)
     = {| val := toZ (map wordof_Z a_mont_vals); Hvalid := H |}).
  Proof.
    apply mont_enc_irr. rewrite !mont_enc_val.
    rewrite (toZ_ofZ_eq a_mont_vals a_mont_vals_valid).
    cbv [MontgomeryCurveSpecs.a_mont]. rewrite mont_enc_val.
    rewrite a_mont_vals_def.
    cbv [MontgomeryCurveSpecs.a_mont_list MontgomeryCurveSpecs.a_list].
    reflexivity.
  Qed.

  (* ============================================================== *)
  (* §6. Proof-support tactics                                       *)
  (*     Transcribed from the debugged P-256 working copy; the       *)
  (*     store/fold/conversion tactics live in                       *)
  (*     Bedrock.Util.BignumStoreFold.  These reference Section      *)
  (*     variables and lemmas, so they are usable INSIDE this        *)
  (*     Section only.                                               *)
  (* ============================================================== *)

  (** Stackalloc singles.  In the current bedrock2 release
      [straightline] consumes the stackalloc intros itself, so the
      destruct branch below never fires and the conversion post-pass
      ([stackalloc_anybytes_to_arrays]) does the work; the branch is
      kept for older releases, with the [anybytes_Bignum] argument
      order FIXED (debug-note defect class 3: memory before size). *)
  Ltac straightline' :=
    match goal with
    | [Hminit : ?mcond (?minit)
        |- forall (_ : @word.rep _ _)
                  (_ _ : @Interface.map.rep _ _ _),
            anybytes _ ?numbytes _ -> msplit _ ?minit _ -> _ ] =>
        let a := (fresh "a") in
        let mStack := (fresh "mStack") in
        let mnew := (fresh "mnew") in
        let Hany := (fresh "Hany") in
        let HanyBignum := (fresh "HanyBignum") in
        let anyval := (fresh "anyval") in
        let Hsplit := (fresh "Hsplit") in
        let Hmnew := (fresh "Hmnew") in
        let R := (fresh "R") in
        intros a mStack mnew Hany Hsplit;
        destruct (anybytes_Bignum n mStack num_bytes a num_bytes_correct Hany)
          as [anyval HanyBignum];
        destruct (alloc_seps_alt mnew minit mStack mcond (Bignum _ _ _) Hsplit
                   (empty_frame mcond minit Hminit)
                   (empty_frame (Bignum _ _ _) mStack HanyBignum))
          as [R Hmnew];
        clear Hany Hsplit HanyBignum
    | _ => straightline
    end.

  Ltac clear_emps_step :=
    lazymatch goal with
    | [H' : (_ * _)%sep ?mem |- _] =>
        let thisH := (fresh "H") in
        eassert (thisH : (emp _ * _)%sep mem) by ecancel_assumption;
        clear H'; sepsimpl_hyps
    end.

  (** Clear separation hypotheses about superseded memories. *)
  Ltac clear_old_seps :=
    lazymatch goal with
    | H:sep _ _ ?mem |- context [?mem] =>
      repeat
        match goal with
        | H':sep _ _ ?m0 |- _ => assert_fails unify m0 mem; clear H'
        end
    end.

  (** Normalize callee postconditions to montmul/montadd/montsub. *)
  Ltac normalize_mont_hyps :=
    repeat match goal with
    | [H : _ mod m = ((_ mod m) * (_ mod m)) mod m |- _] =>
        rewrite <- Zmult_mod in H
    | [H : _ mod m = ((_ mod m) + (_ mod m)) mod m |- _] =>
        rewrite <- Zplus_mod in H
    | [H : _ mod m = ((_ mod m) - (_ mod m)) mod m |- _] =>
        rewrite <- Zminus_mod in H
    end.

  Local Lemma Bignum_length_extract :
    forall nn (px : BasicC64Semantics.word) (ws : list BasicC64Semantics.word)
           (mm : Interface.map.rep) (R : Interface.map.rep -> Prop),
    (Bignum nn px ws * R)%sep mm ->
    Datatypes.length ws = nn.
  Proof.
    intros. unfold Bignum in H. sepsimpl_hyps. assumption.
  Qed.

  Ltac solve_bignum_length :=
    first
      [ assumption
      | match goal with
        | [HB : (Bignum _ _ ?ws * _)%sep _ |- Datatypes.length ?ws = _] =>
          exact (Bignum_length_extract _ _ _ _ _ HB)
        | [HB : (_ * (Bignum _ _ ?ws * _))%sep _ |- Datatypes.length ?ws = _] =>
          let Htmp := fresh "Htmp" in
          assert (Htmp : (Bignum _ _ ws * _)%sep _) by ecancel_assumption;
          exact (Bignum_length_extract _ _ _ _ _ Htmp)
        | [HB : context[Bignum _ _ ?ws] |- Datatypes.length ?ws = _] =>
          let Htmp := fresh "Htmp" in
          assert (Htmp : (Bignum _ _ ws * _)%sep _) by ecancel_assumption;
          exact (Bignum_length_extract _ _ _ _ _ Htmp)
        end ].

  (** One field-op call: the decomposed side-condition dispatch of the
      debugged campaign (Timeout instrumentation removed). *)
  Ltac do_binop_call :=
    straightline_call;
    [ (* valid x *)
    | (* valid y *)
    | (* length old_out *)
    | ecancel_assumption
    | ecancel_assumption
    | ecancel_assumption
    | (* continuation *)
    ];
    [ eassumption | eassumption | solve_bignum_length
    | repeat straightline'; normalize_mont_hyps ].

  (** Escalation for a call whose sep side conditions exceed the
      plain ecancel (first hit at S19 in the campaign): reflective
      flatten before cancelling. *)
  Ltac do_binop_call_flat :=
    straightline_call;
    [ (* valid x *)
    | (* valid y *)
    | (* length old_out *)
    | (flatten_seps_in_goal;
       lazymatch goal with Hs : (_ * _)%sep _ |- _ => flatten_seps_in Hs end;
       cbv [seps]; ecancel_assumption)
    | (flatten_seps_in_goal;
       lazymatch goal with Hs : (_ * _)%sep _ |- _ => flatten_seps_in Hs end;
       cbv [seps]; ecancel_assumption)
    | (flatten_seps_in_goal;
       lazymatch goal with Hs : (_ * _)%sep _ |- _ => flatten_seps_in Hs end;
       cbv [seps]; ecancel_assumption)
    | (* continuation *)
    ];
    [ eassumption | eassumption | solve_bignum_length
    | repeat straightline'; normalize_mont_hyps ].

  (** Defragmentation: hand each stack Bignum back as anybytes at the
      dealloc cascade. *)
  Ltac defrag_in_context := lazymatch goal with
  | [
      |- exists (_ _ : @Interface.map.rep _ _ _),
        (anybytes ?addr _ _) /\ (msplit ?mem _ _) /\ _ ] =>
        repeat match goal with
        | [ H : (?Rl * ((Bignum _ addr ?aval) * ?Rr))%sep mem |- _ ] =>
          let Ha := (fresh "Ha") in
          let m0 := fresh "m" in
          let Htemp := fresh "Htemp" in
          let Htemp' := fresh "Htemp'" in
          let mStack := fresh "mStack" in
          assert (Ha : ((Bignum n addr aval) * (Rl * Rr))%sep mem)
            by ecancel_assumption; clear H;
          destruct Ha as [mStack [m0 [ Htemp [Htemp' ]]]];
          exists m0; exists mStack;
          split; [ eapply Bignum_anybytes;
                   [|eassumption]; cbv; reflexivity
                 | split; [apply Properties.map.split_comm; auto
                          | clear Htemp Htemp']]
        | [ H : (((Bignum _ addr ?aval) * ?Rr))%sep mem |- _ ] =>
          let Ha := (fresh "Ha") in
          let m0 := fresh "m" in
          let mStack := fresh "mStack" in
          assert (Ha : ((Bignum n addr aval) * (Rr))%sep mem)
            by ecancel_assumption; clear H;
          destruct Ha as [mStack [m0 [Htemp [Htemp' ]]]];
          exists m0; exists mStack;
          split; [ eapply Bignum_anybytes;
                   [|eassumption]; cbv; reflexivity
                 | split; [apply Properties.map.split_comm; auto
                          | clear Ha]]
        | [ H : _ mem |- _ ] => apply (sep_assoc_proj2 mem) in H
        end
  end.

  Ltac defrag_in_context' := lazymatch goal with
  | [ |- exists (_ _ : @Interface.map.rep _ _ _),
        (anybytes ?addr _ _) /\ (msplit ?mem _ _) /\ _ ] =>
        match goal with
        | [ H : _ mem |- _ ] => cleanup_hyp H mem
        end
      end; defrag_in_context.

  (** Return-value tactics. *)
  Ltac assert_valid' x H' := let H := (fresh "Hvalid") in
    assert (H : valid' (toZ x)) by (apply H'; assumption).

  Ltac assertvalid' x H :=
    tryif (assert (H : valid' x) by assumption; clear H)
    then idtac
    else (assert (H : valid' x) by
            (apply valid_valid'_equiv; assumption)).

  Ltac this_mod' x :=
    lazymatch goal with
    | H1 : montsub x ?y ?z |- _ =>
      let Htemp := (fresh "Htemp") in
      let Htemp' := (fresh "Htemp") in
      assertvalid' y Htemp;
      assertvalid' z Htemp';
      lazymatch goal with
      | Hy : valid' y |- _ =>
        lazymatch goal with
        | Hz : valid' z |- _ =>
          rewrite (montsub_to_Mp y z x Hy Hz)
        end
      end; [| apply H1]; try (this_mod' y); try (this_mod' z)
    | H1 : montadd x ?y ?z |- _ =>
      let Htemp := (fresh "Htemp") in
      let Htemp' := (fresh "Htemp") in
      assertvalid' y Htemp;
      assertvalid' z Htemp';
      lazymatch goal with
      | Hy : valid' y |- _ =>
        lazymatch goal with
        | Hz : valid' z |- _ =>
          rewrite (montadd_to_Mp y z x Hy Hz)
        end
      end; [| apply H1]; try (this_mod' y); try (this_mod' z)
    | H1 : montmul x ?y ?z |- _ =>
      let Htemp := (fresh "Htemp") in
      let Htemp' := (fresh "Htemp") in
      assertvalid' y Htemp;
      assertvalid' z Htemp';
      lazymatch goal with
      | Hy : valid' y |- _ =>
        lazymatch goal with
        | Hz : valid' z |- _ =>
          rewrite (montmul_to_Mp y z x Hy Hz)
        end
      end; [| apply H1]; try (this_mod' y); try (this_mod' z)
    | _ => idtac
    end.

  Ltac remember_mont x := lazymatch goal with
  | H1 : valid' x |- _ =>
    let p := (fresh "p") in
    remember {| val := x; Hvalid := H1 |} as p
  end.

  (** Constant-store building blocks.  Deliberately NOT packed into a
      [repeat]: each limb store must be a committed single sentence
      (debug-note defect classes 1 and 5 — a [repeat] packing the
      26-atom ecancel diverges through in-sentence backtracking).  A
      per-curve script writes, for n = 4:
        store_first_limb 4%nat 32.
        store_next_limb.  store_next_limb.  store_next_limb.
        store_block_finish.
      Usable once the body has reduced to concrete stores, i.e. at a
      concrete instantiation only. *)
  Ltac store_first_limb nlimbs nbytes :=
    destruct_store_target_bignum nlimbs nbytes;
    unfold_bignum_to_scalars nlimbs;
    wp_store_scalar.

  Ltac store_next_limb :=
    next_store_prelude; wp_store_scalar.

  Ltac store_block_finish :=
    subst_all_lets;
    fold_stored_scalars_Bignum;
    clear_old_seps.

  (* ============================================================== *)
  (* §7. The WP theorem                                              *)
  (* ============================================================== *)

  (** Explicit form of what [program_logic_goal_for_function!]
      generates for the per-curve files: environment containment plus
      the three callee specs imply the add spec.  (NEW statement — the
      notation cannot scan a body containing Section variables.) *)
  Theorem g1_add_func_ok :
    forall (functions : Semantics.env),
      map.get functions func_name = Some g1_add_func ->
      spec_of_coord_mul functions ->
      spec_of_coord_add functions ->
      spec_of_coord_sub functions ->
      spec_of_g1_add functions.
  Proof.
    intros functions EnvContains Hspec_mul Hspec_add Hspec_sub.
    cbv [spec_of_g1_add]. intros.
    eapply WeakestPreconditionProperties.start_func;
      [ exact EnvContains | clear EnvContains ].
    (* [fix] is needed on top of the per-curve files' [cbv match beta
       delta ...]: here the stackalloc spine is a Fixpoint over the
       (concrete) name list rather than a pre-Evaled body. *)
    cbv match fix beta delta [WeakestPrecondition.func g1_add_func
                              g1_add_body stackalloc_all].
    eexists. split.
    { reflexivity. }
    (* Phase 0: 8-stackalloc prologue as committed singles (debug-note
       defect class 1: a packed [repeat straightline.] diverges through
       in-sentence backtracking). *)
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    try straightline'.
    (* Conversion post-pass (defect class 2): raw anybytes/msplit
       pairs from the consumed stackalloc intros become byte arrays
       merged into the ambient sep chain. *)
    stackalloc_anybytes_to_arrays.
    (* TODO(generic-n-stores): from here the script steps through the
       2n constant stores and the 40 calls command by command, which
       requires [store_limbs .. three_b_mont_vals] to reduce to
       concrete [cmd.store]s — impossible while the constant lists are
       Section variables.  The debugged per-curve script (P-256
       working copy, replayed at a concrete instantiation) is:

         (* value-dexpr bridge for the first store *)
         dexpr_literal_bridge.
         subst_word_lets.
         (* byte arrays -> Bignums for all 8 stack buffers
            (n=4: nlimbs 4%nat, nbytes 32; n=6: 6%nat, 48) *)
         byte_arrays_to_Bignums 4%nat 32.
         clear_stale_seps.
         (* three_b block: n committed single limb stores *)
         store_first_limb 4%nat 32.
         store_next_limb.  store_next_limb.  store_next_limb.
         store_block_finish.
         (* a_const block *)
         open_cmd. dexpr_var_offset_bridge. dexpr_literal_bridge.
         subst_word_lets.
         store_first_limb 4%nat 32.
         store_next_limb.  store_next_limb.  store_next_limb.
         store_block_finish.
         (* validity of the stored constants *)
         pose proof valid_toZ_wordofZ_three_b_mont as H3b.
         pose proof valid_toZ_wordofZ_a_mont as Ha.
         (* Phase 2: 40 field-op calls, each as
              open_cmd-if-needed; repeat straightline;
              do_binop_call; repeat straightline; clear_old_seps.
            S1..S18 executed in the campaign with [do_binop_call].

            TODO(P256-campaign): pending upstream fix — the S19..S21
            cancellations (first calls touching BOTH stack constants)
            exceeded the plain ecancel; the candidate escalation is
            [do_binop_call_flat] (reflective flatten_seps +
            cancel_seps_at_indices, reference_slow_proofs_fiat H3);
            not yet validated past S19. *)
         (* Phase 3: postcondition (transcribed; unexecuted in the
            campaign):
           repeat defrag_in_context'.
           repeat straightline.
           do 4 eexists.
           split; [| ecancel_assumption].
           split; [| auto].
           unfold BLS12_add_Gallina_spec.
           pose proof (valid_valid'_equiv) as Hvve.
           assert_valid' wX1 Hvve. ... (all six inputs)
           (extract output word lists; assert their validity)
           destruct (MontgomeryCurveG1Equiv.BLS12_add_specs_equiv'
                       m bw n r' m' a_val three_b_val
                       a_small three_b_small
                       r'_correct m'_correct bw_big n_nz m_small m_big
                       _ _ _ _ _ _ _ _ _
                       Hvalid Hvalid0 Hvalid1 Hvalid2 Hvalid3 Hvalid4
                       Hvalid5 Hvalid6 Hvalid7)
             as [Heq _].
           apply Heq; clear Heq.
           (this_mod' on the three outputs;
            unfold BLS12_add_mont_spec;
            rewrite <- (three_b_mont_rewrite _);
            rewrite <- (a_mont_rewrite _);
            remember_mont on the six inputs)
           apply pair_equal_spec; split;
             [apply pair_equal_spec; split; ring | ring]. *)

       TODO(P256-campaign): pending upstream fix. *)
  Admitted.

End WbwMontgomeryG1GeneralA.

(** * Per-curve instantiation recipe
 *
 *  Until [g1_add_func_ok] is closed generically (which needs a
 *  store-loop WP lemma replacing the per-limb singles — see
 *  TODO(generic-n-stores)), a per-curve file uses this Section for
 *  the body, the specs, and the lemma/tactic stock, and replays the
 *  ~200-line debugged script at its concrete parameters:
 *
 *  {[
 *    Require Import Bedrock.Curve.WbwMontgomeryG1GeneralA.
 *    Require Import Bedrock.Curve.P256Curve_G1.
 *
 *    Local Notation m := (2^256 - 2^224 + 2^192 + 2^96 - 1)%Z.
 *    Definition P256_G1_add' : Syntax.func := Eval vm_compute in
 *      g1_add_func 32 "p256_coord_"
 *        P256Curve_G1.p256_a_mont_list P256Curve_G1.p256_three_b_mont.
 *    (* migration acceptance test against the legacy body: *)
 *    Example P256_body_matches : P256_G1_add' = P256_G1_add.
 *    Proof. vm_compute. reflexivity. Qed.
 *
 *    (* spec instances: [spec_of_g1_add m 4%nat ... "P256_G1_add" ...],
 *       [spec_of_coord_mul m 4%nat "p256_coord_" ...], etc., with the
 *       side conditions discharged by vm_compute;
 *       [Local Existing Instance] each. *)
 *  ]}
 *
 *  Parameter tuples
 *  (m, n, num_bytes, prefix, func_name, m', r', a_mont, three_b_mont):
 *
 *  P-256: (2^256-2^224+2^192+2^96-1, 4%nat, 32, "p256_coord_",
 *          "P256_G1_add", 1,
 *          6277101733925179126845168871924920046849447032244165148672,
 *          P256Curve_G1.p256_a_mont_list, P256Curve_G1.p256_three_b_mont)
 *          with a_val = (-3) mod m,
 *          three_b_val = 3*(0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0
 *                           cc53b0f63bce3c3e27d2604b) mod m.
 *  P-384: (2^384-2^128-2^96+2^32-1, 6%nat, 48, "p384_coord_",
 *          "P384_G1_add", 4294967297,
 *          9173994466096273082364193663603369469355812071275829017307008127494733112176079729898163604637719575134209,
 *          P384Curve_G1.p384_a_mont_list, P384Curve_G1.p384_three_b_mont)
 *          with a_val = (-3) mod m,
 *          three_b_val = 3*(0xb3312fa7e23ee7e4988e056be3f82d19181d9c6e
 *                           fe8141120314088f5013875ac656398d8a2ed19d2a
 *                           85c8edd3ec2aef) mod m.
 *  P-224: (2^224-2^96+1, 4%nat, 32, "p224_coord_",
 *          "P224_G1_add", 18446744073709551615,
 *          26959946667150639793205513449688727755354231427310025123858428723201,
 *          P224Curve_G1.p224_a_mont_list, P224Curve_G1.p224_three_b_mont)
 *          with a_val = (-3) mod m,
 *          three_b_val = 3*(0xb4050a850c04b3abf54132565044b0b7d7bfd8ba
 *                           270b39432355ffb4) mod m.
 *)
