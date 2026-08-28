(** * Rupicola derivation of the general-a Renes-Costello-Batina
      complete point addition (40 field operations).

    Written as a text-only structural clone of [CurveAdd.v] (the a=0
    case, 34 ops) during a build-locked session; every place where an
    API detail could not be checked against a compiler was flagged
    with a comment starting (* PORT-CHECK: ... *).  The file compiled
    end-to-end (including the [Derive ... compile] trial) on
    2026-08-28 with no source changes; each PORT-CHECK now carries a
    resolution note.

    Relation to the existing code base:

    - [CurveAdd.v] derives the a=0 RCB addition ([ladderstep_gallina],
      Algorithm 7 of RCB 2015) with one stack-loaded curve constant
      (three_b).  This file derives the general-a addition
      (Algorithm 1 of RCB 2015, 12M + 29add-class ops = 40 field ops)
      with TWO stack-loaded curve constants (a and 3b).

    - The op order and the buffer-reuse discipline are copied
      one-for-one from the Qed-proved hand-written bedrock2 function
      [P256_G1_add] in [src/Bedrock/Curve/P256_G1_Add_Spec.v]
      (steps S1-S40 in its comments), which is also the source of the
      SSA transcription in [src/Bedrock/Curve/NistG1AddRustCmd.v] §1.
      Rupicola maps each [let/n] binder name to the bedrock2 variable
      of the same name, so the Gallina chain below uses exactly the
      variables of [P256_G1_add]: three_b, a_const, t0..t5,
      outx, outy, outz.

    - The intent is to replace the hand-written NIST-curve bodies
      (P-256 / P-384 / P-224) and their hand-written WP proofs by this
      correct-by-construction derivation; see the instantiation plan
      at the end of the file. *)

Require Import Rupicola.Lib.Api. Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Local Open Scope Z_scope.

(* Compatibility shim: opam bedrock2 >=0.0.9 removed the name from func *)
Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.
Local Definition program_logic_goal_for (_ : function_t) (P : Prop) := P.
Local Notation "program_logic_goal_for_function! proc" :=
  (program_logic_goal_for proc True) (at level 10, only parsing).

Section Gallina.

Context {field_parameters : FieldParameters}.
Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
Context {field_representation : FieldRepresentation}.

Local Notation F := (F M_pos).
Local Infix "+F" := (@F.add M_pos) (at level 100).
Local Infix "-F" := (@F.sub M_pos) (at level 100).
Local Infix "*F" := (@F.mul M_pos) (at level 90).

(** The two curve constants: a and 3b of y^2 = x^3 + a x + b. *)
Context {a_val : F} {three_b_val : F}.

  (** General-a RCB complete addition, 40 field operations.

      Step markers S1-S40 reference the step numbering of the bedrock2
      body [P256_G1_add] (P256_G1_Add_Spec.v) and of the SSA list
      [rcb_ops] (NistG1AddRustCmd.v).  Buffer reuse is byte-identical
      to [P256_G1_add]: the destination of each [let/n] is the
      destination buffer of the corresponding [$mul]/[$add]/[$sub].

      [stack] marks the FIRST binding of each stack-allocated
      temporary (three_b, a_const, t0..t5), exactly as in
      [ladderstep_gallina]; outx/outy/outz are the caller-provided
      output buffers, so their first bindings are plain [let/n]. *)
  Definition rcb_add_general_gallina
             (X1 Y1 Z1 X2 Y2 Z2 : F) : \<< F, F, F \>> :=
    let/n three_b := stack three_b_val in
    let/n a_const := stack a_val in
    let/n t0 := stack (X1 *F X2) in       (* S1 *)
    let/n t1 := stack (Y1 *F Y2) in       (* S2 *)
    let/n t2 := stack (Z1 *F Z2) in       (* S3 *)
    let/n t3 := stack (X1 +F Y1) in       (* S4 *)
    let/n t4 := stack (X2 +F Y2) in       (* S5 *)
    let/n t3 := (t3 *F t4) in             (* S6 *)
    let/n t4 := (t0 +F t1) in             (* S7 *)
    let/n t3 := (t3 -F t4) in             (* S8  t3 = (X1+Y1)(X2+Y2)-t0-t1 *)
    let/n t4 := (X1 +F Z1) in             (* S9 *)
    let/n t5 := stack (X2 +F Z2) in       (* S10 *)
    let/n t4 := (t4 *F t5) in             (* S11 *)
    let/n t5 := (t0 +F t2) in             (* S12 *)
    let/n t4 := (t4 -F t5) in             (* S13 t4 = (X1+Z1)(X2+Z2)-t0-t2 *)
    let/n t5 := (Y1 +F Z1) in             (* S14 *)
    let/n outx := (Y2 +F Z2) in           (* S15 *)
    let/n t5 := (t5 *F outx) in           (* S16 *)
    let/n outx := (t1 +F t2) in           (* S17 *)
    let/n t5 := (t5 -F outx) in           (* S18 t5 = (Y1+Z1)(Y2+Z2)-t1-t2 *)
    let/n outz := (a_const *F t4) in      (* S19 outz = a*t4 *)
    let/n outx := (three_b *F t2) in      (* S20 outx = 3b*t2 *)
    let/n outz := (outx +F outz) in       (* S21 outz = 3b*t2 + a*t4 *)
    let/n outx := (t1 -F outz) in         (* S22 *)
    let/n outz := (outz +F t1) in         (* S23 *)
    let/n outy := (outx *F outz) in       (* S24 *)
    let/n t1 := (t0 +F t0) in             (* S25 *)
    let/n t1 := (t1 +F t0) in             (* S26 t1 = 3*t0 *)
    let/n t2 := (a_const *F t2) in        (* S27 t2 = a*t2 *)
    let/n t4 := (three_b *F t4) in        (* S28 t4 = 3b*t4 *)
    let/n t1 := (t1 +F t2) in             (* S29 t1 = 3*t0 + a*t2 *)
    let/n t2 := (t0 -F t2) in             (* S30 t2 = t0 - a*t2 *)
    let/n t2 := (a_const *F t2) in        (* S31 t2 = a*(t0 - a*t2) *)
    let/n t4 := (t4 +F t2) in             (* S32 t4 = 3b*t4 + a*(t0-a*t2) *)
    let/n t0 := (t1 *F t4) in             (* S33 *)
    let/n outy := (outy +F t0) in         (* S34 Y3 *)
    let/n t0 := (t5 *F t4) in             (* S35 *)
    let/n outx := (t3 *F outx) in         (* S36 *)
    let/n outx := (outx -F t0) in         (* S37 X3 *)
    let/n t0 := (t3 *F t1) in             (* S38 *)
    let/n outz := (t5 *F outz) in         (* S39 *)
    let/n outz := (outz +F t0) in         (* S40 Z3 *)
    \<outx, outy, outz\>.

End Gallina.

Section __.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters}
          {field_parameters_ok : FieldParameters_ok}.

  Context {field_representation : FieldRepresentation}
          {field_representation_ok : FieldRepresentation_ok}.

  Local Notation F := (F M_pos).

  #[local] Hint Resolve relax_bounds : compiler.
  Existing Instance felem_alloc.

  Context (Hbounds_eq : loose_bounds = tight_bounds).

  (** The two curve-constant felems and the names of their bedrock2
      loader functions (one loader per constant, cloned from the
      three_b loader of CurveAdd.v). *)
  Context (three_b : felem).
  Context (three_b_name : string).
  Context (Hb_bounds : maybe_bounded (Some loose_bounds) three_b).

  Context (a_const : felem).
  Context (a_name : string).
  Context (Ha_bounds : maybe_bounded (Some loose_bounds) a_const).

  Local Definition three_b_val : F := feval (proj1_sig three_b).
  Local Definition a_val : F := feval (proj1_sig a_const).

  (** Calling convention: outputs first, then P1, then P2 — the ABI of
      the hand-written [P256_G1_add] this derivation is meant to
      replace.
      PORT-CHECK: CurveAdd.v's "curve_add" puts the outputs LAST
      (X1,X2,Y1,Y2,Z1,Z2,Xout,Yout,Zout).  Rupicola's derivation
      machinery treats all pointer arguments uniformly, so argument
      order should be irrelevant; if the [compile] driver turns out to
      be order-sensitive, move the outputs last to match CurveAdd.v
      exactly and adapt the per-curve wrapper instead.
      RESOLVED 2026-08-28: the derivation succeeded with the
      outputs-first ABI; no reordering was needed. *)
  Instance spec_of_rcb_add_general : spec_of "curve_add_general" :=
    fnspec! "curve_add_general"
          (poutx pouty poutz pX1 pY1 pZ1 pX2 pY2 pZ2 : word)
          / (X1 Y1 Z1 X2 Y2 Z2 outxold outyold outzold : F) R,
    { requires tr mem :=
        (FElem (Some tight_bounds) pX1 X1
         * FElem (Some tight_bounds) pY1 Y1
         * FElem (Some tight_bounds) pZ1 Z1
         * FElem (Some tight_bounds) pX2 X2
         * FElem (Some tight_bounds) pY2 Y2
         * FElem (Some tight_bounds) pZ2 Z2
         * FElem (Some tight_bounds) poutx outxold
         * FElem (Some tight_bounds) pouty outyold
         * FElem (Some tight_bounds) poutz outzold * R)%sep mem;
      ensures tr' mem' :=
        tr = tr'
        /\ exists outx outy outz (* output values *)
                  : F ,
                  (@rcb_add_general_gallina _ a_val three_b_val X1 Y1 Z1 X2 Y2 Z2
           = \<outx, outy, outz\>)
          /\ (FElem (Some tight_bounds) pX1 X1
                * FElem (Some tight_bounds) pY1 Y1
                * FElem (Some tight_bounds) pZ1 Z1
                * FElem (Some tight_bounds) pX2 X2
                * FElem (Some tight_bounds) pY2 Y2
                * FElem (Some tight_bounds) pZ2 Z2
                * FElem (Some tight_bounds) poutx outx
                * FElem (Some tight_bounds) pouty outy
                * FElem (Some tight_bounds) poutz outz * R)%sep mem'}.

  (** Downstream compile lemma: lets a later Rupicola derivation call
      "curve_add_general" as a single [nlet_eq] step.  Clone of
      [compile_ladderstep]. *)
  Lemma compile_rcb_add_general {tr m l functions}
        (x1 y1 z1 x2 y2 z2 outx1 outy1 outz1 : F)
        {P} {pred: P (@rcb_add_general_gallina _ a_val three_b_val x1 y1 z1 x2 y2 z2) -> predicate}
        {k: nlet_eq_k P (@rcb_add_general_gallina _ a_val three_b_val x1 y1 z1 x2 y2 z2)} {k_impl} :
    let v := @rcb_add_general_gallina _ a_val three_b_val x1 y1 z1 x2 y2 z2 in
    forall
           Rout
           X1_ptr X1_var Y1_ptr Y1_var Z1_ptr Z1_var
           X2_ptr X2_var Y2_ptr Y2_var Z2_ptr Z2_var
           outx_ptr outx_var outy_ptr outy_var outz_ptr outz_var,

      spec_of_rcb_add_general functions ->

      (FElem (Some tight_bounds) X1_ptr x1 * FElem (Some tight_bounds) Y1_ptr y1 *
       FElem (Some tight_bounds) Z1_ptr z1 * FElem (Some tight_bounds) X2_ptr x2 *
       FElem (Some tight_bounds) Y2_ptr y2 * FElem (Some tight_bounds) Z2_ptr z2 *
       FElem (Some tight_bounds) outx_ptr outx1 *
       FElem (Some tight_bounds) outy_ptr outy1 * FElem (Some tight_bounds) outz_ptr outz1 * Rout)%sep m ->

      map.get l X1_var = Some X1_ptr ->
      map.get l Y1_var = Some Y1_ptr ->
      map.get l Z1_var = Some Z1_ptr ->
      map.get l X2_var = Some X2_ptr ->
      map.get l Y2_var = Some Y2_ptr ->
      map.get l Z2_var = Some Z2_ptr ->
      map.get l outx_var = Some outx_ptr ->
      map.get l outy_var = Some outy_ptr ->
      map.get l outz_var = Some outz_ptr ->

      (let v := v in
       forall (* output values *) m',
       let '\<outx', outy', outz'\> := @rcb_add_general_gallina _ a_val three_b_val x1 y1 z1 x2 y2 z2 in
            (FElem (Some tight_bounds) X1_ptr x1 * FElem (Some tight_bounds) Y1_ptr y1 *
            FElem (Some tight_bounds) Z1_ptr z1 * FElem (Some tight_bounds) X2_ptr x2 *
            FElem (Some tight_bounds) Y2_ptr y2 * FElem (Some tight_bounds) Z2_ptr z2 *
            FElem (Some tight_bounds) outx_ptr outx' *
            FElem (Some tight_bounds) outy_ptr outy' * FElem (Some tight_bounds) outz_ptr outz' * Rout)%sep m' ->
         (<{ Trace := tr;
             Memory := m';
             Locals := l;
             Functions := functions }>
          k_impl
          <{ pred (k v eq_refl) }>)) ->

      <{ Trace := tr;
         Memory := m;
         Locals := l;
         Functions := functions }>
      cmd.seq
        (cmd.call [] "curve_add_general"
                  [ expr.var outx_var; expr.var outy_var;
                  expr.var outz_var;
                  expr.var X1_var; expr.var Y1_var; expr.var Z1_var;
                  expr.var X2_var; expr.var Y2_var; expr.var Z2_var])
        k_impl
      <{ pred (nlet_eq
                 [outx_var; outy_var; outz_var]
                 v k) }>.
  Proof.
    (* PORT-CHECK: proof script cloned verbatim from compile_ladderstep
       (CurveAdd.v).
       RESOLVED 2026-08-28: replayed; Qed succeeds unchanged. *)
    repeat straightline'.
    handle_call.
    lazymatch goal with
    | Hcont : (forall m', _ -> _),
      Heq : rcb_add_general_gallina _ _ _ _ _ _ = _,
      Hsep : sep _ _ _ |- _ =>
      apply Hcont; rewrite Heq; ecancel_assumption
    end.
  Qed.

  Local Ltac ecancel_assumption ::= ecancel_assumption_impl.

  (* Spec for the three_b constant loader function *)
  Instance spec_of_three_b_loader : spec_of three_b_name :=
    fnspec! three_b_name (pout : word) / (outold : F) Rout,
    { requires tr mem :=
        (FElem None pout outold * Rout)%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        (FElem (Some loose_bounds) pout three_b_val * Rout)%sep mem' }.

  (* Spec for the a constant loader function — same shape, second
     constant. *)
  Instance spec_of_a_loader : spec_of a_name :=
    fnspec! a_name (pout : word) / (outold : F) Rout,
    { requires tr mem :=
        (FElem None pout outold * Rout)%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        (FElem (Some loose_bounds) pout a_val * Rout)%sep mem' }.

  (* Compilation lemma for loading the three_b constant *)
  Lemma compile_load_three_b {tr m l functions}
        {P} {pred: P three_b_val -> predicate}
        {k: nlet_eq_k P three_b_val} {k_impl} :
    let v := three_b_val in
    forall
           R out out_ptr out_var out_bounds,
      spec_of_three_b_loader functions ->
      map.get l out_var = Some out_ptr ->
      (FElem out_bounds out_ptr out * R)%sep m ->
      (let v := v in
       forall m',
         (FElem (Some loose_bounds) out_ptr v * R)%sep m' ->
         (<{ Trace := tr;
             Memory := m';
             Locals := l;
             Functions := functions }>
          k_impl
          <{ pred (k v eq_refl) }>)) ->
      <{ Trace := tr;
         Memory := m;
         Locals := l;
         Functions := functions }>
      cmd.seq
        (cmd.call [] three_b_name [expr.var out_var])
        k_impl
      <{ pred (nlet_eq [out_var] v k) }>.
  Proof.
    repeat straightline'.
    handle_call.
    lazymatch goal with
    | |- sep _ _ _ => ecancel_assumption
    | _ => idtac
    end.
    sepsimpl; repeat straightline'; subst; eauto.
  Qed.

  (* Compilation lemma for loading the a constant — verbatim clone of
     compile_load_three_b with a_name / a_val. *)
  Lemma compile_load_a {tr m l functions}
        {P} {pred: P a_val -> predicate}
        {k: nlet_eq_k P a_val} {k_impl} :
    let v := a_val in
    forall
           R out out_ptr out_var out_bounds,
      spec_of_a_loader functions ->
      map.get l out_var = Some out_ptr ->
      (FElem out_bounds out_ptr out * R)%sep m ->
      (let v := v in
       forall m',
         (FElem (Some loose_bounds) out_ptr v * R)%sep m' ->
         (<{ Trace := tr;
             Memory := m';
             Locals := l;
             Functions := functions }>
          k_impl
          <{ pred (k v eq_refl) }>)) ->
      <{ Trace := tr;
         Memory := m;
         Locals := l;
         Functions := functions }>
      cmd.seq
        (cmd.call [] a_name [expr.var out_var])
        k_impl
      <{ pred (nlet_eq [out_var] v k) }>.
  Proof.
    repeat straightline'.
    handle_call.
    lazymatch goal with
    | |- sep _ _ _ => ecancel_assumption
    | _ => idtac
    end.
    sepsimpl; repeat straightline'; subst; eauto.
  Qed.

  Local Hint Extern 5
    (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ three_b_val _))) =>
    simple eapply compile_load_three_b; shelve : compiler.

  (* PORT-CHECK: second constant-loader hint.  The pattern keys on the
     Local Definition a_val, exactly as the three_b hint keys on
     three_b_val.  If both hints are candidates at the same priority
     and misfire (each pattern is a distinct constant so they should
     not), disambiguate by priority (5 vs 6).
     RESOLVED 2026-08-28: both hints at priority 5 fire on their own
     constants; no misfire observed in the derivation. *)
  Local Hint Extern 5
    (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ a_val _))) =>
    simple eapply compile_load_a; shelve : compiler.

  (* Bounds tightening: since loose_bounds = tight_bounds, we can go
     loose→tight (reverse of relax_bounds_FElem). Needed because add
     produces loose_bounds but sub/mul expect tight_bounds inputs. *)
  Local Lemma tighten_bounds_FElem x_ptr x
    : Lift1Prop.impl1 (FElem (Some loose_bounds) x_ptr x)
                      (FElem (Some tight_bounds) x_ptr x).
  Proof. rewrite Hbounds_eq. reflexivity. Qed.
  Local Hint Immediate tighten_bounds_FElem : ecancel_impl.

  (* PORT-CHECK: derivation driver cloned from CurveAdd.v.  Two
     unverified deltas vs the attested a=0 run:
     (1) the callee list adds a_name — CurveAdd.v attests
         [mul; add; sub; three_b_name]; the extra loader is assumed to
         be handled the same way (its spec_of instance is in scope and
         its Hint Extern fires on the [stack a_val] binding);
     (2) chain length 42 nlets vs 34 — the [compile] tactic has not
         been timed on this length; if it stalls, apply the
         MSM helper-extraction pattern (split the chain at S18/S24)
         before concluding the approach fails.
     RESOLVED 2026-08-28: [compile] handles the 42-nlet chain with
     both loaders in one run (whole-file compile finishes in minutes);
     no split was needed. *)
  Derive rcb_add_general_body in
         (defn! "curve_add_general"
                ("outx", "outy", "outz", "X1", "Y1", "Z1", "X2", "Y2", "Z2")
              { rcb_add_general_body },
           implements @rcb_add_general_gallina _ a_val three_b_val
                      using [mul; add; sub; three_b_name; a_name])
         as rcb_add_general_correct.
  Proof. compile. Qed.

End __.

#[global] Existing Instance spec_of_rcb_add_general.

#[global]
Hint Extern 8 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (rcb_add_general_gallina _ _ _ _ _ _) _))) =>
       simple eapply compile_rcb_add_general; shelve : compiler.

(** * Instantiation plan (per curve)

    The Section above is abstract in FieldParameters /
    FieldRepresentation and in the two constant felems + loader names.
    Per curve, the instantiation needs five ingredients; the first
    three already exist.

    ** P-256

    - FieldParameters / FieldRepresentation:
      [Bedrock.Field.Synthesis.Examples.p256_prime] provides
      [p256_field_parameters] (prefix "p256_coord_", so the callee
      names are "p256_coord_mul" / "p256_coord_add" /
      "p256_coord_sub"), [p256_field_parameters_ok], [p256_frep],
      [p256_frep_ok], on Bitwidth64 / BasicC64Semantics (4 limbs).
    - Constants: [src/Bedrock/Curve/P256Curve_G1.v] defines
      [p256_a_mont_list]    = a_mont_list m bw n m' a   (a = -3 mod m)
      [p256_three_b_mont]   = three_b_mont_list m bw n m' three_b
      with validity lemmas ([p256_three_b_mont_valid], and the a-side
      analogue), 4 Montgomery limbs each.
    - Loader functions: clone
      [Bedrock.Field.Synthesis.Examples.bls12_three_b] twice: a
      bedrock2 function "p256_three_b" (resp. "p256_a_const") that
      stores the 4 precomputed limbs of [p256_three_b_mont]
      (resp. [p256_a_mont_list]) into its out buffer, plus the proof
      of [spec_of_three_b_loader] (resp. [spec_of_a_loader]) — i.e.
      feval of the stored felem equals the constant, bounded_by
      loose_bounds.
    - Hbounds_eq (loose_bounds = tight_bounds): holds for the
      word-by-word-Montgomery FieldRepresentation used by the BLS12
      instantiations of CurveAdd.v; the NIST curves use the same
      representation family, so the same proof (reflexivity /
      vm_compute on the bounds records) applies.
      PORT-CHECK: verify against [p256_frep] specifically.
    - Bound felems: [maybe_bounded (Some loose_bounds)] witnesses for
      the two constant felems, from the validity lemmas above.

    Then:
      Definition p256_curve_add_general_body :=
        rcb_add_general_body (* ctx *) "p256_three_b" "p256_a_const".
    and register ("curve_add_general", p256_curve_add_general_body)
    together with the two loader functions and the field ops in the
    function table (the pattern of TestFp2.v /
    [P256Curve_G1.v]'s table).  Bridging
    [spec_of_rcb_add_general] to the Bignum-level
    [spec_of_P256_G1_add] of P256_G1_Add_Spec.v (same op order, same
    ABI [poutx;pouty;poutz;pX1;pY1;pZ1;pX2;pY2;pZ2]) goes through the
    feval chain exactly as the BLS12 files bridge FElem specs to
    MontgomeryCurveSpecs; once done, the hand-written [P256_G1_add]
    body and its 1400-line WP proof can be retired.

    ** P-384

    Same recipe with
    [Bedrock.Field.Synthesis.Examples.p384_field]:
    [p384_field_parameters] (prefix "p384_coord_"), [p384_frep],
    6 limbs; constants a = -3 mod p384_m and 3b from the FIPS b
    (values as in NistG1AddRustCmd.v §2: [p384_a_bytes] /
    [p384_threeb_bytes] are the same numbers in byte form), encoded
    via a_mont_list / three_b_mont_list at bw=64, n=6.

    ** P-224

    Same recipe with
    [Bedrock.Field.Synthesis.Examples.p224_field]:
    [p224_field_parameters] (prefix "p224_coord_"), [p224_frep],
    4 limbs; a = -3 mod p224_m, 3b from the SEC-2 b (cf.
    [p224_b] in NistG1AddRustCmd.v §2).

    ** Not covered

    P-521 uses an unsaturated-Solinas representation, not
    word-by-word Montgomery; Hbounds_eq (loose = tight) FAILS there,
    so this derivation does not instantiate to P-521 as-is.  The
    P-521 path stays on the RustCmd pipeline (NistG1AddRustCmd.v). *)
