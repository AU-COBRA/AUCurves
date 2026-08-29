(** * Rupicola derivation of the general-a Renes-Costello-Batina
      complete point DOUBLING (31 field operations).

    Structural clone of [CurveAddGeneralA.v] (the compiled general-a
    ADDITION derivation): same section layout, same two stack-loaded
    curve constants (a and 3b), same loader specs and loader
    compilation lemmas, same [Derive ... compile] driver.  Written
    statically (no compiler run); every unverified API detail is
    flagged (* PORT-CHECK: ... *).

    Formula: RCB 2015 (ePrint 2015/1060), Algorithm 3 — "complete,
    projective point doubling for arbitrary prime-order short
    Weierstrass curves", cost 8M + 3S + 3m_a + 2m_3b + 15add.  This is
    also the EFD entry dbl-2015-rcb.  The three squarings are written
    as [x *F x] (binary [mul]) so that the callee list is exactly the
    one of the addition ([mul; add; sub] + two loaders); see PORT-CHECK
    (S) below for the [square] variant.

    Op order: the repository contains no dedicated doubling op
    sequence — [g1_double] in pXXX-safe-rust/src/group.rs is
    [g1_add(p, p)], and NistG1AddRustCmd.v transcribes only the
    addition.  The chain below is therefore transcribed directly from
    Algorithm 3, in its published order, with the buffer discipline
    of the addition derivation: t0..t3 are stack temporaries, and
    X3/Y3/Z3 of the paper are the caller-provided output buffers
    outx/outy/outz.  Steps are numbered D1-D31.

    Algorithm 3 is NOT the addition formula specialised to P1 = P2:
    lines 29-31 (Z3 = 8·Y³·Z) use the curve equation
    Y²Z = X³ + aXZ² + bZ³ to replace
    2YZ·(Y² + 3bZ² + 2aXZ) + 2XY·(3X² + aZ²).  Consequently the
    Z-level Gallina spec of the doubling
    ([rcb_double_general_Z_spec], CurveDoubleGeneralA_GallinaToZ.v) is
    stated as the transcription of Algorithm 3 itself, and the
    equality with [add(P, P)] on curve points is a separate theorem
    that this file does not claim. *)

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

  (** General-a RCB complete doubling, Algorithm 3, 31 field
      operations.  Step markers D1-D31 are the line numbers of
      Algorithm 3 (RCB 2015).  Paper variable -> binder:
      t0..t3 -> t0..t3 (stack), X3 -> outx, Y3 -> outy, Z3 -> outz.

      [stack] marks the FIRST binding of each stack-allocated
      temporary (three_b, a_const, t0..t3), exactly as in
      [rcb_add_general_gallina]; outx/outy/outz are the caller's
      output buffers, so their first bindings are plain [let/n].

      PORT-CHECK (A): three steps have dest = both operands
      (D5 t3 := t3 + t3, D7 outz := outz + outz, D26, D30, D31).
      [compile_binop] (Compilation2.v) takes the x-, y- and
      out-FElem facts as three separate hypotheses on the same
      memory, so full aliasing is admissible; PointDouble.v's
      [t := t +F t] (a=0 doubling, compiled) is the attested case.
      D1-D3 (t0 := X1 * X1 etc.) alias the two operands of [mul]
      with a distinct destination; same lemma, same argument.

      PORT-CHECK (S): D1-D3 could be [X1 ^2] ([F.pow _ 2], the
      [square] UnOp, as in PointDouble.v).  That would add [square]
      to the callee list and a [to_Z_pow2] rewrite to the
      GallinaToZ lemma; kept as [mul] for the structural clone. *)
  Definition rcb_double_general_gallina
             (X1 Y1 Z1 : F) : \<< F, F, F \>> :=
    let/n three_b := stack three_b_val in
    let/n a_const := stack a_val in
    let/n t0 := stack (X1 *F X1) in       (* D1  t0 = X^2 *)
    let/n t1 := stack (Y1 *F Y1) in       (* D2  t1 = Y^2 *)
    let/n t2 := stack (Z1 *F Z1) in       (* D3  t2 = Z^2 *)
    let/n t3 := stack (X1 *F Y1) in       (* D4 *)
    let/n t3 := (t3 +F t3) in             (* D5  t3 = 2XY *)
    let/n outz := (X1 *F Z1) in           (* D6 *)
    let/n outz := (outz +F outz) in       (* D7  outz = 2XZ *)
    let/n outx := (a_const *F outz) in    (* D8  outx = a*2XZ *)
    let/n outy := (three_b *F t2) in      (* D9  outy = 3b*Z^2 *)
    let/n outy := (outx +F outy) in       (* D10 outy = 3bZ^2 + 2aXZ *)
    let/n outx := (t1 -F outy) in         (* D11 *)
    let/n outy := (t1 +F outy) in         (* D12 *)
    let/n outy := (outx *F outy) in       (* D13 outy = (Y^2-A)(Y^2+A) *)
    let/n outx := (t3 *F outx) in         (* D14 outx = 2XY(Y^2-A) *)
    let/n outz := (three_b *F outz) in    (* D15 outz = 3b*2XZ *)
    let/n t2 := (a_const *F t2) in        (* D16 t2 = aZ^2 *)
    let/n t3 := (t0 -F t2) in             (* D17 t3 = X^2 - aZ^2 *)
    let/n t3 := (a_const *F t3) in        (* D18 *)
    let/n t3 := (t3 +F outz) in           (* D19 t3 = 3b*2XZ + a(X^2-aZ^2) *)
    let/n outz := (t0 +F t0) in           (* D20 *)
    let/n t0 := (outz +F t0) in           (* D21 t0 = 3X^2 *)
    let/n t0 := (t0 +F t2) in             (* D22 t0 = 3X^2 + aZ^2 *)
    let/n t0 := (t0 *F t3) in             (* D23 *)
    let/n outy := (outy +F t0) in         (* D24 Y3 *)
    let/n t2 := (Y1 *F Z1) in             (* D25 *)
    let/n t2 := (t2 +F t2) in             (* D26 t2 = 2YZ *)
    let/n t0 := (t2 *F t3) in             (* D27 *)
    let/n outx := (outx -F t0) in         (* D28 X3 *)
    let/n outz := (t2 *F t1) in           (* D29 outz = 2Y^3Z *)
    let/n outz := (outz +F outz) in       (* D30 *)
    let/n outz := (outz +F outz) in       (* D31 Z3 = 8Y^3Z *)
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
      loader functions.  Same Context order as CurveAddGeneralA.v, so
      that the section-discharged argument order of
      [rcb_double_general_correct] is the one of
      [rcb_add_general_correct]:
        Hbounds_eq three_b three_b_name a_const a_name marker functions.
      PORT-CHECK (C): that order is what the per-curve [refine]
      assumes (CurveDoubleGeneralA_P256.v §3); Hb_bounds / Ha_bounds
      are unused and drop out, as in the addition. *)
  Context (three_b : felem).
  Context (three_b_name : string).
  Context (Hb_bounds : maybe_bounded (Some loose_bounds) three_b).

  Context (a_const : felem).
  Context (a_name : string).
  Context (Ha_bounds : maybe_bounded (Some loose_bounds) a_const).

  Local Definition three_b_val : F := feval (proj1_sig three_b).
  Local Definition a_val : F := feval (proj1_sig a_const).

  (** Calling convention: outputs first, then the input point
      (the outputs-first ABI of the addition, attested to work with
      the [compile] driver on 2026-08-28). *)
  Instance spec_of_rcb_double_general : spec_of "curve_double_general" :=
    fnspec! "curve_double_general"
          (poutx pouty poutz pX1 pY1 pZ1 : word)
          / (X1 Y1 Z1 outxold outyold outzold : F) R,
    { requires tr mem :=
        (FElem (Some tight_bounds) pX1 X1
         * FElem (Some tight_bounds) pY1 Y1
         * FElem (Some tight_bounds) pZ1 Z1
         * FElem (Some tight_bounds) poutx outxold
         * FElem (Some tight_bounds) pouty outyold
         * FElem (Some tight_bounds) poutz outzold * R)%sep mem;
      ensures tr' mem' :=
        tr = tr'
        /\ exists outx outy outz (* output values *)
                  : F ,
                  (@rcb_double_general_gallina _ a_val three_b_val X1 Y1 Z1
           = \<outx, outy, outz\>)
          /\ (FElem (Some tight_bounds) pX1 X1
                * FElem (Some tight_bounds) pY1 Y1
                * FElem (Some tight_bounds) pZ1 Z1
                * FElem (Some tight_bounds) poutx outx
                * FElem (Some tight_bounds) pouty outy
                * FElem (Some tight_bounds) poutz outz * R)%sep mem'}.

  (** Downstream compile lemma: lets a later Rupicola derivation call
      "curve_double_general" as a single [nlet_eq] step.  Clone of
      [compile_rcb_add_general]. *)
  Lemma compile_rcb_double_general {tr m l functions}
        (x1 y1 z1 outx1 outy1 outz1 : F)
        {P} {pred: P (@rcb_double_general_gallina _ a_val three_b_val x1 y1 z1) -> predicate}
        {k: nlet_eq_k P (@rcb_double_general_gallina _ a_val three_b_val x1 y1 z1)} {k_impl} :
    let v := @rcb_double_general_gallina _ a_val three_b_val x1 y1 z1 in
    forall
           Rout
           X1_ptr X1_var Y1_ptr Y1_var Z1_ptr Z1_var
           outx_ptr outx_var outy_ptr outy_var outz_ptr outz_var,

      spec_of_rcb_double_general functions ->

      (FElem (Some tight_bounds) X1_ptr x1 * FElem (Some tight_bounds) Y1_ptr y1 *
       FElem (Some tight_bounds) Z1_ptr z1 *
       FElem (Some tight_bounds) outx_ptr outx1 *
       FElem (Some tight_bounds) outy_ptr outy1 * FElem (Some tight_bounds) outz_ptr outz1 * Rout)%sep m ->

      map.get l X1_var = Some X1_ptr ->
      map.get l Y1_var = Some Y1_ptr ->
      map.get l Z1_var = Some Z1_ptr ->
      map.get l outx_var = Some outx_ptr ->
      map.get l outy_var = Some outy_ptr ->
      map.get l outz_var = Some outz_ptr ->

      (let v := v in
       forall (* output values *) m',
       let '\<outx', outy', outz'\> := @rcb_double_general_gallina _ a_val three_b_val x1 y1 z1 in
            (FElem (Some tight_bounds) X1_ptr x1 * FElem (Some tight_bounds) Y1_ptr y1 *
            FElem (Some tight_bounds) Z1_ptr z1 *
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
        (cmd.call [] "curve_double_general"
                  [ expr.var outx_var; expr.var outy_var;
                  expr.var outz_var;
                  expr.var X1_var; expr.var Y1_var; expr.var Z1_var])
        k_impl
      <{ pred (nlet_eq
                 [outx_var; outy_var; outz_var]
                 v k) }>.
  Proof.
    (* Proof script cloned from compile_rcb_add_general (Qed on
       2026-08-28); only the match pattern on the Gallina chain
       changes (three arguments instead of six). *)
    repeat straightline'.
    handle_call.
    lazymatch goal with
    | Hcont : (forall m', _ -> _),
      Heq : rcb_double_general_gallina _ _ _ = _,
      Hsep : sep _ _ _ |- _ =>
      apply Hcont; rewrite Heq; ecancel_assumption
    end.
  Qed.

  Local Ltac ecancel_assumption ::= ecancel_assumption_impl.

  (** Loader specs and loader compilation lemmas: verbatim duplicates
      of CurveAddGeneralA.v.  Duplicated rather than imported so that
      this file does not depend on the addition derivation; the two
      copies are definitionally equal once the felem / name arguments
      are supplied (same fnspec, same [feval (proj1_sig _)]), and the
      per-curve files discharge the doubling copy from the addition
      loader proofs by [exact] (PORT-CHECK (L) in
      CurveDoubleGeneralA_P256.v). *)
  Instance spec_of_three_b_loader : spec_of three_b_name :=
    fnspec! three_b_name (pout : word) / (outold : F) Rout,
    { requires tr mem :=
        (FElem None pout outold * Rout)%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        (FElem (Some loose_bounds) pout three_b_val * Rout)%sep mem' }.

  Instance spec_of_a_loader : spec_of a_name :=
    fnspec! a_name (pout : word) / (outold : F) Rout,
    { requires tr mem :=
        (FElem None pout outold * Rout)%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        (FElem (Some loose_bounds) pout a_val * Rout)%sep mem' }.

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

  (** Derivation driver, cloned from CurveAddGeneralA.v (which
      handled 42 nlets with both loaders in one [compile] run).  This
      chain has 33 nlets and four stack temporaries instead of six.
      PORT-CHECK (D): the only new shapes relative to the attested
      run are the aliased binops of PORT-CHECK (A); if [compile]
      stalls on one of them the failing step can be identified by
      truncating the chain after that step. *)
  Derive rcb_double_general_body in
         (defn! "curve_double_general"
                ("outx", "outy", "outz", "X1", "Y1", "Z1")
              { rcb_double_general_body },
           implements @rcb_double_general_gallina _ a_val three_b_val
                      using [mul; add; sub; three_b_name; a_name])
         as rcb_double_general_correct.
  Proof. compile. Qed.

End __.

#[global] Existing Instance spec_of_rcb_double_general.

#[global]
Hint Extern 8 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (rcb_double_general_gallina _ _ _) _))) =>
       simple eapply compile_rcb_double_general; shelve : compiler.

(** * Instantiation plan (per curve)

    Identical to the plan of CurveAddGeneralA.v; every per-curve
    ingredient (FieldParameters / FieldRepresentation, the two
    constant felems, the two loader bodies and their loader-spec
    proofs, Hbounds_eq) is shared with the addition instantiation
    and is imported from CurveAddGeneralA_PXXX.v.  What is new per
    curve:

      Definition pXXX_curve_double_general_func :=
        rcb_double_general_body "pXXX_three_b" "pXXX_a_const".
      Lemma pXXX_curve_double_general_ok : ... spec_of_rcb_double_general ...
        (refine with rcb_double_general_correct, argument order as
        for the addition).
      The loader-spec hypotheses are this file's copies of the
      loader specs; they are discharged from the addition loader
      proofs by conversion.
      Bignum-level spec of "curve_double_general" (ABI
      [poutx; pouty; poutz; pX; pY; pZ]) with the Z-level
      [rcb_double_general_Z_spec] of CurveDoubleGeneralA_GallinaToZ.v,
      and its bridge from [spec_of_rcb_double_general] (the
      _valid_out shape, as for the addition).

    Files: CurveDoubleGeneralA_P256.v, CurveDoubleGeneralA_P384.v,
    CurveDoubleGeneralA_P224.v.  P-521 is not covered (unsaturated
    Solinas representation; Hbounds_eq fails), as for the addition. *)
