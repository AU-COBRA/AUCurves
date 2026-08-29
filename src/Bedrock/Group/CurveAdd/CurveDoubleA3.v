(** * Rupicola derivation of the a = -3 Renes-Costello-Batina
      complete point DOUBLING (RCB 2015, Algorithm 6).

    Structural clone of [CurveDoubleGeneralA.v] (the general-a
    DOUBLING derivation, Algorithm 3) with the [a_const] block deleted
    and [three_b] replaced by [b], exactly as [CurveAddA3.v] relates
    to [CurveAddGeneralA.v].

    Op counts:

      Algorithm 3 (general a)  31 ops = 8M + 3S + 3 m_a + 2 m_3b + 15 add
                                      = 16 multiplications, 15 add/sub
      Algorithm 6 (a = -3)     34 ops = 8M + 3S + 2 m_b          + 21 add
                                      = 13 multiplications, 21 add/sub

    Three multiplications traded for six additions, and one stack
    buffer saved (one constant instead of two; t0..t3 in both).

    Source: Renes, Costello, Batina, "Complete addition formulas for
    prime order elliptic curves", EUROCRYPT 2016 / ePrint 2015/1060,
    Algorithm 6 ("Complete, projective point doubling for prime order
    short Weierstrass curves E/Fq : y^2 = x^3 - 3x + b"), EFD entry
    dbl-2015-rcb.  Steps below are numbered E1-E34 after that
    algorithm's line numbers.  As with Algorithm 3, the three
    squarings are written [x *F x] (binary [mul]) so that the callee
    list is [mul; add; sub] plus the single loader.

    Like Algorithm 3, Algorithm 6 is NOT the addition formula
    specialised to P1 = P2: its lines 32-34 compute Z3 = 8 Y^3 Z using
    the curve equation.  What IS an unconditional polynomial identity
    is Algorithm 6 = Algorithm 3 at (a, 3b) := (-3, 3b), proved in
    [CurveA3Equiv.v]; that is the statement this file's users need,
    and it needs no on-curve hypothesis.

    Honesty ledger (this file): 0 Admitted, 0 Axiom.  Written
    statically (no compiler run); unverified API details are flagged
    (* PORT-CHECK: ... *). *)

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

(** The single curve constant: b of y^2 = x^3 - 3x + b. *)
Context {b_val : F}.

  (** a = -3 RCB complete doubling, Algorithm 6, 34 field operations.
      Step markers E1-E34 are the line numbers of Algorithm 6 (RCB
      2015).  Paper variable -> binder: t0..t3 -> t0..t3 (stack),
      X3 -> outx, Y3 -> outy, Z3 -> outz, b -> b_const (stack).

      [stack] marks the FIRST binding of each stack-allocated
      temporary (b_const, t0..t3); outx/outy/outz are the caller's
      output buffers, so their first bindings (E10, E8, E6) are plain
      [let/n].

      PORT-CHECK (A): the aliased binops (E5 t3 := t3+t3, E7, E10,
      E21, E23, E29, E33, E34, and the in-place updates E9/E19/E20/
      E25/E27/E31) are the shapes already attested by
      [rcb_double_general_gallina] (D5/D7/D26/D30/D31) and by
      PointDouble.v's compiled [t := t +F t].

      PORT-CHECK (S): E1-E3 could be [square] instead of [mul]; kept
      as [mul] for the structural clone, as in Algorithm 3. *)
  Definition rcb_double_a3_gallina
             (X1 Y1 Z1 : F) : \<< F, F, F \>> :=
    let/n b_const := stack b_val in
    let/n t0 := stack (X1 *F X1) in       (* E1  t0 = X^2 *)
    let/n t1 := stack (Y1 *F Y1) in       (* E2  t1 = Y^2 *)
    let/n t2 := stack (Z1 *F Z1) in       (* E3  t2 = Z^2 *)
    let/n t3 := stack (X1 *F Y1) in       (* E4 *)
    let/n t3 := (t3 +F t3) in             (* E5  t3 = 2XY *)
    let/n outz := (X1 *F Z1) in           (* E6 *)
    let/n outz := (outz +F outz) in       (* E7  outz = 2XZ *)
    let/n outy := (b_const *F t2) in      (* E8  outy = b*Z^2 *)
    let/n outy := (outy -F outz) in       (* E9  outy = b*Z^2 - 2XZ *)
    let/n outx := (outy +F outy) in       (* E10 *)
    let/n outy := (outx +F outy) in       (* E11 outy = 3(bZ^2 - 2XZ) *)
    let/n outx := (t1 -F outy) in         (* E12 outx = Y^2 - that *)
    let/n outy := (t1 +F outy) in         (* E13 outy = Y^2 + that *)
    let/n outy := (outx *F outy) in       (* E14 *)
    let/n outx := (outx *F t3) in         (* E15 *)
    let/n t3 := (t2 +F t2) in             (* E16 *)
    let/n t2 := (t2 +F t3) in             (* E17 t2 = 3Z^2 *)
    let/n outz := (b_const *F outz) in    (* E18 outz = b*2XZ *)
    let/n outz := (outz -F t2) in         (* E19 *)
    let/n outz := (outz -F t0) in         (* E20 outz = b*2XZ - 3Z^2 - X^2 *)
    let/n t3 := (outz +F outz) in         (* E21 *)
    let/n outz := (outz +F t3) in         (* E22 outz = 3*that *)
    let/n t3 := (t0 +F t0) in             (* E23 *)
    let/n t0 := (t3 +F t0) in             (* E24 t0 = 3X^2 *)
    let/n t0 := (t0 -F t2) in             (* E25 t0 = 3X^2 - 3Z^2 *)
    let/n t0 := (t0 *F outz) in           (* E26 *)
    let/n outy := (outy +F t0) in         (* E27 Y3 *)
    let/n t0 := (Y1 *F Z1) in             (* E28 *)
    let/n t0 := (t0 +F t0) in             (* E29 t0 = 2YZ *)
    let/n outz := (t0 *F outz) in         (* E30 *)
    let/n outx := (outx -F outz) in       (* E31 X3 *)
    let/n outz := (t0 *F t1) in           (* E32 outz = 2Y^3 Z *)
    let/n outz := (outz +F outz) in       (* E33 *)
    let/n outz := (outz +F outz) in       (* E34 Z3 = 8Y^3 Z *)
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

  Context (b_const : felem).
  Context (b_name : string).
  Context (Hb_bounds : maybe_bounded (Some loose_bounds) b_const).

  Local Definition b_val : F := feval (proj1_sig b_const).

  (** Calling convention: outputs first, then the input point. *)
  Instance spec_of_rcb_double_a3 : spec_of "curve_double_a3" :=
    fnspec! "curve_double_a3"
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
                  (@rcb_double_a3_gallina _ b_val X1 Y1 Z1
           = \<outx, outy, outz\>)
          /\ (FElem (Some tight_bounds) pX1 X1
                * FElem (Some tight_bounds) pY1 Y1
                * FElem (Some tight_bounds) pZ1 Z1
                * FElem (Some tight_bounds) poutx outx
                * FElem (Some tight_bounds) pouty outy
                * FElem (Some tight_bounds) poutz outz * R)%sep mem'}.

  (** Downstream compile lemma.  Clone of
      [compile_rcb_double_general]. *)
  Lemma compile_rcb_double_a3 {tr m l functions}
        (x1 y1 z1 outx1 outy1 outz1 : F)
        {P} {pred: P (@rcb_double_a3_gallina _ b_val x1 y1 z1) -> predicate}
        {k: nlet_eq_k P (@rcb_double_a3_gallina _ b_val x1 y1 z1)} {k_impl} :
    let v := @rcb_double_a3_gallina _ b_val x1 y1 z1 in
    forall
           Rout
           X1_ptr X1_var Y1_ptr Y1_var Z1_ptr Z1_var
           outx_ptr outx_var outy_ptr outy_var outz_ptr outz_var,

      spec_of_rcb_double_a3 functions ->

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
       let '\<outx', outy', outz'\> := @rcb_double_a3_gallina _ b_val x1 y1 z1 in
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
        (cmd.call [] "curve_double_a3"
                  [ expr.var outx_var; expr.var outy_var;
                  expr.var outz_var;
                  expr.var X1_var; expr.var Y1_var; expr.var Z1_var])
        k_impl
      <{ pred (nlet_eq
                 [outx_var; outy_var; outz_var]
                 v k) }>.
  Proof.
    repeat straightline'.
    handle_call.
    lazymatch goal with
    | Hcont : (forall m', _ -> _),
      Heq : rcb_double_a3_gallina _ _ _ = _,
      Hsep : sep _ _ _ |- _ =>
      apply Hcont; rewrite Heq; ecancel_assumption
    end.
  Qed.

  Local Ltac ecancel_assumption ::= ecancel_assumption_impl.

  (** Loader spec and loader compilation lemma: verbatim duplicates of
      CurveAddA3.v, duplicated (not imported) so that this file does
      not depend on the addition derivation, exactly as
      CurveDoubleGeneralA.v duplicates CurveAddGeneralA.v's.  The two
      copies are convertible once the felem / name arguments are
      supplied, so the per-curve file discharges this copy from the
      addition loader proof by [exact]. *)
  Instance spec_of_b_loader : spec_of b_name :=
    fnspec! b_name (pout : word) / (outold : F) Rout,
    { requires tr mem :=
        (FElem None pout outold * Rout)%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        (FElem (Some loose_bounds) pout b_val * Rout)%sep mem' }.

  Lemma compile_load_b {tr m l functions}
        {P} {pred: P b_val -> predicate}
        {k: nlet_eq_k P b_val} {k_impl} :
    let v := b_val in
    forall
           R out out_ptr out_var out_bounds,
      spec_of_b_loader functions ->
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
        (cmd.call [] b_name [expr.var out_var])
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
    (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ b_val _))) =>
    simple eapply compile_load_b; shelve : compiler.

  Local Lemma tighten_bounds_FElem x_ptr x
    : Lift1Prop.impl1 (FElem (Some loose_bounds) x_ptr x)
                      (FElem (Some tight_bounds) x_ptr x).
  Proof. rewrite Hbounds_eq. reflexivity. Qed.
  Local Hint Immediate tighten_bounds_FElem : ecancel_impl.

  (** Derivation driver: 35 nlets, one loader, four stack
      temporaries.  Strictly smaller than the attested 42-nlet
      two-loader run of CurveAddGeneralA.v. *)
  Derive rcb_double_a3_body in
         (defn! "curve_double_a3"
                ("outx", "outy", "outz", "X1", "Y1", "Z1")
              { rcb_double_a3_body },
           implements @rcb_double_a3_gallina _ b_val
                      using [mul; add; sub; b_name])
         as rcb_double_a3_correct.
  Proof. compile. Qed.

End __.

#[global] Existing Instance spec_of_rcb_double_a3.

#[global]
Hint Extern 8 (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (rcb_double_a3_gallina _ _ _) _))) =>
       simple eapply compile_rcb_double_a3; shelve : compiler.
