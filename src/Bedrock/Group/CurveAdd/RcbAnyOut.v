(** * The a = 0 RCB addition and doubling bodies with unconstrained outputs.

    [CurveAdd.spec_of_ladderstep] and [PointDoubleA0.spec_of_rcb_double_a0]
    require each OUTPUT buffer to hold a tight field element before the
    call.  A caller that passes fresh stack memory (the copy-out
    wrappers [msm_curve_add] / [msm_curve_double] of
    [BLS12_G1ArenaRust.v]) cannot establish that: [stackalloc] gives
    arbitrary bytes, i.e. [FElem None].  The derived code never reads
    its output buffers before writing them, so the same derivation goes
    through with [FElem None] outputs.

    This file re-runs the two Rupicola derivations of [CurveAdd.v] and
    [PointDoubleA0.v] against specs whose outputs are [FElem None]
    (same Gallina programs, same callees, same argument names), and
    checks by [reflexivity] that the derived bodies are the bodies
    already emitted ([ladderstep_body], [rcb_double_a0_body]).  So the
    shipped code satisfies the weaker-precondition specs
    [spec_of_ladderstep_anyout] / [spec_of_rcb_double_a0_anyout]
    ([ladderstep_anyout_correct], [rcb_double_a0_anyout_correct]). *)

Require Import Rupicola.Lib.Api. Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Bedrock.Group.CurveAdd.CurveAdd.
Require Import Bedrock.Group.CurveAdd.PointDoubleA0.
Local Open Scope Z_scope.

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
  Context (three_b : felem).
  Context (three_b_name : string).
  Context (Hb_bounds : maybe_bounded (Some loose_bounds) three_b).

  Local Definition three_b_val : F := feval (proj1_sig three_b).

  #[local] Instance spec_of_ladderstep_anyout : spec_of "curve_add" | 0 :=
    fnspec! "curve_add"
          (pX1 pX2 pY1 pY2 pZ1 pZ2 pXout pYout pZout : word)
          / (X1 X2 Y1 Y2 Z1 Z2 Xoutold Youtold Zoutold : F) R,
    { requires tr mem :=
        (FElem (Some tight_bounds) pX1 X1
         * FElem (Some tight_bounds) pX2 X2
         * FElem (Some tight_bounds) pY1 Y1
         * FElem (Some tight_bounds) pY2 Y2
         * FElem (Some tight_bounds) pZ1 Z1
         * FElem (Some tight_bounds) pZ2 Z2
         * FElem None pXout Xoutold
         * FElem None pYout Youtold
         * FElem None pZout Zoutold * R)%sep mem;
      ensures tr' mem' :=
        tr = tr'
        /\ exists Xout Yout Zout : F,
             (@ladderstep_gallina _ three_b_val X1 X2 Y1 Y2 Z1 Z2
              = \<Xout, Yout, Zout\>)
          /\ (FElem (Some tight_bounds) pX1 X1
                * FElem (Some tight_bounds) pX2 X2
                * FElem (Some tight_bounds) pY1 Y1
                * FElem (Some tight_bounds) pY2 Y2
                * FElem (Some tight_bounds) pZ1 Z1
                * FElem (Some tight_bounds) pZ2 Z2
                * FElem (Some tight_bounds) pXout Xout
                * FElem (Some tight_bounds) pYout Yout
                * FElem (Some tight_bounds) pZout Zout * R)%sep mem'}.

  #[local] Instance spec_of_rcb_double_a0_anyout : spec_of "curve_double_a0" | 0 :=
    fnspec! "curve_double_a0"
          (pXin pYin pZin pXout pYout pZout : word)
          / (X Y Z Xold Yold Zold : F) R,
    { requires tr mem :=
        (FElem (Some tight_bounds) pXin X
         * FElem (Some tight_bounds) pYin Y
         * FElem (Some tight_bounds) pZin Z
         * FElem None pXout Xold
         * FElem None pYout Yold
         * FElem None pZout Zold * R)%sep mem;
      ensures tr' mem' :=
        tr = tr'
        /\ exists Xo Yo Zo : F,
             (@rcb_double_a0_gallina _ three_b_val X Y Z
              = \<Xo, Yo, Zo\>)
             /\ (FElem (Some tight_bounds) pXin X
                 * FElem (Some tight_bounds) pYin Y
                 * FElem (Some tight_bounds) pZin Z
                 * FElem (Some tight_bounds) pXout Xo
                 * FElem (Some tight_bounds) pYout Yo
                 * FElem (Some tight_bounds) pZout Zo * R)%sep mem' }.

  Local Ltac ecancel_assumption ::= ecancel_assumption_impl.

  #[local] Instance spec_of_three_b_loader_anyout : spec_of three_b_name | 0 :=
    fnspec! three_b_name (pout : word) / (outold : F) Rout,
    { requires tr mem :=
        (FElem None pout outold * Rout)%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        (FElem (Some loose_bounds) pout three_b_val * Rout)%sep mem' }.

  Lemma compile_load_three_b_anyout {tr m l functions}
        {P} {pred: P three_b_val -> predicate}
        {k: nlet_eq_k P three_b_val} {k_impl} :
    let v := three_b_val in
    forall
           R out out_ptr out_var out_bounds,
      spec_of_three_b_loader_anyout functions ->
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

  Local Hint Extern 5
    (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ three_b_val _))) =>
    simple eapply compile_load_three_b_anyout; shelve : compiler.

  Local Lemma tighten_bounds_FElem x_ptr x
    : Lift1Prop.impl1 (FElem (Some loose_bounds) x_ptr x)
                      (FElem (Some tight_bounds) x_ptr x).
  Proof. rewrite Hbounds_eq. reflexivity. Qed.
  Local Hint Immediate tighten_bounds_FElem : ecancel_impl.

  Derive ladderstep_body_anyout SuchThat
         (defn! "curve_add"
                ("X1", "X2", "Y1", "Y2", "Z1", "Z2", "Xout", "Yout", "Zout")
              { ladderstep_body_anyout },
           implements @ladderstep_gallina _ three_b_val
                      using [mul; add; sub; three_b_name])
         As ladderstep_anyout_derived.
  Proof. compile. Qed.

  Derive rcb_double_a0_body_anyout SuchThat
         (defn! "curve_double_a0"
                ("Xin", "Yin", "Zin", "Xout", "Yout", "Zout")
              { rcb_double_a0_body_anyout },
           implements @rcb_double_a0_gallina _ three_b_val
                      using [mul; add; sub; three_b_name])
         As rcb_double_a0_anyout_derived.
  Proof. compile. Qed.

  (** The derived bodies are the ones already emitted. *)
  Lemma ladderstep_body_anyout_eq :
    ladderstep_body_anyout = ladderstep_body three_b_name.
  Proof. reflexivity. Qed.

  Lemma rcb_double_a0_body_anyout_eq :
    rcb_double_a0_body_anyout = rcb_double_a0_body three_b_name.
  Proof. reflexivity. Qed.
End __.
