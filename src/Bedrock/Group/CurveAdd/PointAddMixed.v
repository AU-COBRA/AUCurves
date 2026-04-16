(** * Mixed-affine point addition for y² = x³ + b (a=0).

    Adds Jacobian (X1:Y1:Z1) to affine (x2, y2, one) where one=1.
    The 'one' parameter holds the field representation of 1 in memory.

    Same complete formula as ladderstep but with Z2 read from 'one'
    and t2 = Z1 (copy, not mul). Saves 1 field multiplication. *)

Require Import Rupicola.Lib.Api. Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Bedrock.Group.CurveAdd.CurveAdd.
Local Open Scope Z_scope.

Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Section Gallina.

Context {field_parameters : FieldParameters}.
Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
Context {field_representation : FieldRepresentation}.

Local Notation F := (F M_pos).
Local Infix "+F" := (@F.add M_pos) (at level 100).
Local Infix "-F" := (@F.sub M_pos) (at level 100).
Local Infix "*F" := (@F.mul M_pos) (at level 90).

Context {three_b_val : F}.

  (** Mixed-affine: same as ladderstep but t2 = Z1 (copy) instead of Z1*Z2 (mul).
      Takes 6 field inputs: X1, x2, Y1, y2, Z1, one (where one = F.of_Z _ 1).
      The formula reads 'one' wherever ladderstep reads Z2.
      Cost: 11M + 2*three_b + copy + many add/sub *)
  Definition point_add_mixed_gallina
             (X1 x2 Y1 y2 Z1 one : F) : \<< F, F, F \>> :=
    let/n three_b := stack three_b_val in
    let/n t0 := stack (X1 *F x2) in
    let/n t1 := stack (Y1 *F y2) in
    let/n t2 := stack Z1 in                  (* Z1*one = Z1 — COPY not MUL *)
    let/n t3 := stack (X1 +F Y1) in
    let/n t4 := stack (x2 +F y2) in
    let/n t3 := (t3 *F t4) in
    let/n t4 := (t0 +F t1) in
    let/n t3 := (t3 -F t4) in
    let/n t4 := (X1 +F Z1) in
    let/n t5 := stack (x2 +F one) in         (* x2 + one, was X2 + Z2 *)
    let/n t4 := (t4 *F t5) in
    let/n t5 := (t0 +F t2) in
    let/n t4 := (t4 -F t5) in
    let/n t5 := (Y1 +F Z1) in
    let/n Xout := (y2 +F one) in             (* y2 + one, was Y2 + Z2 *)
    let/n t5 := (t5 *F Xout) in
    let/n Xout := (t1 +F t2) in
    let/n t5 := (t5 -F Xout) in
    let/n Zout := (three_b *F t2) in
    let/n Xout := (t1 -F Zout) in
    let/n Zout := (Zout +F t1) in
    let/n Yout := (Xout *F Zout) in
    let/n t1 := (t0 +F t0) in
    let/n t1 := (t1 +F t0) in
    let/n t4 := (three_b *F t4) in
    let/n t0 := (t1 *F t4) in
    let/n Yout := (Yout +F t0) in
    let/n t0 := (t5 *F t4) in
    let/n Xout := (t3 *F Xout) in
    let/n Xout := (Xout -F t0) in
    let/n t0 := (t3 *F t1) in
    let/n Zout := (t5 *F Zout) in
    let/n Zout := (Zout +F t0) in
    \<Xout, Yout, Zout\>.

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
  Context (three_b : felem).
  Context (three_b_name : string).
  Context (Hb_bounds : maybe_bounded (Some loose_bounds) three_b).

  Local Definition three_b_val : F := feval (proj1_sig three_b).

  Local Lemma tighten_bounds_FElem x_ptr x
    : Lift1Prop.impl1 (FElem (Some loose_bounds) x_ptr x)
                      (FElem (Some tight_bounds) x_ptr x).
  Proof. rewrite Hbounds_eq. reflexivity. Qed.
  Local Hint Immediate tighten_bounds_FElem : ecancel_impl.

  Local Ltac ecancel_assumption ::= ecancel_assumption_impl.

  Instance spec_of_three_b_loader : spec_of three_b_name :=
    fnspec! three_b_name (pout : word) / (outold : F) Rout,
    { requires tr mem :=
        (FElem None pout outold * Rout)%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        (FElem (Some loose_bounds) pout three_b_val * Rout)%sep mem' }.

  Lemma compile_load_three_b_local {tr m l functions} :
    let v := three_b_val in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
           R out out_ptr out_var out_bounds,
      spec_of_three_b_loader functions ->
      map.get l out_var = Some out_ptr ->
      (FElem out_bounds out_ptr out * R)%sep m ->
      (let v := v in
       forall m',
         (FElem (Some loose_bounds) out_ptr v * R)%sep m' ->
         (<{ Trace := tr; Memory := m'; Locals := l; Functions := functions }>
          k_impl <{ pred (k v eq_refl) }>)) ->
      <{ Trace := tr; Memory := m; Locals := l; Functions := functions }>
      cmd.seq (cmd.call [] three_b_name [expr.var out_var]) k_impl
      <{ pred (nlet_eq [out_var] v k) }>.
  Proof.
    repeat straightline'. handle_call.
    lazymatch goal with | |- sep _ _ _ => ecancel_assumption | _ => idtac end.
    sepsimpl; repeat straightline'; subst; eauto.
  Qed.

  Local Hint Extern 5
    (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ three_b_val _))) =>
    simple eapply compile_load_three_b_local; shelve : compiler.

  (* spec: 6 input FElems + 3 output FElems, preserves inputs *)
  Instance spec_of_point_add_mixed : spec_of "curve_add_mixed" :=
    fnspec! "curve_add_mixed"
          (pX1 px2 pY1 py2 pZ1 pone pXout pYout pZout : word)
          / (X1 x2 Y1 y2 Z1 one Xold Yold Zold : F) R,
    { requires tr mem :=
        (FElem (Some tight_bounds) pX1 X1
         * FElem (Some tight_bounds) px2 x2
         * FElem (Some tight_bounds) pY1 Y1
         * FElem (Some tight_bounds) py2 y2
         * FElem (Some tight_bounds) pZ1 Z1
         * FElem (Some tight_bounds) pone one
         * FElem (Some tight_bounds) pXout Xold
         * FElem (Some tight_bounds) pYout Yold
         * FElem (Some tight_bounds) pZout Zold * R)%sep mem;
      ensures tr' mem' :=
        tr = tr'
        /\ (let '\<Xo, Yo, Zo\> := @point_add_mixed_gallina _ three_b_val X1 x2 Y1 y2 Z1 one in
           (FElem (Some tight_bounds) pX1 X1
            * FElem (Some tight_bounds) px2 x2
            * FElem (Some tight_bounds) pY1 Y1
            * FElem (Some tight_bounds) py2 y2
            * FElem (Some tight_bounds) pZ1 Z1
            * FElem (Some tight_bounds) pone one
            * FElem (Some tight_bounds) pXout Xo
            * FElem (Some tight_bounds) pYout Yo
            * FElem (Some tight_bounds) pZout Zo * R)%sep mem') }.

  Derive point_add_mixed_body SuchThat
         (defn! "curve_add_mixed"
                ("X1", "x2", "Y1", "y2", "Z1", "one", "Xout", "Yout", "Zout")
              { point_add_mixed_body },
           implements @point_add_mixed_gallina _ three_b_val
                      using [mul; add; sub; felem_copy; three_b_name])
         As point_add_mixed_correct.
  Proof. compile. Qed.

End __.

#[global] Existing Instance spec_of_point_add_mixed.
