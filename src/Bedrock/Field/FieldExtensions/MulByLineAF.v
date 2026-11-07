(** * Multiplication of an Fp12 element by a Miller-loop line value, derived by Rupicola over an
      arbitrary field ([Bedrock.Specs.AbstractField]) standing for Fp2.

    The line values of the BLS12 Miller loop ([Theory.BLS12Pairing.Pairing.make_line]) have three
    nonzero Fp2 coefficients out of six: c0.c0 = b0, c0.c1 = b1, c1.c1 = b4 (indices 0, 1, 4).
    [af_mul_by_line_gallina mulxi x0 .. x5 b0 b1 b4] is the in-place [let/n] chain of
    [Theory.BLS12Pairing.SparseLine.mul_by_line6]: with f = a0 + a1 w (a0 = (x0,x1,x2),
    a1 = (x3,x4,x5)) and the line B0 + B1 w (B0 = (b0,b1,0), B1 = (0,b4,0)),
      T0 = a0 B0 (5 multiplications), T1 = a1 B1 (3), c0 = T0 + v T1,
      c1 = (a0 + a1)(B0 + B1) - T0 - T1 (5),
    13 multiplications of the field instead of 18.  [af_mul_by_line_body] is derived from it with
    the AbstractField compile lemmas ([af_mul_by_line_correct], Qed); it calls exactly
    [AbstractField.mul], [add], [sub] and [mulxi_name].  Everything here is Qed. *)

Require Import Rupicola.Lib.Api. Import bedrock2.WeakestPrecondition.
Require Import Bedrock.Specs.AbstractField.
Require Bedrock.Field.FieldExtensions.Compilation2_Fp2.
Require Bedrock.Field.FieldExtensions.CycSqrAF.
Local Open Scope Z_scope.

Section Gallina.
  Context {F : Type} {field_parameters : AbstractField.FieldParameters F}.
  Context (mulxi : F -> F).

  Local Infix "+F" := AbstractField.Fadd (at level 100).
  Local Infix "-F" := AbstractField.Fsub (at level 100).
  Local Infix "*F" := AbstractField.Fmul (at level 90).

  Definition af_mul_by_line_gallina (x0 x1 x2 x3 x4 x5 b0 b1 b4 : F)
    : \<< F, F, F, F, F, F \>> :=
    (* T0 = a0 * (b0, b1, 0) = (s0, t, s1) *)
    let/n s0 := stack (x0 *F b0) in
    let/n s1 := stack (x1 *F b1) in
    let/n t := stack (x0 +F x1) in
    let/n u := stack (b0 +F b1) in
    let/n t := (t *F u) in
    let/n t := (t -F s0) in
    let/n t := (t -F s1) in
    let/n w := stack (x2 *F b1) in
    let/n w := mulxi w in
    let/n s0 := (s0 +F w) in
    let/n w := (x2 *F b0) in
    let/n s1 := (s1 +F w) in
    (* T1 = a1 * b4 v = (xi x5 b4, x3 b4, x4 b4) = (r0, r1, r2) *)
    let/n r0 := stack (x5 *F b4) in
    let/n r0 := mulxi r0 in
    let/n r1 := stack (x3 *F b4) in
    let/n r2 := stack (x4 *F b4) in
    (* a0 + a1, in the slots of a1 *)
    let/n x3 := (x0 +F x3) in
    let/n x4 := (x1 +F x4) in
    let/n x5 := (x2 +F x5) in
    (* U = (a0 + a1) * (b0, b1 + b4, 0) = (w, z, q) *)
    let/n u := (b1 +F b4) in
    let/n w := (x3 *F b0) in
    let/n q := stack (x4 *F u) in
    let/n z := stack (x3 +F x4) in
    let/n e := stack (b0 +F u) in
    let/n z := (z *F e) in
    let/n z := (z -F w) in
    let/n z := (z -F q) in
    let/n e := (x5 *F u) in
    let/n e := mulxi e in
    let/n w := (w +F e) in
    let/n e := (x5 *F b0) in
    let/n q := (q +F e) in
    (* c1 = U - T0 - T1 *)
    let/n x3 := (w -F s0) in
    let/n x3 := (x3 -F r0) in
    let/n x4 := (z -F t) in
    let/n x4 := (x4 -F r1) in
    let/n x5 := (q -F s1) in
    let/n x5 := (x5 -F r2) in
    (* c0 = T0 + v T1 = (s0 + xi r2, t + r0, s1 + r1) *)
    let/n e := mulxi r2 in
    let/n x0 := (s0 +F e) in
    let/n x1 := (t +F r0) in
    let/n x2 := (s1 +F r1) in
    \<x0, x1, x2, x3, x4, x5\>.
End Gallina.

Section Derive.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {F : Type}
          {field_parameters : AbstractField.FieldParameters F}
          {field_representation : AbstractField.FieldRepresentation}
          {field_representation_ok : AbstractField.FieldRepresentation_ok}.

  Local Notation AFElem := Compilation2_Fp2.AFElem.

  #[local, refine]
  Instance afelem_alloc_mbl : Allocable (AFElem None) :=
    {| size_in_bytes := AbstractField.felem_size_in_bytes;
       size_in_bytes_mod := AbstractField.felem_size_in_bytes_mod |}.
  Proof.
    - intros px x m0 H.
      unfold AFElem in H. destruct H as [ws H].
      apply sep_emp_l in H. destruct H as [_ H].
      apply (proj2 (AbstractField.FElem_from_bytes px m0)).
      exists ws. exact H.
    - intros px m0 H.
      apply (proj1 (AbstractField.FElem_from_bytes px m0)) in H.
      destruct H as [ws H].
      exists (AbstractField.feval ws). unfold AFElem. exists ws.
      apply sep_emp_l. split; [ split; [ reflexivity | exact I ] | exact H ].
  Defined.

  Context (Hbounds_eq : AbstractField.loose_bounds = AbstractField.tight_bounds).
  Context (mulxi : F -> F) (mulxi_name : string).

  Local Lemma tighten_bounds_AFElem_mbl x_ptr x
    : Lift1Prop.impl1 (AFElem (Some AbstractField.loose_bounds) x_ptr x)
                      (AFElem (Some AbstractField.tight_bounds) x_ptr x).
  Proof. rewrite Hbounds_eq. reflexivity. Qed.

  #[local] Instance spec_of_af_mul_mbl : spec_of AbstractField.mul :=
    AbstractField.binop_spec AbstractField.bin_mul.
  #[local] Instance spec_of_af_add_mbl : spec_of AbstractField.add :=
    AbstractField.binop_spec AbstractField.bin_add.
  #[local] Instance spec_of_af_sub_mbl : spec_of AbstractField.sub :=
    AbstractField.binop_spec AbstractField.bin_sub.
  #[local] Instance spec_of_af_mulxi_mbl : spec_of mulxi_name :=
    @CycSqrAF.spec_of_af_mulxi _ _ _ _ _ _ F field_parameters field_representation mulxi mulxi_name.

  Local Hint Extern 7
    (WeakestPrecondition.cmd _ _ _ _ _
      (_ (nlet_eq _ (@AbstractField.Fmul _ _ _ _) _))) =>
    simple eapply Compilation2_Fp2.compile_af_mul; shelve : compiler.
  Local Hint Extern 7
    (WeakestPrecondition.cmd _ _ _ _ _
      (_ (nlet_eq _ (@AbstractField.Fadd _ _ _ _) _))) =>
    simple eapply Compilation2_Fp2.compile_af_add; shelve : compiler.
  Local Hint Extern 7
    (WeakestPrecondition.cmd _ _ _ _ _
      (_ (nlet_eq _ (@AbstractField.Fsub _ _ _ _) _))) =>
    simple eapply Compilation2_Fp2.compile_af_sub; shelve : compiler.
  Local Hint Extern 5
    (WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (mulxi _) _))) =>
    simple eapply (@CycSqrAF.compile_af_mulxi _ _ _ _ _ _ _ _ _ _ _ _ _ _ mulxi mulxi_name);
    shelve : compiler.
  Local Hint Immediate Compilation2_Fp2.relax_bounds_AFElem : ecancel_impl.
  Local Hint Immediate Compilation2_Fp2.drop_bounds_AFElem : ecancel_impl.
  Local Hint Immediate tighten_bounds_AFElem_mbl : ecancel_impl.

  Local Ltac ecancel_assumption ::= ecancel_assumption_impl.

  #[local] Instance spec_of_af_mul_by_line : spec_of "bls12_Fp12_mul_by_line" :=
    fnspec! "bls12_Fp12_mul_by_line"
          (p0 p1 p2 p3 p4 p5 q0 q1 q4 : word) / (x0 x1 x2 x3 x4 x5 b0 b1 b4 : F) R,
    { requires tr mem :=
        (AFElem (Some AbstractField.tight_bounds) p0 x0
         * AFElem (Some AbstractField.tight_bounds) p1 x1
         * AFElem (Some AbstractField.tight_bounds) p2 x2
         * AFElem (Some AbstractField.tight_bounds) p3 x3
         * AFElem (Some AbstractField.tight_bounds) p4 x4
         * AFElem (Some AbstractField.tight_bounds) p5 x5
         * AFElem (Some AbstractField.tight_bounds) q0 b0
         * AFElem (Some AbstractField.tight_bounds) q1 b1
         * AFElem (Some AbstractField.tight_bounds) q4 b4 * R)%sep mem;
      ensures tr' mem' :=
        tr = tr'
        /\ exists y0 y1 y2 y3 y4 y5 : F,
          (af_mul_by_line_gallina mulxi x0 x1 x2 x3 x4 x5 b0 b1 b4
           = \<y0, y1, y2, y3, y4, y5\>)
          /\ (AFElem (Some AbstractField.tight_bounds) p0 y0
              * AFElem (Some AbstractField.tight_bounds) p1 y1
              * AFElem (Some AbstractField.tight_bounds) p2 y2
              * AFElem (Some AbstractField.tight_bounds) p3 y3
              * AFElem (Some AbstractField.tight_bounds) p4 y4
              * AFElem (Some AbstractField.tight_bounds) p5 y5
              * AFElem (Some AbstractField.tight_bounds) q0 b0
              * AFElem (Some AbstractField.tight_bounds) q1 b1
              * AFElem (Some AbstractField.tight_bounds) q4 b4 * R)%sep mem' }.

  Derive af_mul_by_line_body SuchThat
         (defn! "bls12_Fp12_mul_by_line"
                ("x0", "x1", "x2", "x3", "x4", "x5", "b0", "b1", "b4")
              { af_mul_by_line_body },
           implements (af_mul_by_line_gallina mulxi)
                      using [AbstractField.mul; AbstractField.add; AbstractField.sub; mulxi_name])
         As af_mul_by_line_correct.
  Proof. compile. Qed.

End Derive.
