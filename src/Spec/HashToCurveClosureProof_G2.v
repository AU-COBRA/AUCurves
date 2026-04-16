(** * G2 point_add and clear_cofactor preserve on_curve_E2.

    Proved algebraically using Field.fsatz over Fp2.
    Mirrors HashToCurveClosureProof.v but works over the quadratic
    extension Fp2 = Fp[u]/(u²+1) instead of Fp.

    Key insight: unfold fp2_cube first, then unfold fp2_sqr in a
    second pass (to catch the fp2_sqr introduced by the cube unfold).
    Without the second pass, nsatz fails because it doesn't recognize
    the mixed fp2_sqr/fp2_mul terms. *)

From Stdlib Require Import ZArith Lia Ring.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Algebra.Hierarchy.
Require Import Spec.HashToCurve.
Require Import Spec.HashToCurveG2.
Require Import Spec.HashToCurveG2FieldSetup.
Require Import Crypto.Util.Decidable.

Local Open Scope F_scope.

Lemma point_add_g2_preserves : forall P Q,
  on_curve_E2_opt P -> on_curve_E2_opt Q ->
  on_curve_E2_opt (point_add_g2 P Q).
Proof.
  intros [[x1 y1]|] [[x2 y2]|] HP HQ; try exact HP; try exact HQ.
  simpl in HP, HQ. unfold point_add_g2.
  destruct (fp2_eqb x1 x2) eqn:Hx.
  2: { (* General addition: x1 ≠ x2 *)
    apply fp2_eqb_false_iff in Hx.
    unfold on_curve_E2_opt, on_curve_E2, fp2_cube, bls12_b_g2 in *.
    unfold fp2_sqr in *.
    set (b := (F.of_Z p_pos 4, F.of_Z p_pos 4) : Fp2) in *.
    Field.fsatz. }
  (* Doubling: x1 = x2 *)
  apply fp2_eqb_true_iff in Hx. subst x2.
  destruct (fp2_eqb y1 (fp2_neg y2)) eqn:Hy.
  { exact I. }
  apply fp2_eqb_false_iff in Hy.
  unfold on_curve_E2_opt, on_curve_E2, fp2_cube, bls12_b_g2 in *.
  unfold fp2_sqr in *.
  set (b := (F.of_Z p_pos 4, F.of_Z p_pos 4) : Fp2) in *.
  assert (Hy1nz : y1 <> fp2_zero).
  { intro Hy0. apply Hy. subst y1.
    assert (fp2_mul y2 y2 = fp2_zero) by (rewrite HQ; rewrite <- HP; ring).
    assert (y2 = fp2_zero) by Field.fsatz. subst. ring. }
  clear HQ Hy y2.
  Field.fsatz.
Qed.

Lemma scalar_mul_g2_preserves : forall n P,
  on_curve_E2_opt P -> on_curve_E2_opt (scalar_mul_g2 n P).
Proof.
  induction n as [|n' IH]; intros P HP.
  - exact I.
  - simpl. apply point_add_g2_preserves; [exact HP|apply IH; exact HP].
Qed.

Theorem clear_cofactor_g2_preserves : forall P,
  on_curve_E2_opt P -> on_curve_E2_opt (clear_cofactor_g2 P).
Proof.
  intros. unfold clear_cofactor_g2. apply scalar_mul_g2_preserves. assumption.
Qed.
