(** * point_add and clear_cofactor preserve on_curve_E.

    Proved algebraically using Field.fsatz for both addition cases.
    Key insight: of_Z 2 and of_Z 3 must be rewritten to 1+1 and 1+1+1
    for the ring solver to handle the doubling formula. *)

From Stdlib Require Import ZArith Lia.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Algebra.Hierarchy.
Require Import Spec.HashToCurve.
Require Import Spec.HashToCurveFieldSetup.
Require Import Spec.HashToCurveSWUProof.
Require Import Crypto.Util.Decidable.

Local Open Scope F_scope.
Local Notation of_Z := (F.of_Z p_pos).

(** Field instance for Fp. *)
#[local] Instance Fp_field : @Algebra.Hierarchy.field Fp Logic.eq 0f 1f
  F.opp F.add F.sub F.mul F.inv F.div
  := @PrimeFieldTheorems.F.field_modulo p_pos p_pos_prime.

#[local] Instance Fp_eq_dec : Decidable.DecidableRel (@Logic.eq Fp) := F.eq_dec.

(** Rewrite lemmas: make 2 and 3 transparent to the ring solver. *)
Local Lemma of_Z_2 : of_Z 2 = (1f +f 1f).
Proof. apply F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

Local Lemma of_Z_3 : of_Z 3 = (1f +f 1f +f 1f).
Proof. apply F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

(** on_curve predicate for affine_point = option (Fp * Fp). *)
Definition on_curve_E_opt (P : affine_point) : Prop :=
  match P with
  | None => True
  | Some pt => on_curve_E pt
  end.

(** Closure of point_add: proved by Field.fsatz in each case. *)
Lemma point_add_preserves : forall P Q,
  on_curve_E_opt P -> on_curve_E_opt Q ->
  on_curve_E_opt (point_add P Q).
Proof.
  intros [[x1 y1]|] [[x2 y2]|] HP HQ; try exact HP; try exact HQ.
  simpl in HP, HQ. unfold point_add.
  destruct (fp_eqb x1 x2) eqn:Hx.
  - (* x1 = x2 *)
    apply fp_eqb_true_iff in Hx. subst x2.
    destruct (fp_eqb y1 (-f y2)) eqn:Hy.
    + (* P + (-P) = O *) exact I.
    + (* Doubling case *)
      apply fp_eqb_false_iff in Hy.
      unfold on_curve_E_opt, on_curve_E, sqr, cube, bls12_b in *.
      assert (Hy1nz : y1 <> 0f).
      { intro Hy0. apply Hy. subst y1.
        assert (y2 *f y2 = 0f) by (rewrite HQ; rewrite <- HP; ring).
        assert (y2 = 0f) by Field.fsatz. subst. ring. }
      rewrite of_Z_2, of_Z_3.
      set (b := of_Z 4) in *.
      clear HQ Hy y2. Field.fsatz.
  - (* x1 ≠ x2: general addition *)
    apply fp_eqb_false_iff in Hx.
    unfold on_curve_E_opt, on_curve_E, sqr, cube, bls12_b in *.
    set (b := of_Z 4) in *.
    Field.fsatz.
Qed.

Lemma scalar_mul_preserves : forall n P,
  on_curve_E_opt P -> on_curve_E_opt (scalar_mul n P).
Proof.
  induction n as [|n' IH]; intros P HP.
  - exact I.
  - simpl. apply point_add_preserves; [exact HP|apply IH; exact HP].
Qed.

Theorem clear_cofactor_preserves : forall P,
  on_curve_E_opt P -> on_curve_E_opt (clear_cofactor P).
Proof.
  intros. unfold clear_cofactor. apply scalar_mul_preserves. assumption.
Qed.
