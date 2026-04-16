(** Precompute the sentinel y-coordinate for the G2 isogeny kernel case. *)
From Stdlib Require Import ZArith.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Spec.HashToCurve.
Require Import Spec.HashToCurveG2.

Definition sentinel_y_re : Z := Eval native_compute in (F.to_Z (fst sentinel_y_g2)).
Definition sentinel_y_im : Z := Eval native_compute in (F.to_Z (snd sentinel_y_g2)).

Lemma sentinel_y_eq : sentinel_y_g2 = (F.of_Z p_pos sentinel_y_re, F.of_Z p_pos sentinel_y_im).
Proof. apply injective_projections; apply F.eq_to_Z_iff; vm_compute; reflexivity. Qed.

Lemma sentinel_on_curve_E2 : on_curve_E2 (sentinel_x_g2, sentinel_y_g2).
Proof.
  rewrite sentinel_y_eq.
  unfold on_curve_E2, sentinel_x_g2, fp2_sqr, fp2_cube, bls12_b_g2, fp2_add, fp2_mul.
  simpl fst; simpl snd.
  apply injective_projections; apply F.eq_to_Z_iff; vm_compute; reflexivity.
Qed.
