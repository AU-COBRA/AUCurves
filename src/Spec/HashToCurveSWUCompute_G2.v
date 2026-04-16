(** * Precomputed values for G2 SWU proof (native_compute).

    Isolated compilation unit for expensive Fp2 computations
    (norm + Legendre symbol). Pattern follows HashToCurveSWUCompute.v. *)

From Stdlib Require Import ZArith BinPos List Bool.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Spec.HashToCurve.
Require Import Spec.HashToCurveFieldSetup.
Require Import Spec.HashToCurveG2.
Require Import Spec.HashToCurveG2FieldSetup.

Local Open Scope F_scope.

(** Edge case: when x₁ = B/(Z·A), gx₁ is a quadratic residue in Fp2.
    This involves a Fp2 norm + a Legendre symbol with 380-bit exponent. *)
Lemma edge_case_gx1_is_square_g2 :
  fp2_is_square (curve_rhs2 iso_A_g2 iso_B_g2
    (fp2_div iso_B_g2 (fp2_mul swu_Z_g2 iso_A_g2))) = true.
Proof. native_compute. reflexivity. Qed.

(** -1 is non-square in Fp (Euler criterion: (-1)^((p-1)/2) ≠ 1). *)
Lemma neg_one_nonsquare : is_square (F.opp 1) = false.
Proof. native_compute. reflexivity. Qed.

(** F.opp 1 ≠ 0 in Fp. *)
Lemma opp_one_nonzero : F.opp (1 : Fp) <> 0.
Proof. intro H. apply (f_equal F.to_Z) in H. revert H. native_compute. discriminate. Qed.

(** 2 ≠ 0 in Fp. *)
Lemma two_nonzero : (F.of_Z p_pos 2 : Fp) <> 0.
Proof. intro H. apply (f_equal F.to_Z) in H. revert H. native_compute. discriminate. Qed.

(** swu_Z_g2 is non-square in Fp2. *)
Lemma swu_Z_g2_nonsquare : fp2_is_square swu_Z_g2 = false.
Proof. native_compute. reflexivity. Qed.

(** F.inv(0) = 0 in Fp. *)
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Lemma Fp_inv_0_precomputed : F.inv (0 : Fp) = 0.
Proof. apply F.eq_to_Z_iff. native_compute. reflexivity. Qed.
