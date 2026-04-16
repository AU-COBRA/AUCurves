(** * Precomputed values for SWU proof (native_compute).

    Isolated compilation unit for expensive computations.
    Follows the project pattern of bls12_cert_native.v. *)

From Stdlib Require Import ZArith BinPos List Bool.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Spec.HashToCurve.
Require Import Spec.HashToCurveFieldSetup.

Local Open Scope F_scope.

(** Edge case: when x₁ = B/(Z·A), gx₁ is a quadratic residue.
    This involves computing F.pow with a 380-bit exponent. *)
Lemma edge_case_gx1_is_square :
  is_square (curve_rhs iso_A iso_B (iso_B * F.inv (swu_Z * iso_A))) = true.
Proof. native_compute. reflexivity. Qed.

(** Isogeny denominators don't vanish at the edge-case x-coordinate B/(Z*A). *)
Lemma edge_xden_nonzero :
  fp_eqb (horner_eval_monic iso_xden (iso_B * F.inv (swu_Z * iso_A))) 0 = false.
Proof. native_compute. reflexivity. Qed.

Lemma edge_yden_nonzero :
  fp_eqb (horner_eval_monic iso_yden (iso_B * F.inv (swu_Z * iso_A))) 0 = false.
Proof. native_compute. reflexivity. Qed.
