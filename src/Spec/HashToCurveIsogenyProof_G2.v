(** * G2 3-isogeny correctness proof.

    Proves [iso_map_g2] maps E2' points to E2 points.
    - Kernel case: sentinel verified via precomputed values.
    - Normal case: polynomial identity verified at Fp2 level using
      polynomial homomorphism (HashToCurveIsogenyBridge_G2). *)

From Stdlib Require Import ZArith Lia Ring List.
Import ListNotations.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Algebra.Hierarchy.
Require Import Spec.HashToCurve.
Require Import Spec.HashToCurveG2.
Require Import Spec.HashToCurveFieldSetup.
Require Import Spec.HashToCurveG2FieldSetup.
Require Import Spec.HashToCurveG2SentinelCompute.
Require Import Spec.HashToCurveIsogenyBridge_G2.
Require Import Crypto.Util.Decidable.

Local Open Scope F_scope.

(** Curve E2' as a polynomial in x' (degree 3). *)
Definition curve_eprime_poly_fp2 : list Fp2 :=
  [iso_B_g2; iso_A_g2; fp2_zero; fp2_one].

Lemma curve_eprime_eval : forall x' : Fp2,
  horner_eval_fp2 curve_eprime_poly_fp2 x' =
  fp2_add (fp2_add (fp2_cube x') (fp2_mul iso_A_g2 x')) iso_B_g2.
Proof.
  intro x'. unfold curve_eprime_poly_fp2, horner_eval_fp2, fp2_cube, fp2_sqr.
  fold horner_eval_fp2.
  apply injective_projections; simpl; ring.
Qed.

(** LHS and RHS of the isogeny identity expressed as Fp2 polynomial coefficient lists. *)
Definition lhs_poly_fp2 : list Fp2 :=
  poly_mul_fp2 (poly_mul_fp2 curve_eprime_poly_fp2
                              (poly_sqr_fp2 iso_ynum_g2))
               (poly_cube_fp2 (iso_xden_g2 ++ [fp2_one])).

Definition rhs_poly_fp2 : list Fp2 :=
  poly_add_fp2
    (poly_mul_fp2 (poly_cube_fp2 iso_xnum_g2)
                  (poly_sqr_fp2 (iso_yden_g2 ++ [fp2_one])))
    (poly_mul_fp2 (poly_scale_fp2 bls12_b_g2 (poly_cube_fp2 (iso_xden_g2 ++ [fp2_one])))
                  (poly_sqr_fp2 (iso_yden_g2 ++ [fp2_one]))).

(** The polynomial identity at the Fp2 coefficient level.
    Proved by projecting to Z×Z and verifying via vm_compute. *)
Lemma lhs_rhs_poly_eq : lhs_poly_fp2 = rhs_poly_fp2.
Proof.
  apply fp2_list_eq_via_zp2.
  vm_compute. reflexivity.
Qed.

(** The isogeny polynomial identity at the Fp2 level. *)
Lemma isogeny_identity_Fp2 : forall x' : Fp2,
  let xn := horner_eval_fp2 iso_xnum_g2 x' in
  let xd := horner_eval_monic_fp2 iso_xden_g2 x' in
  let yn := horner_eval_fp2 iso_ynum_g2 x' in
  let yd := horner_eval_monic_fp2 iso_yden_g2 x' in
  fp2_mul (fp2_mul (fp2_add (fp2_add (fp2_cube x') (fp2_mul iso_A_g2 x')) iso_B_g2)
                    (fp2_mul yn yn))
          (fp2_mul (fp2_mul xd xd) xd)
  =
  fp2_add
    (fp2_mul (fp2_mul (fp2_mul xn xn) xn) (fp2_mul yd yd))
    (fp2_mul bls12_b_g2 (fp2_mul (fp2_mul (fp2_mul xd xd) xd) (fp2_mul yd yd))).
Proof.
  intro x'. cbv zeta.
  rewrite <- (curve_eprime_eval x').
  unfold horner_eval_monic_fp2.
  (* Express LHS as horner_eval lhs_poly_fp2; ditto for RHS, modulo
     associativity which we fix with ring afterward. *)
  set (xn := horner_eval_fp2 iso_xnum_g2 x').
  set (xd := horner_eval_fp2 (iso_xden_g2 ++ [fp2_one]) x').
  set (yn := horner_eval_fp2 iso_ynum_g2 x').
  set (yd := horner_eval_fp2 (iso_yden_g2 ++ [fp2_one]) x').
  set (cep := horner_eval_fp2 curve_eprime_poly_fp2 x').
  assert (HLHS : horner_eval_fp2 lhs_poly_fp2 x' =
                 fp2_mul (fp2_mul cep (fp2_mul yn yn))
                         (fp2_mul (fp2_mul xd xd) xd)).
  { unfold lhs_poly_fp2.
    rewrite horner_eval_fp2_mul, horner_eval_fp2_mul,
            horner_eval_fp2_sqr, horner_eval_fp2_cube.
    fold cep yn xd. reflexivity. }
  assert (HRHS : horner_eval_fp2 rhs_poly_fp2 x' =
                 fp2_add (fp2_mul (fp2_mul (fp2_mul xn xn) xn) (fp2_mul yd yd))
                         (fp2_mul (fp2_mul bls12_b_g2 (fp2_mul (fp2_mul xd xd) xd))
                                  (fp2_mul yd yd))).
  { unfold rhs_poly_fp2.
    rewrite horner_eval_fp2_add, horner_eval_fp2_mul,
            horner_eval_fp2_cube, horner_eval_fp2_sqr,
            horner_eval_fp2_mul, horner_eval_fp2_scale,
            horner_eval_fp2_cube, horner_eval_fp2_sqr.
    fold xn xd yd. reflexivity. }
  (* The goal differs from HRHS only by associativity of bls12_b * xd³ * yd² *)
  rewrite <- HLHS.
  rewrite lhs_rhs_poly_eq, HRHS.
  set (b := bls12_b_g2). clearbody xn xd yn yd cep b.
  (* Goal: ... = ... bls12_b * (xd³ * yd²) ...; HRHS form has (bls12_b * xd³) * yd² *)
  apply injective_projections; simpl; ring.
Qed.

(** The isogeny maps E2' points to E2 points. *)
Theorem iso_map_g2_on_curve : forall (pt : Fp2 * Fp2),
  on_curve_E2prime pt ->
  on_curve_E2 (iso_map_g2 pt).
Proof.
  intros [x' y'] Hcurve.
  unfold on_curve_E2prime in Hcurve.
  unfold on_curve_E2, iso_map_g2.
  set (xn := horner_eval_fp2 iso_xnum_g2 x').
  set (xd := horner_eval_monic_fp2 iso_xden_g2 x').
  set (yn := horner_eval_fp2 iso_ynum_g2 x').
  set (yd := horner_eval_monic_fp2 iso_yden_g2 x').
  set (z := fp2_mul xd yd).
  destruct (fp2_eqb z fp2_zero) eqn:Hz.
  - exact sentinel_on_curve_E2.
  - apply fp2_eqb_false_iff in Hz.
    assert (Hxd : xd <> fp2_zero)
      by (intro H; apply Hz; subst z; rewrite H; ring).
    assert (Hyd : yd <> fp2_zero)
      by (intro H; apply Hz; subst z; rewrite H; ring).
    pose proof (isogeny_identity_Fp2 x') as Hident.
    cbv zeta in Hident. fold xn xd yn yd in Hident.
    unfold fp2_sqr, fp2_cube in *.
    rewrite <- Hcurve in Hident.
    set (b := bls12_b_g2) in *.
    subst z. clearbody xn xd yn yd b. clear Hcurve x'.
    unfold fp2_sqr in *.
    Field.fsatz.
Qed.
