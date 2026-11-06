(** * BLS12-381 final exponentiation: pure lemmas for the functional bedrock2 proofs.

    - The Frobenius constants loaded by the bedrock2 code (BLS12_FrobConstants.v:
      [BLS12_381_Frob.frob_*], Commitments' definitions) are the constants
      [gamma*_381], [c1*_381] of Frob381.v, by computation.
    - [cyc_frobenius_381]: the p-Frobenius with these constants preserves the
      cyclotomic subgroup.
    - [hard_chain] / [easy_chain]: the per-call feval equations of
      bls12_final_exp_hard_dsd / bls12_final_exp compose to
      [Pairing.final_exp_hard_dsd] / [Pairing.final_exponentiation_dsd].
    - [final_exponentiation_dsd_381_frob]: Pairing.final_exponentiation_dsd with the
      loaded constants = Pairing.final_exponentiation with the p^2 constants of
      Commitments (frob_gamma1_p2, frob_gamma2_p2, frob_coeff_fp12_p2_c1), for f
      invertible (f * fp12_inv f = 1).
*)

From Stdlib Require Import ZArith.ZArith.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Theory.BLS12Pairing.Pairing.
Require Import Theory.BLS12Pairing.Fp12Ring.
Require Import Theory.BLS12Pairing.Cyclotomic.
Require Import Theory.BLS12Pairing.Frobenius.
Require Import Theory.BLS12Pairing.Prime381.
Require Import Theory.BLS12Pairing.FinalExpFunctional.
Require Import Theory.BLS12Pairing.Frob381.
Require Import Theory.BLS12Pairing.CycExpModel.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_FrobConstants.
Module P := Theory.BLS12Pairing.Pairing.

Local Open Scope Z_scope.

Local Notation p := p381.
Local Notation Fp2 := ((F p381 * F p381)%type).
Local Notation Fp12 := ((Fp2 * Fp2 * Fp2 * (Fp2 * Fp2 * Fp2))%type).

(** ** The loaded constants are those of Frob381.v *)

Local Ltac fp2_vm :=
  apply BLS12_381_Frob.fp2_eq_by_to_Z; vm_compute; reflexivity.

Lemma frob_gamma1_381 : BLS12_381_Frob.frob_gamma1 = gamma1_381.
Proof. rewrite <- BLS12_381_Frob.gamma1_loaded_eq. fp2_vm. Qed.
Lemma frob_gamma2_381 : BLS12_381_Frob.frob_gamma2 = gamma2_381.
Proof. rewrite <- BLS12_381_Frob.gamma2_loaded_eq. fp2_vm. Qed.
Lemma frob_coeff_fp12_c1_381 : BLS12_381_Frob.frob_coeff_fp12_c1 = c1_381.
Proof. rewrite <- BLS12_381_Frob.w_frob_c1_loaded_eq. fp2_vm. Qed.
Lemma frob_gamma1_p2_381 : BLS12_381_Frob.frob_gamma1_p2 = gamma1_p2_381.
Proof. rewrite <- BLS12_381_Frob.gamma1_p2_loaded_eq. fp2_vm. Qed.
Lemma frob_gamma2_p2_381 : BLS12_381_Frob.frob_gamma2_p2 = gamma2_p2_381.
Proof. rewrite <- BLS12_381_Frob.gamma2_p2_loaded_eq. fp2_vm. Qed.
Lemma frob_coeff_fp12_p2_c1_381 : BLS12_381_Frob.frob_coeff_fp12_p2_c1 = c1_p2_381.
Proof. rewrite <- BLS12_381_Frob.w_frob_p2_c1_loaded_eq. fp2_vm. Qed.

(** ** Cyclotomic subgroup and the p-Frobenius *)

Lemma cyc_frobenius_381 : forall f : Fp12, cyclotomic f ->
  cyclotomic (P.fp12_frobenius p gamma1_381 gamma2_381 c1_381 f).
Proof. intros f Hf. rewrite frobenius_381_is_pow. apply cyc_pw, Hf. Qed.

(** ** The hard part: per-call equations -> Pairing.final_exp_hard_dsd *)

Section Chains.
  Variables (g1p2 g2p2 wp2 : Fp2).

  Lemma hard_chain (f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 : Fp12) :
    a1 = P.fp12_pow_bls_c_signed p f ->
    a2 = P.fp12_pow_bls_x_signed p a1 ->
    a3 = P.fp12_conjugate p a1 ->
    a4 = P.fp12_mul p a3 a2 ->
    a5 = P.fp12_pow_bls_x_signed p a4 ->
    a6 = P.fp12_frobenius p gamma1_381 gamma2_381 c1_381 a4 ->
    a7 = P.fp12_mul p a6 a5 ->
    a8 = P.fp12_pow_bls_x_signed p a7 ->
    a9 = P.fp12_pow_bls_x_signed p a8 ->
    a10 = P.fp12_frobenius_p2 p g1p2 g2p2 wp2 a7 ->
    a11 = P.fp12_conjugate p a7 ->
    a12 = P.fp12_mul p a11 a9 ->
    a13 = P.fp12_mul p a12 a10 ->
    a14 = P.fp12_mul p f a13 ->
    a14 = P.final_exp_hard_dsd p gamma1_381 gamma2_381 g1p2 g2p2 c1_381 wp2 f.
  Proof. intros; subst; reflexivity. Qed.

  (** The cyclotomic side conditions of the four cyc_exp calls after the first. *)
  Lemma hard_cyc (f a1 a2 a3 a4 a5 a6 a7 a8 : Fp12) : cyclotomic f ->
    a1 = P.fp12_pow_bls_c_signed p f ->
    a2 = P.fp12_pow_bls_x_signed p a1 ->
    a3 = P.fp12_conjugate p a1 ->
    a4 = P.fp12_mul p a3 a2 ->
    a5 = P.fp12_pow_bls_x_signed p a4 ->
    a6 = P.fp12_frobenius p gamma1_381 gamma2_381 c1_381 a4 ->
    a7 = P.fp12_mul p a6 a5 ->
    a8 = P.fp12_pow_bls_x_signed p a7 ->
    cyclotomic a1 /\ cyclotomic a4 /\ cyclotomic a7 /\ cyclotomic a8.
  Proof.
    intros Hf E1 E2 E3 E4 E5 E6 E7 E8.
    assert (C1 : cyclotomic a1) by (subst; apply cyc_pow_bls_c_signed, Hf).
    assert (C4 : cyclotomic a4).
    { rewrite E4, E3, E2. apply cyc_mul; [apply cyc_conj, C1 | apply cyc_pow_bls_x_signed, C1]. }
    assert (C7 : cyclotomic a7).
    { rewrite E7, E6, E5. apply cyc_mul; [apply cyc_frobenius_381, C4 | apply cyc_pow_bls_x_signed, C4]. }
    split; [exact C1 |]. split; [exact C4 |]. split; [exact C7 |].
    rewrite E8. apply cyc_pow_bls_x_signed, C7.
  Qed.

  (** The same side conditions one at a time (for use inside the WP proof). *)
  Lemma cyc_of_eq (x y : Fp12) : x = y -> cyclotomic y -> cyclotomic x.
  Proof. intros ->; trivial. Qed.

  Lemma cyc_step_cs (f a1 : Fp12) : cyclotomic f ->
    a1 = P.fp12_pow_bls_c_signed p f -> cyclotomic a1.
  Proof. intros Hf ->. apply cyc_pow_bls_c_signed, Hf. Qed.

  Lemma cyc_step_xs (a b : Fp12) : cyclotomic a ->
    b = P.fp12_pow_bls_x_signed p a -> cyclotomic b.
  Proof. intros Ha ->. apply cyc_pow_bls_x_signed, Ha. Qed.

  Lemma cyc_step_a4 (a1 a2 a3 a4 : Fp12) : cyclotomic a1 ->
    a2 = P.fp12_pow_bls_x_signed p a1 -> a3 = P.fp12_conjugate p a1 ->
    a4 = P.fp12_mul p a3 a2 -> cyclotomic a4.
  Proof.
    intros C1 -> -> ->. apply cyc_mul; [apply cyc_conj, C1 | apply cyc_pow_bls_x_signed, C1].
  Qed.

  Lemma cyc_step_a7 (a4 a5 a6 a7 : Fp12) : cyclotomic a4 ->
    a5 = P.fp12_pow_bls_x_signed p a4 ->
    a6 = P.fp12_frobenius p gamma1_381 gamma2_381 c1_381 a4 ->
    a7 = P.fp12_mul p a6 a5 -> cyclotomic a7.
  Proof.
    intros C4 -> -> ->. apply cyc_mul; [apply cyc_frobenius_381, C4 | apply cyc_pow_bls_x_signed, C4].
  Qed.

  (** The easy part, then the hard part. *)
  Lemma easy_chain (f b1 b2 b3 b4 b5 out : Fp12) :
    b1 = P.fp12_conjugate p f ->
    b2 = P.fp12_inv p f ->
    b3 = P.fp12_mul p b1 b2 ->
    b4 = P.fp12_frobenius_p2 p g1p2 g2p2 wp2 b3 ->
    b5 = P.fp12_mul p b4 b3 ->
    out = P.final_exp_hard_dsd p gamma1_381 gamma2_381 g1p2 g2p2 c1_381 wp2 b5 ->
    out = P.final_exponentiation_dsd p gamma1_381 gamma2_381 g1p2 g2p2 c1_381 wp2 f.
  Proof. intros; subst; reflexivity. Qed.
End Chains.

(** The easy part lands in the cyclotomic subgroup ([Frobenius.easy_part_cyclotomic]). *)
Lemma easy_cyc_381 (f b1 b2 b3 b4 b5 : Fp12) :
  P.fp12_mul p f (P.fp12_inv p f) = P.fp12_one p ->
  b1 = P.fp12_conjugate p f ->
  b2 = P.fp12_inv p f ->
  b3 = P.fp12_mul p b1 b2 ->
  b4 = P.fp12_frobenius_p2 p gamma1_p2_381 gamma2_p2_381 c1_p2_381 b3 ->
  b5 = P.fp12_mul p b4 b3 ->
  cyclotomic b5.
Proof.
  intros Hinv E1 E2 E3 E4 E5. subst.
  exact (easy_part_cyclotomic p381_prime p381_mod4 p381_mod3 _ _ _
           H381_gamma2_p2 H381_gamma1_p2 H381_c1_p2 f Hinv).
Qed.

(** The DSD final exponentiation with the loaded constants is Pairing.final_exponentiation
    with Commitments' p^2 constants. *)
Theorem final_exponentiation_dsd_381_frob : forall f : Fp12,
  P.fp12_mul p f (P.fp12_inv p f) = P.fp12_one p ->
  P.final_exponentiation_dsd p gamma1_381 gamma2_381 gamma1_p2_381 gamma2_p2_381 c1_381 c1_p2_381 f =
  P.final_exponentiation p BLS12_381_Frob.frob_gamma1_p2 BLS12_381_Frob.frob_gamma2_p2
    BLS12_381_Frob.frob_coeff_fp12_p2_c1 f.
Proof.
  intros f Hinv.
  rewrite frob_gamma1_p2_381, frob_gamma2_p2_381, frob_coeff_fp12_p2_c1_381.
  exact (final_exponentiation_dsd_381_correct f Hinv).
Qed.
