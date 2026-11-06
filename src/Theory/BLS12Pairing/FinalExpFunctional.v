(** * Functional correctness of the DSD hard part of the final exponentiation.

    For BLS12-381 (p = [FinalExpEquiv.bls_p]) and Frobenius constants of
    Pairing.v satisfying the hypotheses of [Frobenius.v]:

    - [final_exp_hard_dsd_correct]: the Gallina hard part [final_exp_hard_dsd]
      (exponentiations by -c and -|x| on the cyclotomic subgroup, two Frobenius
      maps) equals [fp12_pow_Z f h3_exp h3_width] for f in the cyclotomic subgroup;
    - [final_exponentiation_dsd_correct]: [final_exponentiation_dsd f =
      final_exponentiation f] for every f with [f * fp12_inv f = 1]
      (every nonzero f once Fp12 is known to be a field).

    The exponent bookkeeping uses [Cyclotomic.zpow]; the integer identity is
    [FinalExpEquiv.h3_exact_chain_c].
*)

From Stdlib Require Import ZArith NArith BinPos List Lia Znumtheory.
Import ListNotations.
Require Import Crypto.Spec.ModularArithmetic.
Require Theory.BLS12Pairing.Pairing.
Require Theory.BLS12Pairing.FinalExpEquiv.
Require Import Theory.BLS12Pairing.Fp12Ring.
Require Import Theory.BLS12Pairing.Cyclotomic.
Require Import Theory.BLS12Pairing.Frobenius.
Require Import Theory.BLS12Pairing.Prime381.
Module P := Theory.BLS12Pairing.Pairing.
Module FE := Theory.BLS12Pairing.FinalExpEquiv.

(** [pw] iterates multiplication: never let conversion unfold it on a 381-bit exponent. *)
Local Opaque Fp12Ring.pw.

Section HardPart.
  Local Notation p := p381.
  Local Notation F := (F p).
  Local Notation Fp2 := (F * F)%type.
  Local Notation Fp6 := (Fp2 * Fp2 * Fp2)%type.
  Local Notation Fp12 := (Fp6 * Fp6)%type.
  Local Notation fp12_mul := (P.fp12_mul p).
  Local Notation fp12_one := (P.fp12_one p).
  Local Notation conj := (P.fp12_conjugate p).
  Local Notation pw := (@pw p).
  Local Notation zpow := (@zpow p).
  Local Notation cyclotomic := (@cyclotomic p).

  (** Frobenius constants and what is assumed about them (xi = 1 + u;
      powers computed in Fp12 on the embedded xi). *)
  Variables gamma1 gamma2 gamma1_p2 gamma2_p2 c1 c1_p2 : Fp2.
  Hypothesis Hgamma2 : gamma2 = P.fp2_mul p gamma1 gamma1.
  Hypothesis Hgamma1 : pw (e212 xi2) (Z.to_N ((Z.pos p - 1) / 3)) = e212 gamma1.
  Hypothesis Hc1 : pw (e212 xi2) (Z.to_N ((Z.pos p - 1) / 6)) = e212 c1.
  Hypothesis Hgamma2_p2 : gamma2_p2 = P.fp2_mul p gamma1_p2 gamma1_p2.
  Hypothesis Hgamma1_p2 : pw (e212 xi2) (Z.to_N ((Z.pos p * Z.pos p - 1) / 3)) = e212 gamma1_p2.
  Hypothesis Hc1_p2 : pw (e212 xi2) (Z.to_N ((Z.pos p * Z.pos p - 1) / 6)) = e212 c1_p2.

  Local Notation frob := (P.fp12_frobenius p gamma1 gamma2 c1).
  Local Notation frob2 := (P.fp12_frobenius_p2 p gamma1_p2 gamma2_p2 c1_p2).

  Lemma frob_zpow : forall f, cyclotomic f -> frob f = zpow f (Z.pos p).
  Proof.
    intros f Hf.
    rewrite (frobenius_is_pow p381_prime p381_mod4 p381_mod3 gamma1 gamma2 c1 Hgamma2 Hgamma1 Hc1).
    unfold Cyclotomic.zpow. reflexivity.
  Qed.

  Lemma frob2_zpow : forall f, cyclotomic f -> frob2 f = zpow f (Z.pos p * Z.pos p).
  Proof.
    intros f Hf.
    rewrite (frobenius_p2_is_pow p381_prime p381_mod4 p381_mod3
               gamma1_p2 gamma2_p2 c1_p2 Hgamma2_p2 Hgamma1_p2 Hc1_p2).
    change (Z.pos p * Z.pos p)%Z with (Z.pos (p * p)).
    unfold Cyclotomic.zpow. reflexivity.
  Qed.

  (** Exponent tracking: each step maps [zpow f a] to [zpow f (g a)]. *)
  Section Track.
    Variable f : Fp12.
    Hypothesis Hf : cyclotomic f.

    Lemma tr_base : f = zpow f 1.
    Proof. rewrite zpow_1; reflexivity. Qed.

    Lemma tr_mul : forall X Y a b, X = zpow f a -> Y = zpow f b -> fp12_mul X Y = zpow f (a + b).
    Proof. intros X Y a b -> ->; rewrite zpow_add by assumption; reflexivity. Qed.

    Lemma tr_conj : forall X a, X = zpow f a -> conj X = zpow f (- a).
    Proof. intros X a ->; apply zpow_opp. Qed.

    Lemma tr_sx : forall X a, X = zpow f a -> P.fp12_pow_bls_x_signed p X = zpow f (a * - P.bls_x).
    Proof.
      intros X a ->. rewrite pow_bls_x_signed_zpow by (apply cyc_zpow; assumption).
      rewrite (zpow_mul f a) by assumption. reflexivity.
    Qed.

    Lemma tr_sc : forall X a, X = zpow f a -> P.fp12_pow_bls_c_signed p X = zpow f (a * - P.bls_c).
    Proof.
      intros X a ->. rewrite pow_bls_c_signed_zpow by (apply cyc_zpow; assumption).
      rewrite (zpow_mul f a) by assumption. reflexivity.
    Qed.

    Lemma tr_frob : forall X a, X = zpow f a -> frob X = zpow f (a * Z.pos p).
    Proof.
      intros X a ->. rewrite frob_zpow by (apply cyc_zpow; assumption).
      rewrite (zpow_mul f a) by assumption. reflexivity.
    Qed.

    Lemma tr_frob2 : forall X a, X = zpow f a -> frob2 X = zpow f (a * (Z.pos p * Z.pos p)).
    Proof.
      intros X a ->. rewrite frob2_zpow by (apply cyc_zpow; assumption).
      rewrite (zpow_mul f a) by assumption. reflexivity.
    Qed.
  End Track.

  (** Syntactic dispatch: no unification below the head symbol (the
      operations unfold to 381-bit field arithmetic). *)
  Ltac track f Hf :=
    lazymatch goal with
    | |- P.fp12_mul _ _ _ = _ => refine (tr_mul f Hf _ _ _ _ _ _); [track f Hf | track f Hf]
    | |- P.fp12_conjugate _ _ = _ => refine (tr_conj f _ _ _); track f Hf
    | |- P.fp12_pow_bls_x_signed _ _ = _ => refine (tr_sx f Hf _ _ _); track f Hf
    | |- P.fp12_pow_bls_c_signed _ _ = _ => refine (tr_sc f Hf _ _ _); track f Hf
    | |- P.fp12_frobenius _ _ _ _ _ = _ => refine (tr_frob f Hf _ _ _); track f Hf
    | |- P.fp12_frobenius_p2 _ _ _ _ _ = _ => refine (tr_frob2 f Hf _ _ _); track f Hf
    | |- ?x = _ => constr_eq x f; exact (tr_base f)
    end.

  (** The integer identity behind the chain, from [FinalExpEquiv.h3_exact_chain_c]. *)
  Lemma h3_exp_eq :
    P.h3_exp = (1 + (P.bls_x ^ 2 - 1 + Z.pos p ^ 2) * (P.bls_x + 1) * P.bls_c
                    * (Z.pos p - P.bls_x))%Z.
  Proof.
    pose proof FE.h3_exact_chain_c as H. cbv zeta in H.
    rewrite p381_eq.
    change P.h3_exp with FE.h3_exp. change P.bls_x with FE.bls_x_abs. change P.bls_c with FE.bls_c.
    exact H.
  Qed.

  Lemma h3_bounds : (0 <= P.h3_exp < 2 ^ Z.of_nat P.h3_width)%Z.
  Proof. vm_compute. split; congruence. Qed.

  Theorem final_exp_hard_dsd_correct : forall f, cyclotomic f ->
    P.final_exp_hard_dsd p gamma1 gamma2 gamma1_p2 gamma2_p2 c1 c1_p2 f =
    P.fp12_pow_Z p f P.h3_exp P.h3_width.
  Proof.
    intros f Hf.
    rewrite fp12_pow_Z_pw by exact h3_bounds.
    rewrite <- zpow_of_N, Z2N.id by (pose proof h3_bounds; lia).
    cbv beta zeta delta [P.final_exp_hard_dsd].
    etransitivity; [track f Hf|].
    apply (f_equal (zpow f)). rewrite h3_exp_eq. ring.
  Qed.

  (** The whole final exponentiation. *)
  Theorem final_exponentiation_dsd_correct : forall f,
    fp12_mul f (P.fp12_inv p f) = fp12_one ->
    P.final_exponentiation_dsd p gamma1 gamma2 gamma1_p2 gamma2_p2 c1 c1_p2 f =
    P.final_exponentiation p gamma1_p2 gamma2_p2 c1_p2 f.
  Proof.
    intros f Hf.
    pose proof (easy_part_cyclotomic p381_prime p381_mod4 p381_mod3
                  gamma1_p2 gamma2_p2 c1_p2 Hgamma2_p2 Hgamma1_p2 Hc1_p2 f Hf) as He.
    cbv beta zeta delta [P.final_exponentiation_dsd P.final_exponentiation].
    apply final_exp_hard_dsd_correct. exact He.
  Qed.

  (** The hard part as the cyclotomic power f^h3. *)
  Corollary final_exp_hard_dsd_pw : forall f, cyclotomic f ->
    P.final_exp_hard_dsd p gamma1 gamma2 gamma1_p2 gamma2_p2 c1 c1_p2 f = pw f (Z.to_N P.h3_exp).
  Proof.
    intros f Hf. rewrite final_exp_hard_dsd_correct by assumption.
    apply fp12_pow_Z_pw, h3_bounds.
  Qed.

End HardPart.
