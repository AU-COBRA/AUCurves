(** * Gallina models of the bedrock2 cyclotomic squaring and cyclotomic exponentiation.

    [cyc_sqr_model] is what [BLS12_Pairing.cyc_sqr_body] computes on (c0, c1):
      (1 + 2 v c1^2, 2 c0 c1)
    It equals the Fp12 square on the cyclotomic subgroup ([cyc_sqr_model_eq]).

    [cyc_exp_step]: one iteration of the square-and-multiply loop of
    [BLS12_Pairing.cyc_exp_neg_fn] (MSB first) moves the invariant
      result = pw B (e >> i)
    from i+1 to i.  [pow_bls_x_signed_pw] / [pow_bls_c_signed_pw] identify the
    conjugated result with the signed exponentiations of Pairing.v.
*)

From Stdlib Require Import ZArith NArith Lia.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Theory.BLS12Pairing.Pairing.
Require Import Theory.BLS12Pairing.Fp12Ring.
Require Import Theory.BLS12Pairing.Cyclotomic.
Module P := Theory.BLS12Pairing.Pairing.

Section CycExpModel.
  Context {p : positive}.

  Local Notation F := (F p).
  Local Notation Fp2 := (F * F)%type.
  Local Notation Fp6 := (Fp2 * Fp2 * Fp2)%type.
  Local Notation Fp12 := (Fp6 * Fp6)%type.

  Add Ring Fp_ring : (@Fp_ring_theory p).
  Add Ring fp2_ring : (@fp2_ring_theory p).
  Add Ring fp6_ring : (@fp6_ring_theory p).
  Add Ring fp12_ring : (@fp12_ring_theory p).

  Local Notation fp6_add := (P.fp6_add p).
  Local Notation fp6_mul := (P.fp6_mul p).
  Local Notation fp12_mul := (P.fp12_mul p).
  Local Notation fp12_one := (P.fp12_one p).
  Local Notation conj := (P.fp12_conjugate p).
  Local Notation pw := (@pw p).

  Definition cyc_sqr_model (f : Fp12) : Fp12 :=
    let c0 := fst f in let c1 := snd f in
    let t := P.fp6_mul_by_v p (fp6_mul c1 c1) in
    (fp6_add (fp6_add t t) (P.fp6_one p), fp6_add (fp6_mul c0 c1) (fp6_mul c0 c1)).

  Lemma cyc_sqr_model_eq : forall f, cyclotomic f -> cyc_sqr_model f = P.fp12_sqr p f.
  Proof.
    intros [c0 c1] H. cbv [cyclotomic] in H.
    apply (f_equal fst) in H.
    cbv [P.fp12_mul P.fp12_conjugate P.fp12_c0 P.fp12_c1 P.fp12_build P.fp12_one fst snd] in H.
    cbv [cyc_sqr_model P.fp12_sqr P.fp12_c0 P.fp12_c1 P.fp12_build fst snd].
    rewrite !fp6_sqr_eq. rewrite !fp6_mul_by_v_eq in *.
    f_equal.
    rewrite <- H. ring.
  Qed.

  Lemma cyc_sqr_model_pw : forall f n, cyclotomic f ->
    cyc_sqr_model (pw f n) = pw f (2 * n).
  Proof.
    intros f n Hf. rewrite cyc_sqr_model_eq by (apply cyc_pw; exact Hf).
    rewrite fp12_sqr_eq, <- pw_add. f_equal. lia.
  Qed.

  Lemma shiftr_step : forall (e : Z) (k : nat), (0 <= e)%Z ->
    Z.to_N (Z.shiftr e (Z.of_nat k)) =
    (2 * Z.to_N (Z.shiftr e (Z.of_nat (S k))) + (if Z.testbit e (Z.of_nat k) then 1 else 0))%N.
  Proof.
    intros e k He.
    rewrite Nat2Z.inj_succ, <- Z.add_1_r, <- Z.shiftr_shiftr by lia.
    set (s := Z.shiftr e (Z.of_nat k)).
    assert (Hs : (0 <= s)%Z) by (apply Z.shiftr_nonneg; exact He).
    rewrite (Z.div2_odd s) at 1.
    replace (Z.testbit e (Z.of_nat k)) with (Z.odd s)
      by (unfold s; rewrite <- Z.bit0_odd, Z.shiftr_spec by lia; f_equal; lia).
    rewrite <- Z.div2_spec.
    assert (H2 : (0 <= Z.div2 s)%Z) by (rewrite Z.div2_div; apply Z.div_pos; lia).
    destruct (Z.odd s); cbn [Z.b2z];
      rewrite Z2N.inj_add, Z2N.inj_mul by lia; reflexivity.
  Qed.

  (** One loop iteration: square (cyclotomic), then multiply by the base if the bit is set. *)
  Lemma cyc_exp_step : forall B (e : Z) (k : nat), (0 <= e)%Z -> cyclotomic B ->
    (if Z.testbit e (Z.of_nat k)
     then fp12_mul (cyc_sqr_model (pw B (Z.to_N (Z.shiftr e (Z.of_nat (S k)))))) B
     else cyc_sqr_model (pw B (Z.to_N (Z.shiftr e (Z.of_nat (S k))))))
    = pw B (Z.to_N (Z.shiftr e (Z.of_nat k))).
  Proof.
    intros B e k He HB.
    rewrite (shiftr_step e k He), cyc_sqr_model_pw by exact HB.
    destruct (Z.testbit e (Z.of_nat k)).
    - rewrite pw_add, pw_1. reflexivity.
    - rewrite N.add_0_r. reflexivity.
  Qed.

  Lemma cyc_exp_init : forall B (e : Z) (w : nat), (0 <= e < 2 ^ Z.of_nat w)%Z ->
    pw B (Z.to_N (Z.shiftr e (Z.of_nat w))) = fp12_one.
  Proof.
    intros B e w He.
    rewrite Z.shiftr_div_pow2 by lia.
    rewrite Z.div_small by lia. reflexivity.
  Qed.

  Lemma cyc_exp_final : forall B (e : Z),
    pw B (Z.to_N (Z.shiftr e (Z.of_nat 0))) = pw B (Z.to_N e).
  Proof. intros. rewrite Z.shiftr_0_r. reflexivity. Qed.

  (** The signed exponentiations of Pairing.v. *)
  Lemma pow_bls_x_signed_pw : forall f,
    P.fp12_pow_bls_x_signed p f = conj (pw f (Z.to_N P.bls_x)).
  Proof.
    intros f. cbv [P.fp12_pow_bls_x_signed P.fp12_pow_bls_x].
    rewrite fp12_pow_Z_pw; [reflexivity |]. cbv. split; congruence.
  Qed.

  Lemma pow_bls_c_signed_pw : forall f,
    P.fp12_pow_bls_c_signed p f = conj (pw f (Z.to_N P.bls_c)).
  Proof.
    intros f. cbv [P.fp12_pow_bls_c_signed P.fp12_pow_bls_c].
    rewrite fp12_pow_Z_pw; [reflexivity |]. cbv. split; congruence.
  Qed.

  Lemma cyc_pow_bls_x_signed : forall f, cyclotomic f ->
    cyclotomic (P.fp12_pow_bls_x_signed p f).
  Proof. intros f Hf. rewrite pow_bls_x_signed_pw. apply cyc_conj, cyc_pw, Hf. Qed.

  Lemma cyc_pow_bls_c_signed : forall f, cyclotomic f ->
    cyclotomic (P.fp12_pow_bls_c_signed p f).
  Proof. intros f Hf. rewrite pow_bls_c_signed_pw. apply cyc_conj, cyc_pw, Hf. Qed.

End CycExpModel.
