(** * The cyclotomic subgroup {f | f * conj f = 1} of Fp12 (Pairing.v tower).

    - closure under [fp12_mul], [fp12_conjugate], [fp12_sqr], powers;
    - on it the conjugate is the inverse ([fp12_inv], for prime p);
    - integer powers [zpow] (negative exponents through the conjugate) and
      their laws [zpow_add], [zpow_mul], [zpow_opp];
    - the signed exponentiations of Pairing.v by |x| and c as [zpow].
*)

From Stdlib Require Import ZArith NArith BinPos List Lia Znumtheory.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Algebra.Field.
Require Theory.BLS12Pairing.Pairing.
Require Import Theory.BLS12Pairing.Fp12Ring.
Module P := Theory.BLS12Pairing.Pairing.

Section Cyclotomic.
  Context {p : positive}.

  Local Notation F := (F p).
  Local Notation Fp2 := (F * F)%type.
  Local Notation Fp6 := (Fp2 * Fp2 * Fp2)%type.
  Local Notation Fp12 := (Fp6 * Fp6)%type.

  Add Ring Fp_ring : (@Fp_ring_theory p).
  Add Ring fp2_ring : (@fp2_ring_theory p).
  Add Ring fp6_ring : (@fp6_ring_theory p).
  Add Ring fp12_ring : (@fp12_ring_theory p).

  Local Notation fp12_mul := (P.fp12_mul p).
  Local Notation fp12_one := (P.fp12_one p).
  Local Notation conj := (P.fp12_conjugate p).
  Local Notation pw := (@pw p).

  Definition cyclotomic (f : Fp12) : Prop := fp12_mul f (conj f) = fp12_one.

  Lemma cyc_one : cyclotomic fp12_one.
  Proof. cbv [cyclotomic]. rewrite conj_one. ring. Qed.

  Lemma cyc_mul : forall f g, cyclotomic f -> cyclotomic g -> cyclotomic (fp12_mul f g).
  Proof.
    cbv [cyclotomic]; intros f g Hf Hg. rewrite conj_mul.
    transitivity (fp12_mul (fp12_mul f (conj f)) (fp12_mul g (conj g))); [ring|].
    rewrite Hf, Hg; ring.
  Qed.

  Lemma cyc_conj : forall f, cyclotomic f -> cyclotomic (conj f).
  Proof. cbv [cyclotomic]; intros f Hf. rewrite conj_conj, <- Hf. ring. Qed.

  Lemma cyc_sqr : forall f, cyclotomic f -> cyclotomic (P.fp12_sqr p f).
  Proof. intros; rewrite fp12_sqr_eq; apply cyc_mul; assumption. Qed.

  Lemma cyc_pw : forall f n, cyclotomic f -> cyclotomic (pw f n).
  Proof.
    intros f n Hf; induction n using N.peano_ind; [apply cyc_one|].
    rewrite pw_succ; apply cyc_mul; assumption.
  Qed.

  Lemma cyc_conj_mul_l : forall f, cyclotomic f -> fp12_mul (conj f) f = fp12_one.
  Proof. cbv [cyclotomic]; intros f Hf; rewrite <- Hf; ring. Qed.

  Lemma F_one_neq_zero : prime p -> @F.one p <> F.zero.
  Proof.
    intros Hp H. pose proof (prime_ge_2 _ Hp).
    apply (f_equal F.to_Z) in H. cbv [F.one F.zero] in H.
    rewrite !F.to_Z_of_Z, !Z.mod_small in H by lia. discriminate.
  Qed.

  Lemma F_inv_one : prime p -> @F.one p = F.inv F.one.
  Proof.
    intros Hp. pose proof (@F.inv_nonzero p Hp F.one (F_one_neq_zero Hp)) as H.
    transitivity (F.mul (F.inv F.one) (@F.one p)); [symmetry; exact H | ring].
  Qed.

  (** On the cyclotomic subgroup the conjugate is the inverse. *)
  Lemma fp12_mul_conj_shape : forall a0 a1 : Fp6,
    fp12_mul (a0, a1) (conj (a0, a1)) =
    (P.fp6_sub p (P.fp6_mul p a0 a0) (P.fp6_mul_by_v p (P.fp6_mul p a1 a1)), P.fp6_zero p).
  Proof.
    intros. cbv [P.fp12_mul P.fp12_conjugate P.fp12_build P.fp12_c0 P.fp12_c1 fst snd].
    rewrite !fp6_mul_by_v_eq.
    apply injective_projections; cbn [fst snd]; ring.
  Qed.

  Lemma conj_is_inv : prime p -> forall f, cyclotomic f -> conj f = P.fp12_inv p f.
  Proof.
    intros Hp [a0 a1] Hf. cbv [cyclotomic] in Hf.
    rewrite fp12_mul_conj_shape in Hf.
    apply (f_equal fst) in Hf; cbn [fst] in Hf.
    change (fst (P.fp12_one p)) with (P.fp6_one p) in Hf.
    cbv [P.fp12_inv P.fp12_build P.fp12_c0 P.fp12_c1 fst snd].
    rewrite !fp6_sqr_eq, Hf.
    replace (P.fp6_inv p (P.fp6_one p)) with (P.fp6_one p).
    - cbv [P.fp12_conjugate P.fp12_build P.fp12_c0 P.fp12_c1 fst snd].
      apply injective_projections; cbn [fst snd]; ring.
    - cbv [P.fp6_inv P.fp6_one P.fp6_build P.fp6_c0 P.fp6_c1 P.fp6_c2 fst snd].
      rewrite !fp2_mul_xi_eq, !fp2_sqr_eq.
      cbv [P.fp2_inv P.fp2_one P.fp2_zero P.fp2_mul P.fp2_add P.fp2_sub xi2 fst snd].
      assert (Hinv : forall x, x = @F.one p -> F.inv x = F.one)
        by (intros x ->; symmetry; apply F_inv_one; assumption).
      match goal with |- context [F.inv ?x] => rewrite (Hinv x) by ring end.
      apply injective_projections; cbn [fst snd]; [apply injective_projections; cbn [fst snd]|];
        apply injective_projections; cbn [fst snd]; ring.
  Qed.

  (* ================================================================ *)
  (** ** Integer powers on the cyclotomic subgroup                     *)
  (* ================================================================ *)

  (** [zpow f z] is f^z, with f^(-n) = conj (f^n) (the inverse on the subgroup). *)
  Definition zpow (f : Fp12) (z : Z) : Fp12 :=
    match z with
    | Z0 => fp12_one
    | Zpos n => pw f (Npos n)
    | Zneg n => conj (pw f (Npos n))
    end.

  Lemma zpow_of_N : forall f n, zpow f (Z.of_N n) = pw f n.
  Proof. intros f [|n]; reflexivity. Qed.

  Lemma zpow_split : forall f z,
    zpow f z = fp12_mul (pw f (Z.to_N z)) (conj (pw f (Z.to_N (- z)))).
  Proof.
    intros f [|n|n]; cbn [zpow Z.to_N Z.opp]; rewrite ?pw_0, ?conj_one; ring.
  Qed.

  Lemma pw_conj_diff : forall f n m, cyclotomic f ->
    fp12_mul (pw f n) (conj (pw f m)) = zpow f (Z.of_N n - Z.of_N m).
  Proof.
    intros f n m Hf.
    destruct (N.le_gt_cases m n) as [Hle|Hlt].
    - replace n with ((n - m) + m)%N by lia.
      replace (Z.of_N (n - m + m) - Z.of_N m)%Z with (Z.of_N (n - m)) by lia.
      rewrite zpow_of_N, pw_add.
      pose proof (cyc_pw f m Hf) as Hm. cbv [cyclotomic] in Hm.
      transitivity (fp12_mul (pw f (n - m)) (fp12_mul (pw f m) (conj (pw f m)))); [ring|].
      rewrite Hm; ring.
    - replace m with (n + (m - n))%N by lia.
      replace (Z.of_N n - Z.of_N (n + (m - n)))%Z with (- Z.of_N (m - n))%Z by lia.
      destruct (m - n)%N as [|k] eqn:Ek; [lia|].
      cbn [Z.of_N Z.opp zpow].
      rewrite pw_add, conj_mul.
      pose proof (cyc_pw f n Hf) as Hn. cbv [cyclotomic] in Hn.
      transitivity (fp12_mul (fp12_mul (pw f n) (conj (pw f n))) (conj (pw f (Npos k)))); [ring|].
      rewrite Hn; ring.
  Qed.

  Lemma zpow_add : forall f a b, cyclotomic f ->
    zpow f (a + b) = fp12_mul (zpow f a) (zpow f b).
  Proof.
    intros f a b Hf.
    assert (HN : forall x, Z.of_N (Z.to_N x) = Z.max 0 x) by (intros [|x|x]; reflexivity).
    transitivity (fp12_mul (pw f (Z.to_N a + Z.to_N b)) (conj (pw f (Z.to_N (- a) + Z.to_N (- b))))).
    - rewrite pw_conj_diff by assumption. f_equal.
      rewrite !N2Z.inj_add, !HN. lia.
    - rewrite !zpow_split, !pw_add, conj_mul. ring.
  Qed.

  Lemma zpow_opp : forall f z, conj (zpow f z) = zpow f (- z).
  Proof.
    intros f [|n|n]; cbn [zpow Z.opp]; rewrite ?conj_one, ?conj_conj; reflexivity.
  Qed.

  Lemma cyc_zpow : forall f z, cyclotomic f -> cyclotomic (zpow f z).
  Proof.
    intros f [|n|n] Hf; cbn [zpow]; auto using cyc_one, cyc_pw, cyc_conj.
  Qed.

  Lemma zpow_mul : forall f a b, cyclotomic f ->
    zpow f (a * b) = zpow (zpow f a) b.
  Proof.
    intros f a b Hf.
    assert (Hnat : forall n, zpow f (a * Z.of_N n) = pw (zpow f a) n).
    { intros n; induction n using N.peano_ind.
      - rewrite Z.mul_0_r; reflexivity.
      - rewrite N2Z.inj_succ, Z.mul_succ_r, zpow_add, IHn, pw_succ by assumption. ring. }
    destruct b as [|n|n].
    - rewrite Z.mul_0_r; reflexivity.
    - exact (Hnat (Npos n)).
    - replace (a * Z.neg n)%Z with (- (a * Z.of_N (Npos n)))%Z by lia.
      rewrite <- zpow_opp, Hnat. reflexivity.
  Qed.

  Lemma zpow_1 : forall f, zpow f 1 = f.
  Proof. intros; apply pw_1. Qed.

  Lemma zpow_conj : forall f z, cyclotomic f -> zpow (conj f) z = zpow f (- z).
  Proof.
    intros f z Hf. replace (conj f) with (zpow f (-1))
      by (change (zpow f (-1)) with (conj (pw f 1)); rewrite pw_1; reflexivity).
    rewrite <- zpow_mul by assumption. f_equal; lia.
  Qed.

  Lemma zpow_mul_base : forall f g z, cyclotomic f -> cyclotomic g ->
    zpow (fp12_mul f g) z = fp12_mul (zpow f z) (zpow g z).
  Proof.
    intros f g [|n|n] Hf Hg; cbn [zpow]; rewrite ?pw_mul_base, ?conj_mul; ring.
  Qed.

  (** Pairing.v's signed exponentiations, on the subgroup. *)
  Lemma pow_bls_x_signed_zpow : forall f, cyclotomic f ->
    P.fp12_pow_bls_x_signed p f = zpow f (- P.bls_x).
  Proof.
    intros f Hf. cbv [P.fp12_pow_bls_x_signed P.fp12_pow_bls_x].
    rewrite fp12_pow_Z_pw by (cbv; split; congruence).
    reflexivity.
  Qed.

  Lemma pow_bls_c_signed_zpow : forall f, cyclotomic f ->
    P.fp12_pow_bls_c_signed p f = zpow f (- P.bls_c).
  Proof.
    intros f Hf. cbv [P.fp12_pow_bls_c_signed P.fp12_pow_bls_c].
    rewrite fp12_pow_Z_pw by (cbv; split; congruence).
    reflexivity.
  Qed.

End Cyclotomic.
