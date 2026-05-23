From Stdlib Require Import ZArith NArith.
From Stdlib Require Import micromega.Lia Bool.Bool.
Require Import Crypto.Spec.ModularArithmetic Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.PrimeFieldTheorems Crypto.Algebra.Hierarchy Crypto.Algebra.Field.
Require Import Crypto.Spec.Curve25519.
Require Import Bedrock.Field.Synthesis.Examples.Ristretto255_Encode.
Local Open Scope F_scope.
Local Notation Fp := (F.F (2^255 - 19)).
Local Notation Fzero := (F.of_Z _ 0).
Local Notation Fone  := (F.of_Z _ 1).
Local Existing Instance Curve25519.field.
Local Existing Instance Curve25519.char_ge_3.
Add Field _f : (Algebra.Field.field_theory_for_stdlib_tactic(T:=F (2^255-19)%positive))
  (morphism (F.ring_morph (2^255-19)%positive), constants [F.is_constant],
   div (F.morph_div_theory (2^255-19)%positive),
   power_tac (F.power_theory (2^255-19)%positive) [F.is_pow_constant]).

Lemma Fpow_pm1 : forall (x : Fp), x <> Fzero -> F.pow x (Z.to_N (2^255 - 19 - 1)) = Fone.
Proof.
  intros x Hx.
  assert (Hxz : F.to_Z x <> 0%Z) by (apply ModularArithmeticTheorems.F.to_Z_nonzero; exact Hx).
  assert (Hrng : (0 <= F.to_Z x < 2^255-19)%Z)
    by (apply ModularArithmeticTheorems.F.to_Z_range; vm_compute; reflexivity).
  apply ModularArithmeticTheorems.F.eq_to_Z_iff.
  rewrite ModularArithmeticTheorems.F.to_Z_pow.
  rewrite ModularArithmeticTheorems.F.to_Z_of_Z.
  rewrite Z2N.id by (vm_compute; intro Hc; discriminate).
  change (Z.pos (2^255-19)%positive) with (2^255 - 19)%Z.
  assert (Hmodnz : (F.to_Z x mod (2^255-19))%Z <> 0%Z)
    by (rewrite Z.mod_small by lia; exact Hxz).
  rewrite (NumTheoryUtil.fermat_little (2^255-19)%Z Curve25519.prime_p (F.to_Z x) Hmodnz).
  rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma SQRT_M1_sq : (SQRT_M1 * SQRT_M1)%F = F.opp Fone.
Proof. unfold SQRT_M1. apply ModularArithmeticTheorems.F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

Lemma mul_zero_factor : forall (a b : Fp), (a * b)%F = Fzero -> a = Fzero \/ b = Fzero.
Proof. intros a b H. apply Hierarchy.zero_product_zero_factor in H. exact H. Qed.

Lemma sub_eq_zero : forall (a b : Fp), (a - b)%F = Fzero -> a = b.
Proof. intros a b H. assert (Hr : a = ((a - b) + b)%F) by field. rewrite Hr, H. field. Qed.

Lemma add_eq_zero : forall (a b : Fp), (a + b)%F = Fzero -> a = F.opp b.
Proof. intros a b H. assert (Hr : a = ((a + b) - b)%F) by field. rewrite Hr, H. field. Qed.

Lemma fourth_roots : forall (t : Fp),
  (t * t * t * t)%F = Fone ->
  t = Fone \/ t = F.opp Fone \/ t = SQRT_M1 \/ t = F.opp SQRT_M1.
Proof.
  intros t Ht.
  assert (Hfac : ((t * t - Fone) * (t * t + Fone))%F = Fzero).
  { transitivity ((t * t * t * t)%F - Fone)%F; [ field | rewrite Ht; field ]. }
  apply mul_zero_factor in Hfac.
  destruct Hfac as [Hsq1 | Hsqm1].
  - assert (Htt : (t * t)%F = Fone) by (apply sub_eq_zero; exact Hsq1).
    assert (Hf2 : ((t - Fone) * (t + Fone))%F = Fzero).
    { transitivity ((t * t)%F - Fone)%F; [ field | rewrite Htt; field ]. }
    apply mul_zero_factor in Hf2.
    destruct Hf2 as [H | H].
    + left. apply sub_eq_zero; exact H.
    + right. left. apply add_eq_zero; exact H.
  - assert (Htt : (t * t)%F = F.opp Fone) by (apply add_eq_zero; exact Hsqm1).
    assert (Hf2 : ((t - SQRT_M1) * (t + SQRT_M1))%F = Fzero).
    { transitivity ((t * t)%F - (SQRT_M1 * SQRT_M1)%F)%F;
        [ field | rewrite Htt, SQRT_M1_sq; field ]. }
    apply mul_zero_factor in Hf2.
    destruct Hf2 as [H | H].
    + right. right. left. apply sub_eq_zero; exact H.
    + right. right. right. apply add_eq_zero; exact H.
Qed.

Lemma is_negative_opp_nonzero : forall (s : Fp),
  s <> Fzero -> is_negative (F.opp s) = negb (is_negative s).
Proof.
  intros s Hnz.
  unfold is_negative.
  rewrite F.to_Z_opp.
  assert (Hp : (0 < 2^255-19)%Z) by (vm_compute; reflexivity).
  assert (Hrng : (0 <= F.to_Z s < 2^255-19)%Z) by (apply F.to_Z_range; lia).
  assert (Hsnz : F.to_Z s <> 0%Z).
  { intro Hz. apply Hnz. apply ModularArithmeticTheorems.F.eq_to_Z_iff.
    rewrite Hz. rewrite F.to_Z_of_Z. reflexivity. }
  rewrite Z.mod_opp_l_nz; [|lia|rewrite Z.mod_small; lia].
  rewrite Z.mod_small by lia.
  change (Z.pos (2^255-19)%positive) with (2^255 - 19)%Z.
  rewrite !Z.bit0_odd.
  rewrite Z.odd_sub.
  replace (Z.odd (2^255 - 19)) with true by reflexivity.
  destruct (Z.odd (F.to_Z s)); reflexivity.
Qed.

Lemma abs_sq : forall (s : Fp), (abs s * abs s)%F = (s * s)%F.
Proof. intros s. unfold abs. destruct (is_negative s); [ field | reflexivity ]. Qed.

Lemma is_negative_abs : forall (s : Fp), is_negative (abs s) = false.
Proof.
  intros s. unfold abs.
  destruct (F.eq_dec s Fzero) as [Hz | Hnz].
  - subst s. unfold is_negative.
    replace (F.to_Z (Fzero : Fp)) with 0%Z by (rewrite ModularArithmeticTheorems.F.to_Z_of_Z; reflexivity).
    reflexivity.
  - destruct (is_negative s) eqn:Hneg.
    + rewrite is_negative_opp_nonzero by exact Hnz. rewrite Hneg. reflexivity.
    + rewrite Hneg. reflexivity.
Qed.

Lemma feqb_iff : forall (x y : Fp), Z.eqb (F.to_Z x) (F.to_Z y) = true <-> x = y.
Proof.
  intros x y. rewrite Z.eqb_eq. split; intro H.
  - apply ModularArithmeticTheorems.F.eq_to_Z_iff. exact H.
  - apply ModularArithmeticTheorems.F.eq_to_Z_iff in H. exact H.
Qed.

Definition ee := ((2^255 - 19 - 5) / 8)%Z.
Definition qq := ((2^255 - 19 - 1) / 4)%Z.

Lemma exp_rel : (2 * Z.to_N ee + 1 = Z.to_N qq)%N.
Proof. unfold ee, qq. vm_compute. reflexivity. Qed.

Lemma exp4_rel : (4 * Z.to_N qq = Z.to_N (2^255 - 19 - 1))%N.
Proof. unfold qq. vm_compute. reflexivity. Qed.

Lemma w_pow_q_fourth : forall (w : Fp), w <> Fzero ->
  ((F.pow w (Z.to_N qq)) * (F.pow w (Z.to_N qq)) * (F.pow w (Z.to_N qq)) * (F.pow w (Z.to_N qq)))%F = Fone.
Proof.
  intros w Hw.
  rewrite <- !ModularArithmeticTheorems.F.pow_add_r.
  replace (Z.to_N qq + Z.to_N qq + Z.to_N qq + Z.to_N qq)%N with (4 * Z.to_N qq)%N by lia.
  rewrite exp4_rel.
  apply Fpow_pm1. exact Hw.
Qed.

Lemma check_eq : forall (u v : Fp),
  let v3 := (v * v * v)%F in
  let v7 := (v3 * v3 * v)%F in
  let r0 := (u * v3 * F.pow (u * v7) (Z.to_N ee))%F in
  (v * r0 * r0)%F = (u * F.pow (u * v7) (Z.to_N qq))%F.
Proof.
  intros u v v3 v7 r0. unfold r0, v7, v3.
  set (w := (u * (v*v*v * (v*v*v) * v))%F).
  rewrite <- exp_rel.
  rewrite ModularArithmeticTheorems.F.pow_add_r.
  rewrite ModularArithmeticTheorems.F.pow_1_r.
  replace (2 * Z.to_N ee)%N with (Z.to_N ee + Z.to_N ee)%N by lia.
  rewrite ModularArithmeticTheorems.F.pow_add_r.
  unfold w. field.
Qed.

Lemma SQRT_M1_nz : SQRT_M1 <> Fzero.
Proof. unfold SQRT_M1. intro H. apply ModularArithmeticTheorems.F.eq_to_Z_iff in H. vm_compute in H. discriminate. Qed.
Lemma one_ne_opp_one : (Fone : Fp) <> F.opp Fone.
Proof. intro H. apply ModularArithmeticTheorems.F.eq_to_Z_iff in H. vm_compute in H. discriminate. Qed.
Lemma sm1_ne_one : SQRT_M1 <> Fone.
Proof. unfold SQRT_M1. intro H. apply ModularArithmeticTheorems.F.eq_to_Z_iff in H. vm_compute in H. discriminate. Qed.
Lemma sm1_ne_opp_one : SQRT_M1 <> F.opp Fone.
Proof. unfold SQRT_M1. intro H. apply ModularArithmeticTheorems.F.eq_to_Z_iff in H. vm_compute in H. discriminate. Qed.
Lemma opp_sm1_ne_one : F.opp SQRT_M1 <> Fone.
Proof. unfold SQRT_M1. intro H. apply ModularArithmeticTheorems.F.eq_to_Z_iff in H. vm_compute in H. discriminate. Qed.
Lemma opp_sm1_ne_opp_one : F.opp SQRT_M1 <> F.opp Fone.
Proof. unfold SQRT_M1. intro H. apply ModularArithmeticTheorems.F.eq_to_Z_iff in H. vm_compute in H. discriminate. Qed.

Lemma mul_cancel_l : forall (a x y : Fp), a <> Fzero -> (a * x)%F = (a * y)%F -> x = y.
Proof.
  intros a x y Ha H.
  assert (Hd : (a * (x - y))%F = Fzero).
  { replace (a * (x - y))%F with ((a * x) - (a * y))%F by field. rewrite H. field. }
  apply mul_zero_factor in Hd. destruct Hd as [Hd | Hd].
  - exfalso. apply Ha. exact Hd.
  - apply sub_eq_zero. exact Hd.
Qed.

Lemma sqrt_ratio_m1_correct :
  forall (u v : Fp),
    v <> Fzero ->
    let '(was_square, r) := sqrt_ratio_m1 u v in
    ((was_square = true  /\ (v * r * r)%F = u) \/
     (was_square = false /\ (v * r * r)%F = (SQRT_M1 * u)%F))
    /\ is_negative r = false.
Proof.
  intros u v Hv.
  unfold sqrt_ratio_m1.
  cbv zeta.
  change (Z.to_N ((2 ^ 255 - 19 - 5) / 8)) with (Z.to_N ee).
  set (r0 := (u * (v * v * v) * (u * (v * v * v * (v * v * v) * v)) ^ Z.to_N ee)%F).
  set (check := (v * r0 * r0)%F).
  split; [ | apply is_negative_abs ].
  assert (Hck : check = (u * F.pow (u * (v * v * v * (v * v * v) * v)) (Z.to_N qq))%F)
    by (unfold check, r0; apply (check_eq u v)).
  destruct (F.eq_dec u Fzero) as [Hu0 | Hune].
  - (* u = 0 *)
    subst u.
    assert (Hr0 : r0 = Fzero) by (unfold r0; field).
    assert (Hcheck0 : check = Fzero) by (unfold check; rewrite Hr0; field).
    rewrite Hcheck0. rewrite Z.eqb_refl. simpl.
    left. split; [ reflexivity | ].
    rewrite Hr0. unfold abs. destruct (is_negative Fzero); field.
  - (* u <> 0 *)
    set (w := (u * (v * v * v * (v * v * v) * v))%F) in *.
    assert (Hwnz : w <> Fzero).
    { unfold w. intro Hc. apply mul_zero_factor in Hc. destruct Hc as [Hc | Hc].
      - apply Hune; exact Hc.
      - repeat (apply mul_zero_factor in Hc; destruct Hc as [Hc | Hc]); apply Hv; exact Hc. }
    set (t := F.pow w (Z.to_N qq)) in *.
    assert (Ht4 : (t * t * t * t)%F = Fone) by (apply w_pow_q_fourth; exact Hwnz).
    assert (Hroots := fourth_roots t Ht4).
    assert (Hcku : check = (u * t)%F) by exact Hck.
    destruct Hroots as [Hr | [Hr | [Hr | Hr]]].
    1:{ (* t = 1 *)
      assert (Hb1 : (F.to_Z check =? F.to_Z u)%Z = true)
        by (apply feqb_iff; rewrite Hcku, Hr; field).
      rewrite Hb1. left. split; [ reflexivity | ].
      replace (v * abs r0 * abs r0)%F with (v * (abs r0 * abs r0))%F by field.
      rewrite abs_sq.
      replace (v * (r0 * r0))%F with check by (unfold check; field).
      rewrite Hck, Hr. field. }
    1:{ (* t = -1 *)
      assert (Hb1 : (F.to_Z check =? F.to_Z u)%Z = false).
      { apply Bool.not_true_is_false. intro Hc. apply feqb_iff in Hc.
        rewrite Hcku in Hc.
        assert (Hcc : (u * t)%F = (u * Fone)%F) by (rewrite Hc; field).
        apply mul_cancel_l in Hcc; [ | exact Hune].
        rewrite Hr in Hcc. apply one_ne_opp_one. symmetry. exact Hcc. }
      assert (Hb2 : (F.to_Z check =? F.to_Z (F.opp u))%Z = true)
        by (apply feqb_iff; rewrite Hcku, Hr; field).
      rewrite Hb1, Hb2. simpl.
      left. split; [ reflexivity | ].
      replace (v * abs (r0 * SQRT_M1) * abs (r0 * SQRT_M1))%F
         with (v * (abs (r0 * SQRT_M1) * abs (r0 * SQRT_M1)))%F by field.
      rewrite abs_sq.
      replace (v * (r0 * SQRT_M1 * (r0 * SQRT_M1)))%F
         with (check * (SQRT_M1 * SQRT_M1))%F by (unfold check; field).
      rewrite SQRT_M1_sq, Hck, Hr. field. }
    1:{ (* t = SQRT_M1 *)
      assert (Hb1 : (F.to_Z check =? F.to_Z u)%Z = false).
      { apply Bool.not_true_is_false. intro Hc. apply feqb_iff in Hc.
        rewrite Hcku in Hc.
        assert (Hcc : (u * t)%F = (u * Fone)%F) by (rewrite Hc; field).
        apply mul_cancel_l in Hcc; [ | exact Hune].
        rewrite Hr in Hcc. apply sm1_ne_one. exact Hcc. }
      assert (Hb2 : (F.to_Z check =? F.to_Z (F.opp u))%Z = false).
      { apply Bool.not_true_is_false. intro Hc. apply feqb_iff in Hc.
        rewrite Hcku in Hc.
        assert (Hcc : (u * t)%F = (u * F.opp Fone)%F) by (rewrite Hc; field).
        apply mul_cancel_l in Hcc; [ | exact Hune].
        rewrite Hr in Hcc. apply sm1_ne_opp_one. exact Hcc. }
      assert (Hb3 : (F.to_Z check =? F.to_Z (F.opp (SQRT_M1 * u)))%Z = false).
      { apply Bool.not_true_is_false. intro Hc. apply feqb_iff in Hc.
        rewrite Hcku in Hc.
        assert (Hcc : (u * t)%F = (u * F.opp SQRT_M1)%F) by (rewrite Hc; field).
        apply mul_cancel_l in Hcc; [ | exact Hune].
        rewrite Hr in Hcc.
        apply one_ne_opp_one.
        assert (HH : (SQRT_M1 * SQRT_M1)%F = F.opp (SQRT_M1 * SQRT_M1))
          by (rewrite Hcc at 2; field).
        rewrite !SQRT_M1_sq in HH. rewrite Group.inv_inv in HH. symmetry. exact HH. }
      rewrite Hb1, Hb2, Hb3. simpl.
      right. split; [ reflexivity | ].
      replace (v * abs r0 * abs r0)%F with (v * (abs r0 * abs r0))%F by field.
      rewrite abs_sq.
      replace (v * (r0 * r0))%F with check by (unfold check; field).
      rewrite Hck, Hr. field. }
    1:{ (* t = -SQRT_M1 *)
      assert (Hb1 : (F.to_Z check =? F.to_Z u)%Z = false).
      { apply Bool.not_true_is_false. intro Hc. apply feqb_iff in Hc.
        rewrite Hcku in Hc.
        assert (Hcc : (u * t)%F = (u * Fone)%F) by (rewrite Hc; field).
        apply mul_cancel_l in Hcc; [ | exact Hune].
        rewrite Hr in Hcc. apply opp_sm1_ne_one. exact Hcc. }
      assert (Hb2 : (F.to_Z check =? F.to_Z (F.opp u))%Z = false).
      { apply Bool.not_true_is_false. intro Hc. apply feqb_iff in Hc.
        rewrite Hcku in Hc.
        assert (Hcc : (u * t)%F = (u * F.opp Fone)%F) by (rewrite Hc; field).
        apply mul_cancel_l in Hcc; [ | exact Hune].
        rewrite Hr in Hcc. apply opp_sm1_ne_opp_one. exact Hcc. }
      assert (Hb3 : (F.to_Z check =? F.to_Z (F.opp (SQRT_M1 * u)))%Z = true)
        by (apply feqb_iff; rewrite Hcku, Hr; field).
      rewrite Hb1, Hb2, Hb3. simpl.
      right. split; [ reflexivity | ].
      replace (v * abs (r0 * SQRT_M1) * abs (r0 * SQRT_M1))%F
         with (v * (abs (r0 * SQRT_M1) * abs (r0 * SQRT_M1)))%F by field.
      rewrite abs_sq.
      replace (v * (r0 * SQRT_M1 * (r0 * SQRT_M1)))%F
         with (check * (SQRT_M1 * SQRT_M1))%F by (unfold check; field).
      rewrite SQRT_M1_sq, Hck, Hr. field. }
Qed.

