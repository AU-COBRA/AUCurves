(** * ZFInv.v — Fermat's LT bridge for [zfp_inv] / [zfp2_inv].

    The Z-level [zfp_inv p x] is implemented as [x^(p-2) mod p] via
    square-and-multiply in [zpow_mod_aux].  For prime [p], this is
    the multiplicative inverse.  Fiat-crypto has the F-level fact in
    [PrimeFieldTheorems.F.inv_nonzero] / [Fq_inv_fermat].  This file
    bridges the two and lifts to Fp2. *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import NArith.NArith.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Ring_theory Field_theory Field_tac.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Bedrock.Field.PairingTheory.ZModTower.
Require Import Bedrock.Field.PairingTheory.CanonicityHelpers.

Local Open Scope Z_scope.

(** Helper: [(x mod m)^k mod m = x^k mod m]. *)
Lemma Z_mod_pow_l : forall x k (m : Z),
  0 < m -> 0 <= k -> ((x mod m) ^ k) mod m = (x ^ k) mod m.
Proof.
  intros x k m Hm Hk.
  generalize dependent k.
  apply natlike_ind; intros.
  - simpl. reflexivity.
  - rewrite !Z.pow_succ_r by lia.
    rewrite Z.mul_mod by lia. rewrite H0. rewrite <- Z.mul_mod by lia.
    rewrite Z.mul_mod with (a := x mod m) by lia.
    rewrite Zmod_mod. rewrite <- Z.mul_mod by lia.
    reflexivity.
Qed.

(** Helper: [(-1) mod n = n - 1] for [1 < n]. *)
Lemma neg_one_mod : forall n, 1 < n -> (-1) mod n = n - 1.
Proof.
  intros n Hn.
  replace (-1) with (-(1)) by ring.
  rewrite Z.mod_opp_l_nz.
  - rewrite Z.mod_small by lia. lia.
  - lia.
  - rewrite Z.mod_small by lia. lia.
Qed.

(** Helper: [(-1)^(2m+1) = -1] in Z. *)
Lemma neg_one_pow_odd_Z : forall m : Z, 0 <= m -> (-1) ^ (2*m+1) = -1.
Proof.
  intros m Hm.
  rewrite Z.pow_add_r by lia.
  rewrite Z.pow_mul_r by lia.
  replace ((-1)^2) with 1 by reflexivity.
  rewrite Z.pow_1_l by lia.
  rewrite Z.pow_1_r. ring.
Qed.

(** Helper: [F.opp 1 ^ k = F.opp 1] in [F qq] for odd positive [k]. *)
Lemma F_opp_one_pow_odd {qq : positive} {prime_qq : prime qq} (Hq : 2 < Z.pos qq) :
  forall k : Z, 0 < k -> Z.odd k = true ->
    ((F.opp (1 : F qq))%F ^ Z.to_N k)%F = (F.opp 1)%F.
Proof.
  intros k Hk Hodd.
  apply F.eq_to_Z_iff.
  rewrite F.to_Z_pow, Z2N.id by lia.
  assert (HtoZopp : F.to_Z ((F.opp 1)%F : F qq) = Z.pos qq - 1).
  { rewrite F.to_Z_opp. rewrite (@F.to_Z_1 qq Hq).
    apply neg_one_mod; lia. }
  rewrite HtoZopp.
  rewrite <- (neg_one_mod (Z.pos qq)) by lia.
  rewrite Z_mod_pow_l by lia.
  apply Z.odd_spec in Hodd. destruct Hodd as [m Hm]. rewrite Hm.
  rewrite neg_one_pow_odd_Z by lia.
  reflexivity.
Qed.

(** Helper: [F.opp 1 <> 1] in [F qq] for [q > 2]. *)
Lemma F_opp_one_ne_one {qq : positive} (Hq : 2 < Z.pos qq) :
  (F.opp 1 : F qq)%F <> (1 : F qq)%F.
Proof.
  intro H.
  apply F.eq_to_Z_iff in H.
  rewrite F.to_Z_opp, (@F.to_Z_1 qq Hq) in H.
  rewrite neg_one_mod in H by lia. lia.
Qed.

(** ** Step 1.1: [zpow_mod_aux] implements modular exponentiation. *)

Section ZPowModAux.
  Context (p : Z) (Hp : 0 < p).

  Lemma zpow_mod_aux_correct : forall (fuel : nat) (base exp acc : Z),
    0 <= exp ->
    (exp < 2 ^ Z.of_nat fuel)%Z ->
    0 <= acc < p ->
    zpow_mod_aux base exp acc p fuel = ((base ^ exp) * acc) mod p.
  Proof.
    induction fuel as [|fuel' IH]; intros base exp acc Hexp Hfuel Hacc.
    - simpl in Hfuel. assert (Hexp0 : exp = 0) by lia. subst exp.
      cbn [zpow_mod_aux].
      rewrite Z.pow_0_r, Z.mul_1_l, Z.mod_small by lia. reflexivity.
    - simpl.
      set (acc' := if Z.odd exp then (acc * base) mod p else acc).
      set (base' := (base * base) mod p).
      assert (Hacc' : 0 <= acc' < p).
      { unfold acc'. destruct (Z.odd exp); [apply Z.mod_pos_bound; lia | exact Hacc]. }
      assert (Hdiv2_bound : 0 <= Z.div2 exp) by (apply Z.div2_nonneg; lia).
      assert (Hdiv2_fuel : Z.div2 exp < 2 ^ Z.of_nat fuel').
      { rewrite Nat2Z.inj_succ in Hfuel.
        rewrite Z.pow_succ_r in Hfuel by lia.
        rewrite Z.div2_div. apply Z.div_lt_upper_bound; lia. }
      rewrite (IH base' (Z.div2 exp) acc' Hdiv2_bound Hdiv2_fuel Hacc').
      unfold acc', base'.
      destruct (Z.odd exp) eqn:Hodd.
      + assert (Heq : exp = 2 * Z.div2 exp + 1).
        { rewrite (Zdiv2_odd_eqn exp) at 1. rewrite Hodd. reflexivity. }
        rewrite Heq at 2.
        rewrite Z.pow_add_r by lia.
        rewrite Z.pow_mul_r by lia.
        replace (base ^ 2) with (base * base) by (rewrite Z.pow_2_r; reflexivity).
        rewrite Z.pow_1_r.
        rewrite Z.mul_mod_idemp_r by lia.
        rewrite Z.mul_mod with (a := ((base * base) mod p) ^ _) by lia.
        rewrite Z_mod_pow_l by lia.
        rewrite <- Z.mul_mod by lia.
        f_equal. ring.
      + assert (Heq : exp = 2 * Z.div2 exp).
        { rewrite (Zdiv2_odd_eqn exp) at 1. rewrite Hodd. ring. }
        rewrite Heq at 2.
        rewrite Z.pow_mul_r by lia.
        replace (base ^ 2) with (base * base) by (rewrite Z.pow_2_r; reflexivity).
        rewrite Z.mul_mod with (a := ((base * base) mod p) ^ _) by lia.
        rewrite Z_mod_pow_l by lia.
        rewrite <- Z.mul_mod by lia.
        reflexivity.
  Qed.

End ZPowModAux.

(** ** Step 1.2: [zfp_inv] is [F.inv] on canonical Z representatives. *)

Section ZFpInvRelation.
  Context {q : positive} {prime_q : prime q}.

  Lemma zfp_inv_fuel_ok :
    Z.pos q - 2 < 2 ^ Z.of_nat (Z.to_nat (Z.log2 (Z.pos q - 2) + 2)).
  Proof.
    pose proof (prime_ge_2 _ prime_q) as Hq2.
    set (k := Z.log2 (Z.pos q - 2)).
    assert (Hk_nn : 0 <= k).
    { unfold k. destruct (Z_lt_le_dec 0 (Z.pos q - 2)) as [Hgt|Hle].
      - apply Z.log2_nonneg.
      - replace (Z.pos q - 2) with 0 by lia. simpl. lia. }
    rewrite Z2Nat.id by lia.
    destruct (Z_lt_le_dec 0 (Z.pos q - 2)) as [Hgt|Hle].
    - pose proof (Z.log2_spec _ Hgt) as [Hlow Hhigh].
      fold k in Hlow, Hhigh.
      assert (Hpow : 2 ^ (k + 2) = 4 * 2 ^ k).
      { rewrite Z.pow_add_r by lia.
        replace (2 ^ 2) with 4 by reflexivity. ring. }
      rewrite Hpow.
      assert (Hkpos : 1 <= 2 ^ k) by (apply (Z.pow_le_mono_r 2 0 k); lia).
      rewrite Z.pow_succ_r in Hhigh by lia.
      lia.
    - replace (Z.pos q - 2) with 0 by lia. simpl. lia.
  Qed.

  Lemma zfp_inv_eq_pow : forall (x : Z),
    zfp_inv (Z.pos q) x = (x ^ (Z.pos q - 2) * 1) mod Z.pos q.
  Proof.
    intro x. unfold zfp_inv.
    pose proof (prime_ge_2 _ prime_q) as Hq2.
    apply zpow_mod_aux_correct; [lia|lia|apply zfp_inv_fuel_ok|lia].
  Qed.

  Lemma F_of_Z_zfp_inv : forall (x : Z),
    2 < Z.pos q ->
    0 <= x < Z.pos q ->
    x <> 0 ->
    F.of_Z q (zfp_inv (Z.pos q) x) = F.inv (F.of_Z q x).
  Proof.
    intros x Hq Hxrange Hxnz.
    rewrite (@F.Fq_inv_fermat q prime_q Hq).
    rewrite zfp_inv_eq_pow.
    rewrite Z.mul_1_r.
    rewrite F.of_Z_mod.
    rewrite F.of_Z_pow.
    apply F.eq_to_Z_iff.
    rewrite !F.to_Z_of_Z.
    rewrite Z2N.id by lia.
    rewrite Zmod_mod. reflexivity.
  Qed.

End ZFpInvRelation.

(** ** Step 1.3: Left-inverse of [zfp_inv] for nonzero canonical x. *)

Section ZFpInvLeft.
  Context {q : positive} {prime_q : prime q}.

  Lemma zfp_inv_left : forall (x : Z),
    2 < Z.pos q ->
    0 < x < Z.pos q ->
    zfp_mul (Z.pos q) (zfp_inv (Z.pos q) x) x = 1.
  Proof.
    intros x Hq Hx.
    assert (Hxnz : x <> 0) by lia.
    assert (Hxrange : 0 <= x < Z.pos q) by lia.
    assert (HFnz : F.of_Z q x <> 0%F).
    { intro HH.
      apply F.eq_to_Z_iff in HH.
      rewrite F.to_Z_of_Z, F.to_Z_0 in HH.
      rewrite Z.mod_small in HH by lia. lia. }
    pose proof (@F.inv_nonzero q prime_q (F.of_Z q x) HFnz) as HinvF.
    apply (f_equal F.to_Z) in HinvF.
    rewrite F.to_Z_mul in HinvF.
    rewrite (@F.to_Z_1 q Hq) in HinvF.
    rewrite F.to_Z_of_Z in HinvF.
    rewrite <- F_of_Z_zfp_inv in HinvF by assumption.
    rewrite F.to_Z_of_Z in HinvF.
    unfold zfp_mul.
    rewrite Zmult_mod_idemp_l in HinvF.
    rewrite (Z.mod_small x) in HinvF by lia.
    exact HinvF.
  Qed.

End ZFpInvLeft.

(** ** Step 1.4: Fp2 sum-of-squares and left-inverse.

    For [q ≡ 3 mod 4], [-1] is a non-residue in [F q].  This means
    [a^2 + b^2 = 0 (mod q)] implies [a = 0 and b = 0] (else [-1] would
    be a square via [-1 = (a/b)^2]).  We prove this fact via
    [euler_criterion], then use it to show [n := a^2 + b^2 mod q] is
    nonzero whenever [(a, b) != (0, 0)], which allows applying
    [zfp_inv_left] to [n]. *)

Section ZFp2InvLeft.
  Context {q : positive} {prime_q : prime q}.
  Context (q_3mod4 : Z.pos q mod 4 = 3).

  Add Field _zfp2_field : (Algebra.Field.field_theory_for_stdlib_tactic(T:=F q))
    (morphism (F.ring_morph q),
     constants [F.is_constant],
     div (F.morph_div_theory q),
     power_tac (F.power_theory q) [F.is_pow_constant]).

  Lemma two_lt_q_3mod4 : 2 < Z.pos q.
  Proof.
    pose proof (prime_ge_2 _ prime_q) as Hq2.
    destruct (Zle_lt_or_eq _ _ Hq2) as [H|H]; [exact H|].
    rewrite <- H in q_3mod4. discriminate.
  Qed.

  Lemma q_div_2_odd : Z.odd (Z.pos q / 2) = true.
  Proof.
    pose proof two_lt_q_3mod4 as Hq.
    assert (H4 : Z.pos q = 4 * (Z.pos q / 4) + 3).
    { pose proof (Z.div_mod (Z.pos q) 4). rewrite q_3mod4 in H. lia. }
    assert (Hq2 : Z.pos q / 2 = 2 * (Z.pos q / 4) + 1).
    { rewrite H4 at 1.
      replace (4 * (Z.pos q / 4) + 3) with (1 + (2 * (Z.pos q / 4) + 1) * 2) by ring.
      rewrite Z_div_plus_full by lia. reflexivity. }
    rewrite Hq2.
    replace (2 * (Z.pos q / 4) + 1) with (1 + 2 * (Z.pos q / 4)) by ring.
    rewrite Z.odd_add_mul_2. reflexivity.
  Qed.

  (** -1 is a non-residue in F q when q ≡ 3 mod 4. *)
  Lemma Fp_neg_one_nonsquare :
    ~ exists s : F q, (s * s)%F = (F.opp 1)%F.
  Proof.
    pose proof two_lt_q_3mod4 as Hq.
    pose proof q_div_2_odd as Hodd.
    pose proof (prime_ge_2 _ prime_q) as Hq2.
    intro Hsq.
    assert (Hnz : (F.opp 1 : F q)%F <> 0%F).
    { intro H. apply F.eq_to_Z_iff in H.
      rewrite F.to_Z_opp, (@F.to_Z_1 q Hq), F.to_Z_0 in H.
      rewrite neg_one_mod in H by lia. lia. }
    pose proof (@F.euler_criterion q prime_q Hq (F.opp 1)%F Hnz) as Heul.
    assert (Hrhs : ((F.opp 1)%F ^ Z.to_N (Z.pos q / 2))%F = (F.opp 1 : F q)%F).
    { apply F_opp_one_pow_odd; [exact Hq | | exact Hodd].
      assert (Hdiv : 0 < Z.pos q / 2).
      { apply Z.div_str_pos. lia. }
      exact Hdiv. }
    assert (Hlhs : ((F.opp 1)%F ^ Z.to_N (Z.pos q / 2))%F = (1 : F q)%F)
      by (apply Heul; exact Hsq).
    rewrite Hrhs in Hlhs.
    apply (F_opp_one_ne_one Hq). exact Hlhs.
  Qed.

  (** If a^2 + b^2 = 0 in F q with q ≡ 3 mod 4, then a = 0 and b = 0. *)
  Lemma Fp_sum_of_squares_zero_implies_both :
    forall a b : F q, (a * a + b * b)%F = 0%F -> a = 0%F /\ b = 0%F.
  Proof.
    pose proof two_lt_q_3mod4 as Hq.
    intros a b Heq.
    destruct (F.eq_dec b 0) as [Hb|Hb].
    - subst b. split; [|reflexivity].
      assert (Haa : (a * a)%F = 0%F) by (rewrite <- Heq; ring).
      destruct (proj1 (Ring.zero_product_iff_zero_factor a a) Haa); assumption.
    - exfalso. apply Fp_neg_one_nonsquare.
      exists (F.div a b).
      unfold F.div.
      assert (Haa_eq : (a * a)%F = (F.opp (b * b))%F).
      { apply (f_equal (fun x => (x - b*b)%F)) in Heq.
        ring_simplify in Heq.
        rewrite !F.pow_2_r in Heq.
        rewrite Heq. ring. }
      transitivity ((a * a) * (F.inv b * F.inv b))%F; [ring|].
      rewrite Haa_eq.
      assert (HinvB : (F.inv b * b)%F = 1%F) by (apply (@F.inv_nonzero q prime_q); exact Hb).
      transitivity (F.opp ((b * F.inv b) * (b * F.inv b)))%F; [ring|].
      replace (b * F.inv b)%F with (1 : F q)%F; [ring|].
      rewrite <- HinvB. ring.
  Qed.

  Lemma sum_of_squares_nonzero_Z : forall a b : Z,
    0 <= a < Z.pos q -> 0 <= b < Z.pos q ->
    (a, b) <> (0, 0) ->
    zfp_add (Z.pos q) (zfp_mul (Z.pos q) a a) (zfp_mul (Z.pos q) b b) <> 0.
  Proof.
    intros a b Ha Hb Hab H.
    pose proof two_lt_q_3mod4 as Hq.
    (* Lift to F q. *)
    assert (HF : (F.of_Z q a * F.of_Z q a + F.of_Z q b * F.of_Z q b)%F = 0%F).
    { apply F.eq_to_Z_iff.
      rewrite F.to_Z_add, !F.to_Z_mul, !F.to_Z_of_Z, F.to_Z_0.
      (* Goal: (a*a mod q + b*b mod q mod q) mod q mod q ... = 0 *)
      unfold zfp_add, zfp_mul in H.
      rewrite (Z.mod_small a) by lia.
      rewrite (Z.mod_small b) by lia.
      exact H. }
    apply Fp_sum_of_squares_zero_implies_both in HF.
    destruct HF as [Ha0 Hb0].
    apply Hab.
    apply F.eq_to_Z_iff in Ha0, Hb0.
    rewrite F.to_Z_of_Z, F.to_Z_0 in Ha0, Hb0.
    rewrite Z.mod_small in Ha0, Hb0 by lia.
    subst a b. reflexivity.
  Qed.

  Lemma zfp2_inv_left : forall (a b : Z),
    0 <= a < Z.pos q -> 0 <= b < Z.pos q ->
    (a, b) <> (0, 0) ->
    zfp2_mul (Z.pos q) (zfp2_inv (Z.pos q) (a, b)) (a, b) = (1, 0).
  Proof.
    intros a b Ha Hb Hab.
    pose proof two_lt_q_3mod4 as Hq.
    pose proof (sum_of_squares_nonzero_Z a b Ha Hb Hab) as Hn.
    set (n := zfp_add (Z.pos q) (zfp_mul (Z.pos q) a a) (zfp_mul (Z.pos q) b b)).
    fold n in Hn.
    assert (Hn_range : 0 <= n < Z.pos q).
    { unfold n, zfp_add. apply Z.mod_pos_bound; lia. }
    assert (Hn_pos : 0 < n) by lia.
    pose proof (@zfp_inv_left q prime_q n Hq (conj Hn_pos (proj2 Hn_range))) as Hinv.
    (* zfp2_mul p (zfp2_inv p (a,b)) (a,b) *)
    unfold zfp2_mul, zfp2_inv. cbn [fst snd]. fold n.
    set (ni := zfp_inv (Z.pos q) n).
    (* First component: (a*ni)*a - (-b*ni)*b = a^2*ni + b^2*ni = n*ni = 1 *)
    (* Second component: (a*ni)*b + (-b*ni)*a = a*b*ni - a*b*ni = 0 *)
    f_equal.
    - (* First component: zfp_sub p (zfp_mul p (a*ni) a) (zfp_mul p (-b*ni) b) = 1 *)
      unfold zfp_sub, zfp_mul, zfp_neg, zfp_add.
      assert (Heq1 : ((((a * ni) mod Z.pos q * a) mod Z.pos q -
                      ((Z.pos q - b) mod Z.pos q * ni) mod Z.pos q * b mod Z.pos q) mod Z.pos q)
                     = ((n * ni) mod Z.pos q)).
      { unfold n, zfp_add, zfp_mul, zfp_sub.
        push_Zmod. pull_Zmod.
        f_equal. ring. }
      rewrite Heq1.
      rewrite Z.mul_comm.
      unfold zfp_mul in Hinv. unfold ni. rewrite Hinv. reflexivity.
    - (* Second component: (a*ni)*b + (-b*ni)*a = 0 *)
      unfold zfp_add, zfp_mul, zfp_neg.
      assert (Heq2 : ((((a * ni) mod Z.pos q * b) mod Z.pos q +
                      ((Z.pos q - b) mod Z.pos q * ni) mod Z.pos q * a mod Z.pos q) mod Z.pos q)
                     = 0).
      { push_Zmod. pull_Zmod.
        (* After push_Zmod / pull_Zmod: (a * ni * b + (0 - b) * ni * a) mod q = 0. *)
        replace (a * ni * b + (0 - b) * ni * a) with 0 by ring.
        apply Z.mod_0_l; lia. }
      rewrite Heq2. reflexivity.
  Qed.

End ZFp2InvLeft.

(** ** Beta-parametric Fp2 left inverse.

    Generalises [ZFp2InvLeft] to [Fp2 = Fp[u]/(u^2 - beta)] for any
    [beta] with [beta] a quadratic non-residue in F q (equivalently,
    [u^2 - beta] is irreducible over Fp).  The norm of [a + bu] is
    [a^2 - beta * b^2]; this section proves it is nonzero on nonzero
    inputs, and derives [zfp2_inv_left_beta].

    The concrete [beta]-specific non-residue hypothesis is supplied by
    the caller:
    - For BN254 family ([beta = -1], [q ≡ 3 mod 4]): via [Fp_neg_one_nonsquare].
    - For BLS12-377 ([beta = -5], [Legendre(-5, p) = -1]): via a
      Pocklington-style Legendre witness (deferred; see
      [CurvePrimalityFacts]). *)

Section ZFp2InvLeftBeta.
  Context {q : positive} {prime_q : prime q}.
  Context (beta : Z).
  Context (Hq : 2 < Z.pos q).

  Add Field _zfp2_beta_field : (Algebra.Field.field_theory_for_stdlib_tactic(T:=F q))
    (morphism (F.ring_morph q),
     constants [F.is_constant],
     div (F.morph_div_theory q),
     power_tac (F.power_theory q) [F.is_pow_constant]).

  (** Quadratic non-residue hypothesis: [beta] is not a square in [F q]. *)
  Hypothesis Fp_beta_nonsquare :
    ~ exists s : F q, (s * s)%F = F.of_Z q beta.

  (** If [a^2 = beta * b^2] in [F q] with [beta] a non-residue, then
      [a = 0] and [b = 0]. *)
  Lemma Fp_a_sq_eq_beta_b_sq_implies_zero :
    forall a b : F q, (a * a)%F = (F.of_Z q beta * (b * b))%F -> a = 0%F /\ b = 0%F.
  Proof.
    intros a b Heq.
    destruct (F.eq_dec b 0) as [Hb|Hb].
    - subst b. split; [|reflexivity].
      assert (Haa : (a * a)%F = 0%F).
      { rewrite Heq. ring. }
      destruct (proj1 (Ring.zero_product_iff_zero_factor a a) Haa); assumption.
    - exfalso. apply Fp_beta_nonsquare.
      exists (F.div a b).
      unfold F.div.
      assert (HinvB : (F.inv b * b)%F = 1%F) by (apply (@F.inv_nonzero q prime_q); exact Hb).
      assert (HinvB' : (b * F.inv b)%F = 1%F)
        by (rewrite F.mul_comm; exact HinvB).
      (* (a/b)^2 = a^2 / b^2 = beta * b^2 / b^2 = beta *)
      transitivity ((a * a) * (F.inv b * F.inv b))%F; [ring|].
      rewrite Heq.
      replace ((F.of_Z q beta * (b * b)) * (F.inv b * F.inv b))%F
        with (F.of_Z q beta * ((b * F.inv b) * (b * F.inv b)))%F by ring.
      rewrite HinvB'. ring.
  Qed.

  (** If [a^2 - beta * b^2 = 0] in [F q], same conclusion. *)
  Lemma Fp_norm_zero_implies_zero :
    forall a b : F q, (a * a - F.of_Z q beta * (b * b))%F = 0%F -> a = 0%F /\ b = 0%F.
  Proof.
    intros a b H.
    apply Fp_a_sq_eq_beta_b_sq_implies_zero.
    apply (f_equal (fun x => (x + F.of_Z q beta * (b * b))%F)) in H.
    ring_simplify in H. rewrite H. ring.
  Qed.

  (** Z-level: the norm [a^2 - beta*b^2 mod q] is nonzero on nonzero inputs. *)
  Lemma norm_nonzero_Z : forall a b : Z,
    0 <= a < Z.pos q -> 0 <= b < Z.pos q ->
    (a, b) <> (0, 0) ->
    zfp_sub (Z.pos q) (zfp_mul (Z.pos q) a a)
                      (zfp_mul (Z.pos q) beta (zfp_mul (Z.pos q) b b)) <> 0.
  Proof.
    intros a b Ha Hb Hab H.
    assert (HF : (F.of_Z q a * F.of_Z q a -
                  F.of_Z q beta * (F.of_Z q b * F.of_Z q b))%F = 0%F).
    { apply F.eq_to_Z_iff.
      rewrite F.to_Z_sub, !F.to_Z_mul, !F.to_Z_of_Z, F.to_Z_0.
      unfold zfp_sub, zfp_mul in H.
      rewrite (Z.mod_small a) by lia.
      rewrite (Z.mod_small b) by lia.
      rewrite <- H. f_equal.
      push_Zmod. pull_Zmod. f_equal. ring. }
    apply Fp_norm_zero_implies_zero in HF.
    destruct HF as [Ha0 Hb0].
    apply Hab.
    apply F.eq_to_Z_iff in Ha0, Hb0.
    rewrite F.to_Z_of_Z, F.to_Z_0 in Ha0, Hb0.
    rewrite Z.mod_small in Ha0, Hb0 by lia.
    subst a b. reflexivity.
  Qed.

  (** The Z-level left inverse for [zfp2_inv_beta]. *)
  Lemma zfp2_inv_left_beta : forall (a b : Z),
    0 <= a < Z.pos q -> 0 <= b < Z.pos q ->
    (a, b) <> (0, 0) ->
    zfp2_mul_beta (Z.pos q) beta (zfp2_inv_beta (Z.pos q) beta (a, b)) (a, b)
      = (1, 0).
  Proof.
    intros a b Ha Hb Hab.
    pose proof (norm_nonzero_Z a b Ha Hb Hab) as Hn.
    set (n := zfp_sub (Z.pos q) (zfp_mul (Z.pos q) a a)
                                 (zfp_mul (Z.pos q) beta (zfp_mul (Z.pos q) b b))).
    fold n in Hn.
    assert (Hn_range : 0 <= n < Z.pos q).
    { unfold n, zfp_sub. apply Z.mod_pos_bound; lia. }
    assert (Hn_pos : 0 < n) by lia.
    pose proof (@zfp_inv_left q prime_q n Hq (conj Hn_pos (proj2 Hn_range))) as Hinv.
    unfold zfp2_mul_beta, zfp2_inv_beta. cbn [fst snd]. fold n.
    set (ni := zfp_inv (Z.pos q) n).
    f_equal.
    - (* First component:
         zfp_add (zfp_mul (a*ni) a) (zfp_mul beta (zfp_mul (-b*ni) b))
         = (a*ni*a + beta * ((q - b) * ni * b)) mod q = (a^2 - beta * b^2) * ni / 1 = 1.
       *)
      unfold zfp_add, zfp_mul, zfp_neg.
      assert (Heq1 : ((((a * ni) mod Z.pos q * a) mod Z.pos q +
                      (beta *
                       ((Z.pos q - b) mod Z.pos q * ni mod Z.pos q * b mod Z.pos q))
                       mod Z.pos q) mod Z.pos q)
                     = ((n * ni) mod Z.pos q)).
      { unfold n, zfp_sub, zfp_mul.
        push_Zmod. pull_Zmod.
        f_equal. ring. }
      rewrite Heq1.
      rewrite Z.mul_comm.
      unfold zfp_mul in Hinv. unfold ni. rewrite Hinv. reflexivity.
    - (* Second component:
         zfp_add (zfp_mul (a*ni) b) (zfp_mul (-b*ni) a) = 0.
       *)
      unfold zfp_add, zfp_mul, zfp_neg.
      assert (Heq2 : ((((a * ni) mod Z.pos q * b) mod Z.pos q +
                      ((Z.pos q - b) mod Z.pos q * ni) mod Z.pos q * a mod Z.pos q) mod Z.pos q)
                     = 0).
      { push_Zmod. pull_Zmod.
        replace (a * ni * b + (0 - b) * ni * a) with 0 by ring.
        apply Z.mod_0_l; lia. }
      rewrite Heq2. reflexivity.
  Qed.

End ZFp2InvLeftBeta.
