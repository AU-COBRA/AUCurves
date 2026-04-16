(** * wNAF (windowed Non-Adjacent Form) digit expansion.

    Converts a non-negative integer k into a sequence of signed digits
    d_i such that k = Σ d_i · 2^i, with the non-adjacency property.

    Window size w is typically 4, giving digits in {-7..7}. *)

From Stdlib Require Import ZArith Lia List.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Core algorithm *)

Definition wnaf_digit (w : nat) (k : Z) : Z :=
  if Z.odd k then
    let d := k mod (2 ^ Z.of_nat w) in
    if d >=? 2 ^ (Z.of_nat w - 1) then d - 2 ^ Z.of_nat w else d
  else
    0.

Definition wnaf_shift (w : nat) (k : Z) : Z :=
  (k - wnaf_digit w k) / 2.

Fixpoint wnaf_digits (w : nat) (k : Z) (len : nat) : list Z :=
  match len with
  | O => []
  | S n => wnaf_digit w k :: wnaf_digits w (wnaf_shift w k) n
  end.

(** ** Weighted sum *)

Fixpoint weighted_sum (digits : list Z) (pos : nat) : Z :=
  match digits with
  | [] => 0
  | d :: rest => d * 2 ^ Z.of_nat pos + weighted_sum rest (S pos)
  end.

Definition wsum (digits : list Z) : Z := weighted_sum digits 0.

(** ** Step reconstruction *)

Lemma wnaf_reconstruct_step : forall w k,
  (1 < w)%nat ->
  k = wnaf_digit w k + 2 * wnaf_shift w k.
Proof.
  intros w k Hw. unfold wnaf_shift.
  (* k - d is always even, so d + 2 * ((k-d)/2) = d + (k-d) = k *)
  enough (H : (k - wnaf_digit w k) mod 2 = 0) by
    (pose proof (Z.div_mod (k - wnaf_digit w k) 2 ltac:(lia)); lia).
  (* Show (k - wnaf_digit w k) is even *)
  unfold wnaf_digit.
  assert (Hpow : 0 < 2 ^ Z.of_nat w) by (apply Z.pow_pos_nonneg; lia).
  assert (H2w : 2 ^ Z.of_nat w = 2 * 2 ^ (Z.of_nat w - 1)).
  { rewrite <- Z.pow_succ_r by lia. f_equal. lia. }
  destruct (Z.odd k) eqn:Hodd.
  - set (m := k mod 2 ^ Z.of_nat w).
    assert (Hm : 0 <= m < 2 ^ Z.of_nat w) by (subst m; apply Z.mod_pos_bound; lia).
    assert (Hkm : k mod (2 ^ Z.of_nat w) = m) by (subst m; reflexivity).
    destruct (m >=? 2 ^ (Z.of_nat w - 1)) eqn:Hge.
    + (* k-d = 2^w*(k/2^w+1), divisible by 2 since 2^w = 2*2^(w-1) *)
      apply Z.geb_le in Hge.
      replace (k - (m - 2 ^ Z.of_nat w)) with
        (2 * (2 ^ (Z.of_nat w - 1) * (k / 2 ^ Z.of_nat w + 1))).
      { rewrite Z.mul_comm. apply Z_mod_mult. }
      { pose proof (Z.div_mod k (2 ^ Z.of_nat w) ltac:(lia)). nia. }
    + (* k-d = 2^w*(k/2^w), divisible by 2 *)
      assert (m < 2 ^ (Z.of_nat w - 1)) by
        (rewrite Z.geb_leb in Hge; apply Z.leb_gt in Hge; lia).
      replace (k - m) with
        (2 * (2 ^ (Z.of_nat w - 1) * (k / 2 ^ Z.of_nat w))).
      { rewrite Z.mul_comm. apply Z_mod_mult. }
      { pose proof (Z.div_mod k (2 ^ Z.of_nat w) ltac:(lia)). nia. }
  - (* k even, d=0 *)
    rewrite Z.sub_0_r.
    assert (Z.even k = true) by (rewrite <- Z.negb_odd, Hodd; auto).
    rewrite Zeven_mod in H. destruct (k mod 2); auto; discriminate.
Qed.

(** ** Weighted sum shift *)

Lemma pow2_succ : forall p, 2 ^ Z.of_nat (S p) = 2 * 2 ^ Z.of_nat p.
Proof.
  intros. replace (Z.of_nat (S p)) with (1 + Z.of_nat p) by lia.
  rewrite Z.pow_add_r by lia. simpl. lia.
Qed.

Lemma weighted_sum_succ : forall ds p,
  weighted_sum ds (S p) = 2 * weighted_sum ds p.
Proof.
  induction ds as [|d rest IH]; intros p.
  - simpl. lia.
  - unfold weighted_sum. fold weighted_sum.
    rewrite IH, !pow2_succ. lia.
Qed.

(** ** Shifted k is non-negative *)

Lemma wnaf_shift_nonneg : forall w k,
  (1 < w)%nat -> 0 <= k ->
  0 <= wnaf_shift w k.
Proof.
  intros w k Hw Hk.
  unfold wnaf_shift. apply Z.div_pos; [|lia].
  unfold wnaf_digit.
  assert (Hpow : 0 < 2 ^ Z.of_nat w) by (apply Z.pow_pos_nonneg; lia).
  destruct (Z.odd k); [|lia].
  set (m := k mod 2 ^ Z.of_nat w).
  assert (Hm : 0 <= m < 2 ^ Z.of_nat w) by (subst m; apply Z.mod_pos_bound; lia).
  assert (Hkm : k - m >= 0).
  { enough (m <= k) by lia. subst m. apply Z.mod_le; lia. }
  destruct (m >=? 2 ^ (Z.of_nat w - 1)); lia.
Qed.

(** ** Main correctness via remainder identity *)

(** The remaining scalar after processing len digits *)
Fixpoint wnaf_remainder (w : nat) (k : Z) (len : nat) : Z :=
  match len with
  | O => k
  | S n => wnaf_remainder w (wnaf_shift w k) n
  end.

(** General identity: digits reconstruct k up to 2^len * remainder *)
Lemma wnaf_sum_remainder : forall w len k,
  (1 < w)%nat ->
  0 <= k ->
  wsum (wnaf_digits w k len) + 2 ^ Z.of_nat len * wnaf_remainder w k len = k.
Proof.
  intros w. induction len as [|n IH]; intros k Hw Hk.
  - simpl. destruct k; reflexivity.
  - simpl wnaf_digits. simpl wnaf_remainder.
    unfold wsum. simpl weighted_sum. rewrite Z.mul_1_r.
    rewrite weighted_sum_succ.
    set (d := wnaf_digit w k). set (k' := wnaf_shift w k).
    pose proof (wnaf_reconstruct_step w k Hw) as Hrecon.
    fold d k' in Hrecon.
    pose proof (wnaf_shift_nonneg w k Hw Hk) as Hk'0.
    fold k' in Hk'0.
    specialize (IH k' Hw Hk'0).
    unfold wsum in IH.
    rewrite pow2_succ. lia.
Qed.

(** Remainder bound: after len steps, remainder < (k + C) / 2^len *)
Lemma wnaf_remainder_nonneg : forall w len k,
  (1 < w)%nat -> 0 <= k ->
  0 <= wnaf_remainder w k len.
Proof.
  intros w. induction len as [|n IH]; intros k Hw Hk; simpl.
  - lia.
  - apply IH; auto. apply wnaf_shift_nonneg; auto.
Qed.

(** Helper: wnaf_shift of 0 is 0 *)
Lemma wnaf_shift_zero : forall w, wnaf_shift w 0 = 0.
Proof. intros. unfold wnaf_shift, wnaf_digit. simpl. reflexivity. Qed.

(** Helper: remainder of 0 is always 0 *)
Lemma wnaf_remainder_of_zero : forall w m, wnaf_remainder w 0 m = 0.
Proof.
  intros. induction m as [|m' IH]; simpl; [reflexivity|].
  rewrite wnaf_shift_zero. exact IH.
Qed.

(** Helper: even k has shift k/2 (Z.odd version) *)
Lemma wnaf_shift_of_even : forall w k,
  Z.odd k = false -> wnaf_shift w k = k / 2.
Proof.
  intros w0 k0 Hev. unfold wnaf_shift, wnaf_digit.
  rewrite Hev. rewrite Z.sub_0_r. reflexivity.
Qed.

(** Helper: divisibility of shift for odd k *)
Lemma wnaf_shift_odd_div : forall w k,
  (1 < w)%nat -> Z.odd k = true -> 0 <= k ->
  exists q, wnaf_shift w k = q * 2 ^ (Z.of_nat w - 1) /\ 0 <= q.
Proof.
  intros w0 k0 Hw0 Hodd Hk0.
  unfold wnaf_shift, wnaf_digit. rewrite Hodd.
  set (m := k0 mod 2 ^ Z.of_nat w0).
  assert (Hpow : 0 < 2 ^ Z.of_nat w0) by (apply Z.pow_pos_nonneg; lia).
  assert (Hpw1 : 0 < 2 ^ (Z.of_nat w0 - 1)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hm : 0 <= m < 2 ^ Z.of_nat w0) by (subst m; apply Z.mod_pos_bound; lia).
  assert (H2w : 2 ^ Z.of_nat w0 = 2 * 2 ^ (Z.of_nat w0 - 1)).
  { rewrite <- Z.pow_succ_r by lia. f_equal. lia. }
  pose proof (Z.div_mod k0 (2 ^ Z.of_nat w0) ltac:(lia)) as Hkdm.
  assert (Hkm : k0 - m >= 0).
  { enough (m <= k0) by lia. subst m. apply Z.mod_le; lia. }
  destruct (m >=? 2 ^ (Z.of_nat w0 - 1)) eqn:Hge.
  - apply Z.geb_le in Hge.
    exists (k0 / 2 ^ Z.of_nat w0 + 1). split.
    + replace (k0 - (m - 2 ^ Z.of_nat w0)) with
        (2 ^ Z.of_nat w0 * (k0 / 2 ^ Z.of_nat w0 + 1)) by lia.
      rewrite H2w at 1. Z.div_mod_to_equations. nia.
    + assert (0 <= k0 / 2 ^ Z.of_nat w0) by (apply Z.div_pos; lia). lia.
  - rewrite Z.geb_leb in Hge. apply Z.leb_gt in Hge.
    exists (k0 / 2 ^ Z.of_nat w0). split.
    + replace (k0 - m) with
        (2 ^ Z.of_nat w0 * (k0 / 2 ^ Z.of_nat w0)) by lia.
      rewrite H2w at 1. Z.div_mod_to_equations. nia.
    + apply Z.div_pos; lia.
Qed.

(** Helper: even steps just halve -- remainder of q * 2^j after j steps equals remainder of q *)
Lemma wnaf_remainder_even_steps : forall w j q,
  (1 < w)%nat ->
  forall m, wnaf_remainder w (q * 2 ^ Z.of_nat j) (j + m) =
            wnaf_remainder w q m.
Proof.
  intros w0 j q Hw0.
  induction j as [|j' IHj]; intros m.
  - simpl. rewrite Z.mul_1_r. reflexivity.
  - replace (S j' + m)%nat with (S (j' + m)) by lia.
    change (wnaf_remainder w0 (wnaf_shift w0 (q * 2 ^ Z.of_nat (S j'))) (j' + m) =
            wnaf_remainder w0 q m).
    assert (Hpow_s : 2 ^ Z.of_nat (S j') = 2 * 2 ^ Z.of_nat j')
      by (apply pow2_succ).
    assert (Heven : Z.odd (q * 2 ^ Z.of_nat (S j')) = false).
    { rewrite Hpow_s, Z.mul_assoc, !Z.odd_mul.
      replace (Z.odd 2) with false by reflexivity.
      rewrite Bool.andb_false_r. reflexivity. }
    assert (Hhalf : q * 2 ^ Z.of_nat (S j') / 2 = q * 2 ^ Z.of_nat j').
    { rewrite Hpow_s. Z.div_mod_to_equations. nia. }
    rewrite (wnaf_shift_of_even _ _ Heven). rewrite Hhalf. apply IHj.
Qed.

(** Helper: for odd k with k < 2^(w-1), shift = 0 *)
Lemma wnaf_shift_small_odd : forall w k,
  (1 < w)%nat -> Z.odd k = true -> 0 <= k -> k < 2 ^ (Z.of_nat w - 1) ->
  wnaf_shift w k = 0.
Proof.
  intros w0 k0 Hw0 Hodd Hk0 Hksm.
  unfold wnaf_shift, wnaf_digit. rewrite Hodd.
  assert (Hpow : 0 < 2 ^ Z.of_nat w0) by (apply Z.pow_pos_nonneg; lia).
  assert (H2w : 2 ^ Z.of_nat w0 = 2 * 2 ^ (Z.of_nat w0 - 1)).
  { rewrite <- Z.pow_succ_r by lia. f_equal. lia. }
  assert (k0 mod 2 ^ Z.of_nat w0 = k0) as Hmod.
  { apply Z.mod_small. lia. }
  rewrite Hmod.
  destruct (k0 >=? 2 ^ (Z.of_nat w0 - 1)) eqn:Hge.
  - exfalso. apply Z.geb_le in Hge. lia.
  - replace (k0 - k0) with 0 by lia. reflexivity.
Qed.

(** Helper: quotient bound -- q <= k / 2^w + 1 *)
Lemma wnaf_odd_quotient_bound : forall w k q,
  (1 < w)%nat -> Z.odd k = true -> 0 <= k ->
  wnaf_shift w k = q * 2 ^ (Z.of_nat w - 1) ->
  0 <= q -> q <= k / 2 ^ Z.of_nat w + 1.
Proof.
  intros w0 k0 q0 Hw0 Hodd Hk0 Hq Hq0.
  unfold wnaf_shift, wnaf_digit in Hq. rewrite Hodd in Hq.
  set (m := k0 mod 2 ^ Z.of_nat w0) in *.
  assert (Hpow : 0 < 2 ^ Z.of_nat w0) by (apply Z.pow_pos_nonneg; lia).
  assert (Hpw1 : 0 < 2 ^ (Z.of_nat w0 - 1)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hm : 0 <= m < 2 ^ Z.of_nat w0) by (subst m; apply Z.mod_pos_bound; lia).
  assert (H2w : 2 ^ Z.of_nat w0 = 2 * 2 ^ (Z.of_nat w0 - 1)).
  { rewrite <- Z.pow_succ_r by lia. f_equal. lia. }
  pose proof (Z.div_mod k0 (2 ^ Z.of_nat w0) ltac:(lia)) as Hkdm.
  destruct (m >=? 2 ^ (Z.of_nat w0 - 1)) eqn:Hge.
  - apply Z.geb_le in Hge.
    replace (k0 - (m - 2 ^ Z.of_nat w0)) with
      (2 ^ Z.of_nat w0 * (k0 / 2 ^ Z.of_nat w0 + 1)) in Hq by lia.
    rewrite H2w in Hq at 1.
    assert (Htmp : 2 * 2 ^ (Z.of_nat w0 - 1) * (k0 / 2 ^ Z.of_nat w0 + 1) / 2 =
                   (k0 / 2 ^ Z.of_nat w0 + 1) * 2 ^ (Z.of_nat w0 - 1))
      by (Z.div_mod_to_equations; nia).
    rewrite Htmp in Hq. nia.
  - rewrite Z.geb_leb in Hge. apply Z.leb_gt in Hge.
    replace (k0 - m) with
      (2 ^ Z.of_nat w0 * (k0 / 2 ^ Z.of_nat w0)) in Hq by lia.
    rewrite H2w in Hq at 1.
    assert (Htmp : 2 * 2 ^ (Z.of_nat w0 - 1) * (k0 / 2 ^ Z.of_nat w0) / 2 =
                   (k0 / 2 ^ Z.of_nat w0) * 2 ^ (Z.of_nat w0 - 1))
      by (Z.div_mod_to_equations; nia).
    rewrite Htmp in Hq. nia.
Qed.

(** If k < 2^(len-1), then remainder after len+1 steps is 0.
    The extra digit absorbs the carry from negative wNAF digits.
    Example: k=13 needs 5 digits (not 4) despite 13 < 2^4. *)
Lemma wnaf_remainder_zero : forall w len k,
  (1 < w)%nat -> 0 <= k < 2 ^ Z.of_nat len ->
  wnaf_remainder w k (S len) = 0.
Proof.
  intros w len k Hw [Hk0 Hklt].
  (* Strengthen: replace < with <= for an induction-friendly bound *)
  enough (Hstrong : forall n k, (1 < w)%nat -> 0 <= k <= 2 ^ Z.of_nat n ->
    wnaf_remainder w k (S n) = 0) by (apply Hstrong; lia).
  clear k Hk0 Hklt len.
  induction n as [n IH] using lt_wf_ind.
  intros k Hw' [Hk0 Hkle].
  destruct n as [|n].
  { (* Base: n = 0, k <= 1 *)
    simpl. simpl in Hkle.
    assert (k = 0 \/ k = 1) as [-> | ->] by lia.
    - rewrite wnaf_shift_zero. reflexivity.
    - rewrite (wnaf_shift_small_odd w 1 Hw); [reflexivity | reflexivity | lia |].
      apply Z.lt_le_trans with (m := 2 ^ 1); [lia|].
      apply Z.pow_le_mono_r; lia. }
  (* Step: n = S n, k <= 2^(S n), goal: wnaf_remainder w k (S (S n)) = 0 *)
  change (wnaf_remainder w k (S (S n))) with (wnaf_remainder w (wnaf_shift w k) (S n)).
  destruct (Z.odd k) eqn:Hodd.
  - (* k odd *)
    (* k is odd and k <= 2^(S n). Since 2^(S n) is even, k < 2^(S n), so k <= 2^(S n) - 1. *)
    assert (Hklt : k < 2 ^ Z.of_nat (S n)).
    { assert (Hev2 : Z.even (2 ^ Z.of_nat (S n)) = true).
      { rewrite pow2_succ. rewrite Z.even_mul. reflexivity. }
      assert (Hodk : Z.even k = false) by (rewrite <- Z.negb_odd, Hodd; reflexivity).
      destruct (Z.eq_dec k (2 ^ Z.of_nat (S n))); [subst; congruence | lia]. }
    destruct (Nat.le_gt_cases w (S n)) as [Hwn | Hwn].
    + (* Case w <= S n: use w-step fast-forward argument *)
      (* Get the quotient q such that wnaf_shift w k = q * 2^(w-1) *)
      destruct (wnaf_shift_odd_div w k Hw Hodd Hk0) as [q [Hq Hq0]].
      (* Bound on q *)
      assert (Hqbound : q <= k / 2 ^ Z.of_nat w + 1)
        by (apply wnaf_odd_quotient_bound with (w := w); auto).
      (* q <= 2^(S n - w) *)
      assert (Hpoww : 0 < 2 ^ Z.of_nat w) by (apply Z.pow_pos_nonneg; lia).
      assert (Hkdivw : k / 2 ^ Z.of_nat w < 2 ^ Z.of_nat (S n - w)).
      { apply Z.div_lt_upper_bound; [lia|].
        rewrite <- Z.pow_add_r by lia.
        replace (Z.of_nat w + Z.of_nat (S n - w)) with (Z.of_nat (S n)) by lia. lia. }
      assert (Hq_le : q <= 2 ^ Z.of_nat (S n - w)).
      { lia. }
      (* Fast-forward w-1 even steps: wnaf_shift w k = q * 2^(w-1) *)
      (* After w-1 even halvings, reach wnaf_remainder w q (S n - (w-1)) *)
      rewrite Hq.
      replace (Z.of_nat w - 1) with (Z.of_nat (w - 1)) by lia.
      replace (S n)%nat with ((w - 1) + (S n - (w - 1)))%nat by lia.
      rewrite wnaf_remainder_even_steps by lia.
      (* Now need: wnaf_remainder w q (S n - (w - 1)) = 0 *)
      (* S n - (w - 1) = S (n - w + 1) = S (S n - w) *)
      replace (S n - (w - 1))%nat with (S (S n - w)) by lia.
      apply IH.
      * lia.  (* S n - w < S n because w >= 2 *)
      * exact Hw.
      * split; [lia|exact Hq_le].
    + (* Case w > S n: k < 2^(S n) <= 2^(w-1), so shift is 0 *)
      assert (Hpow_le : 2 ^ Z.of_nat (S n) <= 2 ^ (Z.of_nat w - 1)).
      { apply Z.pow_le_mono_r; lia. }
      rewrite (wnaf_shift_small_odd w k Hw Hodd Hk0).
      * apply wnaf_remainder_of_zero.
      * lia.
  - (* k even *)
    rewrite wnaf_shift_of_even by exact Hodd.
    apply IH; [lia | exact Hw |].
    split.
    + apply Z.div_pos; lia.
    + transitivity (2 ^ Z.of_nat (S n) / 2).
      * apply Z.div_le_mono; lia.
      * rewrite pow2_succ. Z.div_mod_to_equations. nia.
Qed.

(** Standard correctness: needs one extra digit for carry.
    For GLV with 128-bit scalars: k < 2^128 with len = 129. *)
Theorem wnaf_correct : forall w len k,
  (1 < w)%nat ->
  (1 <= len)%nat ->
  0 <= k < 2 ^ Z.of_nat (len - 1) ->
  wsum (wnaf_digits w k len) = k.
Proof.
  intros w len k Hw Hlen [Hk0 Hklt].
  destruct len as [|n]; [lia|].
  replace (S n - 1)%nat with n in Hklt by lia.
  pose proof (wnaf_sum_remainder w (S n) k Hw Hk0) as Hsr.
  rewrite (wnaf_remainder_zero w n k Hw (conj Hk0 Hklt)) in Hsr.
  rewrite Z.mul_0_r in Hsr. lia.
Qed.

(** ** Digit bound *)

Theorem wnaf_digit_bound_single : forall w k,
  (1 < w)%nat ->
  Z.abs (wnaf_digit w k) < 2 ^ (Z.of_nat w - 1).
Proof.
  intros w k Hw. unfold wnaf_digit.
  assert (Hpow : 0 < 2 ^ Z.of_nat w) by (apply Z.pow_pos_nonneg; lia).
  assert (Hpow2 : 0 < 2 ^ (Z.of_nat w - 1)) by (apply Z.pow_pos_nonneg; lia).
  assert (H2w : 2 ^ Z.of_nat w = 2 * 2 ^ (Z.of_nat w - 1)).
  { rewrite <- Z.pow_succ_r by lia. f_equal. lia. }
  destruct (Z.odd k) eqn:Hodd; [|simpl; lia].
  set (m := k mod 2 ^ Z.of_nat w).
  assert (Hm : 0 <= m < 2 ^ Z.of_nat w) by (subst m; apply Z.mod_pos_bound; lia).
  destruct (m >=? 2 ^ (Z.of_nat w - 1)) eqn:Hge.
  - apply Z.geb_le in Hge.
    (* m is odd (k odd, m = k mod 2^w, 2^w even) *)
    assert (Hmodd : Z.odd m = true).
    { (* m is odd: k mod 2^w preserves parity since 2 | 2^w *)
      subst m.
      assert (Hkm_even : (k - k mod 2 ^ Z.of_nat w) mod 2 = 0).
      { pose proof (Z.div_mod k (2 ^ Z.of_nat w) ltac:(lia)) as Hdm.
        set (q := k / 2 ^ Z.of_nat w).
        replace (k - k mod 2 ^ Z.of_nat w) with (2 ^ Z.of_nat w * q) by lia.
        replace (2 ^ Z.of_nat w * q) with (2 ^ (Z.of_nat w - 1) * q * 2)
          by (rewrite H2w; ring).
        apply Z_mod_mult. }
      (* k ≡ m (mod 2), so odd k → odd m *)
      assert (Hmod_eq : k mod 2 = k mod 2 ^ Z.of_nat w mod 2).
      { set (mm := k mod 2 ^ Z.of_nat w) in *.
        pose proof (Z.div_mod (k - mm) 2 ltac:(lia)) as Hdm2.
        rewrite Hkm_even in Hdm2.
        assert (Hk_eq : k = mm + 2 * ((k - mm) / 2)) by lia.
        rewrite Hk_eq.
        rewrite Z.add_mod by lia.
        rewrite (Z.mul_comm 2), Z_mod_mult, Z.add_0_r.
        apply Z.mod_small.
        apply Z.mod_pos_bound. lia. }
      (* Z.odd k ↔ k mod 2 = 1 *)
      assert (Hk1 : k mod 2 = 1).
      { pose proof (Z.mod_pos_bound k 2 ltac:(lia)).
        assert (k mod 2 <> 0).
        { intro Habs. apply Zmod_divides in Habs; [|lia].
          destruct Habs as [c Hc].
          rewrite Hc, Z.odd_mul in Hodd. discriminate. }
        lia. }
      rewrite Hmod_eq in Hk1.
      set (mm := k mod 2 ^ Z.of_nat w).
      rewrite <- Z.negb_even.
      destruct (Z.even mm) eqn:He; [|reflexivity].
      exfalso. rewrite Zeven_mod in He. apply Z.eqb_eq in He.
      fold mm in Hk1. lia. }
    (* m odd and m >= 2^(w-1): m > 2^(w-1) since 2^(w-1) is even *)
    assert (m <> 2 ^ (Z.of_nat w - 1)).
    { intro Heq. rewrite Heq in Hmodd.
      rewrite Z.odd_pow in Hmodd by lia. discriminate. }
    rewrite H2w in *. lia.
  - rewrite Z.geb_leb in Hge. apply Z.leb_gt in Hge.
    assert (Hmodd : Z.odd m = true).
    { (* m is odd: k mod 2^w preserves parity since 2 | 2^w *)
      subst m.
      assert (Hkm_even : (k - k mod 2 ^ Z.of_nat w) mod 2 = 0).
      { pose proof (Z.div_mod k (2 ^ Z.of_nat w) ltac:(lia)) as Hdm.
        set (q := k / 2 ^ Z.of_nat w).
        replace (k - k mod 2 ^ Z.of_nat w) with (2 ^ Z.of_nat w * q) by lia.
        replace (2 ^ Z.of_nat w * q) with (2 ^ (Z.of_nat w - 1) * q * 2)
          by (rewrite H2w; ring).
        apply Z_mod_mult. }
      (* k ≡ m (mod 2), so odd k → odd m *)
      assert (Hmod_eq : k mod 2 = k mod 2 ^ Z.of_nat w mod 2).
      { set (mm := k mod 2 ^ Z.of_nat w) in *.
        pose proof (Z.div_mod (k - mm) 2 ltac:(lia)) as Hdm2.
        rewrite Hkm_even in Hdm2.
        assert (Hk_eq : k = mm + 2 * ((k - mm) / 2)) by lia.
        rewrite Hk_eq.
        rewrite Z.add_mod by lia.
        rewrite (Z.mul_comm 2), Z_mod_mult, Z.add_0_r.
        apply Z.mod_small.
        apply Z.mod_pos_bound. lia. }
      (* Z.odd k ↔ k mod 2 = 1 *)
      assert (Hk1 : k mod 2 = 1).
      { pose proof (Z.mod_pos_bound k 2 ltac:(lia)).
        assert (k mod 2 <> 0).
        { intro Habs. apply Zmod_divides in Habs; [|lia].
          destruct Habs as [c Hc].
          rewrite Hc, Z.odd_mul in Hodd. discriminate. }
        lia. }
      rewrite Hmod_eq in Hk1.
      set (mm := k mod 2 ^ Z.of_nat w).
      rewrite <- Z.negb_even.
      destruct (Z.even mm) eqn:He; [|reflexivity].
      exfalso. rewrite Zeven_mod in He. apply Z.eqb_eq in He.
      fold mm in Hk1. lia. }
    assert (0 < m).
    { destruct (Z.eq_dec m 0) as [->|]; [discriminate Hmodd | lia]. }
    lia.
Qed.

Theorem wnaf_digit_bound : forall w k len i d,
  (1 < w)%nat -> 0 <= k ->
  nth_error (wnaf_digits w k len) i = Some d ->
  Z.abs d < 2 ^ (Z.of_nat w - 1).
Proof.
  intros w k0 len. revert k0. induction len as [|n IH]; intros k i d Hw Hk Hnth.
  - simpl in Hnth. destruct i; discriminate.
  - simpl in Hnth. destruct i as [|i'].
    + simpl in Hnth. injection Hnth as <-. apply wnaf_digit_bound_single. exact Hw.
    + simpl in Hnth. apply IH with (k0 := wnaf_shift w k) (i := i'); auto.
      apply wnaf_shift_nonneg; auto.
Qed.

(** ** Non-adjacency *)

Lemma wnaf_digit_not_zero_odd : forall w k,
  wnaf_digit w k <> 0 -> Z.odd k = true.
Proof.
  intros w k H. unfold wnaf_digit in H.
  destruct (Z.odd k); [reflexivity | exfalso; apply H; reflexivity].
Qed.

Lemma wnaf_shift_even : forall w k,
  Z.odd k = false -> wnaf_shift w k = k / 2.
Proof.
  intros w k Hodd. unfold wnaf_shift, wnaf_digit. rewrite Hodd.
  rewrite Z.sub_0_r. reflexivity.
Qed.

Lemma shift_div_pow2_wm1 : forall w k,
  (1 < w)%nat -> wnaf_digit w k <> 0 ->
  (2 ^ Z.of_nat (w - 1) | wnaf_shift w k).
Proof.
  intros w k Hw Hd.
  assert (Hodd : Z.odd k = true) by (apply wnaf_digit_not_zero_odd in Hd; exact Hd).
  unfold wnaf_shift.
  assert (Hpow : 0 < 2 ^ Z.of_nat w) by (apply Z.pow_pos_nonneg; lia).
  assert (H2w : 2 ^ Z.of_nat w = 2 * 2 ^ Z.of_nat (w - 1)).
  { replace (Z.of_nat w) with (1 + Z.of_nat (w - 1)) by lia.
    rewrite Z.pow_add_r by lia. simpl. lia. }
  assert (Hdiv : (2 ^ Z.of_nat w | k - wnaf_digit w k)).
  { unfold wnaf_digit. rewrite Hodd.
    set (m := k mod 2 ^ Z.of_nat w).
    destruct (m >=? 2 ^ (Z.of_nat w - 1)) eqn:Hge.
    - replace (k - (m - 2 ^ Z.of_nat w)) with (k - m + 2 ^ Z.of_nat w) by lia.
      subst m. exists (k / 2 ^ Z.of_nat w + 1).
      pose proof (Z.div_mod k (2 ^ Z.of_nat w) ltac:(lia)). lia.
    - subst m. exists (k / 2 ^ Z.of_nat w).
      pose proof (Z.div_mod k (2 ^ Z.of_nat w) ltac:(lia)). lia. }
  destruct Hdiv as [q Hq]. exists q.
  rewrite H2w in Hq.
  assert (0 < 2 ^ Z.of_nat (w - 1)) by (apply Z.pow_pos_nonneg; lia).
  Z.div_mod_to_equations. nia.
Qed.

Lemma pow2_divides_even : forall m k,
  (1 <= m)%nat -> (2 ^ Z.of_nat m | k) -> Z.odd k = false.
Proof.
  intros m k Hm [q Hq].
  replace (Z.of_nat m) with (1 + Z.of_nat (m - 1)) in Hq by lia.
  rewrite Z.pow_add_r in Hq by lia. simpl in Hq.
  rewrite Hq. rewrite Z.odd_mul.
  rewrite Bool.andb_false_iff. right.
  destruct (2 ^ Z.of_nat (m - 1)); simpl; auto.
Qed.

Lemma pow2_div_half : forall m k,
  (1 <= m)%nat -> (2 ^ Z.of_nat m | k) -> (2 ^ Z.of_nat (m - 1) | k / 2).
Proof.
  intros m k Hm [q Hq]. exists q.
  replace (Z.of_nat m) with (1 + Z.of_nat (m - 1)) in Hq by lia.
  rewrite Z.pow_add_r in Hq by lia.
  rewrite Hq. simpl (2 ^ 1). rewrite Z.mul_assoc.
  assert (0 < 2 ^ Z.of_nat (m - 1)) by (apply Z.pow_pos_nonneg; lia).
  Z.div_mod_to_equations. nia.
Qed.

Lemma zero_digits_from_pow2_div : forall w len k m,
  (1 < w)%nat -> 0 <= k ->
  (1 <= m)%nat -> (2 ^ Z.of_nat m | k) ->
  forall j, (j < m)%nat -> (j < len)%nat ->
  nth j (wnaf_digits w k len) 0 = 0.
Proof.
  intros w len k m Hw Hk Hm Hdiv.
  revert k m Hk Hm Hdiv.
  induction len as [|n IHn]; intros k m Hk Hm Hdiv j Hj Hjlen.
  - lia.
  - simpl. destruct j as [|j'].
    + simpl. unfold wnaf_digit.
      rewrite (pow2_divides_even m k Hm Hdiv). reflexivity.
    + simpl. apply (IHn (wnaf_shift w k) (m - 1)%nat).
      * apply wnaf_shift_nonneg; auto.
      * lia.
      * rewrite (wnaf_shift_even w k (pow2_divides_even m k Hm Hdiv)).
        apply pow2_div_half; auto.
      * lia.
      * lia.
Qed.

Theorem wnaf_non_adjacent : forall w k len i,
  (1 < w)%nat -> 0 <= k ->
  let digits := wnaf_digits w k len in
  nth i digits 0 <> 0 ->
  forall j, (1 <= j < w)%nat ->
  (i + j < len)%nat ->
  nth (i + j) digits 0 = 0.
Proof.
  intros w k len. revert k.
  induction len as [|n IHn]; intros k i Hw Hk digits Hdi j Hj Hjlen; subst digits.
  - simpl in *. lia.
  - simpl wnaf_digits in *. destruct i as [|i'].
    + (* i = 0: nonzero digit is wnaf_digit w k *)
      simpl (nth 0 _ _) in Hdi.
      assert (Hdiv : (2 ^ Z.of_nat (w - 1) | wnaf_shift w k))
        by (apply shift_div_pow2_wm1; auto).
      replace j with (S (j - 1)) by lia.
      simpl (nth (0 + S _) _ _).
      apply (zero_digits_from_pow2_div w n (wnaf_shift w k) (w - 1)%nat);
        [exact Hw | apply wnaf_shift_nonneg; auto | lia | exact Hdiv | lia | lia].
    + (* i > 0: reduce to tail *)
      simpl (nth (S i') _ _) in Hdi.
      replace (S i' + j)%nat with (S (i' + j))%nat by lia.
      simpl (nth (S _) _ _).
      apply (IHn (wnaf_shift w k) i' Hw (wnaf_shift_nonneg w k Hw Hk)).
      exact Hdi. exact Hj. lia.
Qed.

(** ** Density bound *)

Definition count_nonzero (ds : list Z) : nat :=
  length (filter (fun d => negb (d =? 0)) ds).

Lemma wnaf_digits_length : forall w k len,
  length (wnaf_digits w k len) = len.
Proof.
  intros w k len. revert k. induction len as [|n IH]; intros k; simpl; auto.
Qed.

Lemma count_nonzero_app : forall ds1 ds2,
  count_nonzero (ds1 ++ ds2) = (count_nonzero ds1 + count_nonzero ds2)%nat.
Proof.
  intros. unfold count_nonzero. rewrite filter_app, app_length. reflexivity.
Qed.

Lemma count_nonzero_skipn_zeros : forall (m : nat) (ds : list Z),
  (forall i : nat, (i < m)%nat -> nth i ds 0%Z = 0%Z) ->
  count_nonzero ds = count_nonzero (skipn m ds).
Proof.
  induction m as [|m' IH]; intros ds Hzeros.
  - reflexivity.
  - destruct ds as [|d ds'].
    + reflexivity.
    + simpl skipn.
      assert (Hd : d = 0%Z) by (apply (Hzeros 0%nat); lia).
      subst d. unfold count_nonzero. simpl filter. simpl negb. simpl length.
      apply IH.
      intros i Hi. apply (Hzeros (S i)). lia.
Qed.

Lemma skipn_wnaf_digits : forall w k m n,
  skipn m (wnaf_digits w k (m + n)) = wnaf_digits w (wnaf_remainder w k m) n.
Proof.
  intros w k m. revert k. induction m as [|m' IH]; intros k n.
  - simpl. reflexivity.
  - simpl wnaf_digits. simpl wnaf_remainder. simpl skipn. apply IH.
Qed.

Lemma nat_div_sub : forall len w : nat,
  (1 < w)%nat -> (w <= len)%nat ->
  ((len - w) / w + 1 = len / w)%nat.
Proof.
  intros len w Hw Hle.
  pose proof (Nat.div_mod len w ltac:(lia)) as Hdm.
  assert (Hr : (len mod w < w)%nat) by (apply Nat.mod_upper_bound; lia).
  assert (Hq : (1 <= len / w)%nat) by (apply Nat.div_str_pos; lia).
  enough (H : (len / w - 1 = (len - w) / w)%nat) by lia.
  apply Nat.div_unique with (r := (len mod w)%nat).
  - exact Hr.
  - assert (w <= w * (len / w))%nat by
      (rewrite <- (Nat.mul_1_r w) at 1; apply Nat.mul_le_mono_l; exact Hq).
    rewrite Nat.mul_sub_distr_l, Nat.mul_1_r. lia.
Qed.

(** The density bound: nonzero digits are spaced at least [w] apart
    (by non-adjacency), so there are at most [len/w + 1] of them.

    An earlier version stated the bound with [w+1] in the denominator,
    but that is too tight — counterexample: w=2, k=341, len=10 gives
    digits [1;0;1;0;1;0;1;0;1;0] with 5 nonzero vs bound 10/3+1=4. *)
Theorem wnaf_density : forall w k len,
  (1 < w)%nat -> 0 <= k ->
  (count_nonzero (wnaf_digits w k len) <= Nat.div len w + 1)%nat.
Proof.
  intros w k len. revert k. induction len as [len IH] using lt_wf_ind.
  intros k Hw Hk.
  destruct len as [|n]; [unfold count_nonzero; simpl; lia|].
  simpl wnaf_digits.
  set (d := wnaf_digit w k). set (k' := wnaf_shift w k).
  assert (Hk' : 0 <= k') by (subst k'; apply wnaf_shift_nonneg; auto).
  destruct (Z.eq_dec d 0) as [Hd0|Hdne].
  - (* d = 0: count(d :: tail) = count(tail), use IH on n *)
    rewrite Hd0. unfold count_nonzero. simpl (filter _ (0 :: _)). simpl negb.
    fold (count_nonzero (wnaf_digits w k' n)).
    transitivity (n / w + 1)%nat;
      [apply IH; [lia | assumption | assumption]|].
    apply Nat.add_le_mono_r. apply Nat.Div0.div_le_mono. lia.
  - (* d <> 0: count(d :: tail) = 1 + count(tail) *)
    assert (Hdb : negb (d =? 0) = true)
      by (rewrite Bool.negb_true_iff; apply Z.eqb_neq; exact Hdne).
    unfold count_nonzero at 1. simpl (filter _ (_ :: _)). rewrite Hdb. simpl length.
    fold (count_nonzero (wnaf_digits w k' n)).
    (* By non-adjacency, the first w-1 elements of the tail are zero *)
    assert (Htail_zeros : forall i : nat, (i < w - 1)%nat -> (i < n)%nat ->
                          nth i (wnaf_digits w k' n) 0%Z = 0%Z).
    { intros i Hi Hin.
      pose proof (wnaf_non_adjacent w k (S n) 0 Hw Hk) as Hna.
      simpl wnaf_digits in Hna. fold d k' in Hna.
      specialize (Hna ltac:(simpl; exact Hdne) (S i) ltac:(lia) ltac:(lia)).
      simpl in Hna. exact Hna. }
    destruct (Nat.lt_ge_cases n (w - 1)) as [Hsmall|Hlarge].
    + (* n < w-1: all tail elements are zero, count = 0 *)
      rewrite (count_nonzero_skipn_zeros n (wnaf_digits w k' n)
                 ltac:(intros i Hi; apply Htail_zeros; lia)).
      assert (Hskip : skipn n (wnaf_digits w k' n) = @nil Z).
      { apply skipn_all2. rewrite wnaf_digits_length. lia. }
      rewrite Hskip. unfold count_nonzero. simpl. lia.
    + (* n >= w-1: skip w-1 zeros, apply IH to remainder *)
      rewrite (count_nonzero_skipn_zeros (w - 1) (wnaf_digits w k' n)
                 ltac:(intros i Hi; apply Htail_zeros; lia)).
      replace n with ((w - 1) + (n - (w - 1)))%nat at 1 by lia.
      rewrite skipn_wnaf_digits.
      assert (Hkr : 0 <= wnaf_remainder w k' (w - 1))
        by (apply wnaf_remainder_nonneg; auto).
      transitivity ((n - (w - 1)) / w + 1 + 1)%nat.
      { enough (count_nonzero (wnaf_digits w (wnaf_remainder w k' (w - 1)) (n - (w - 1)))
                <= (n - (w - 1)) / w + 1)%nat by lia.
        apply IH; [lia | assumption | assumption]. }
      enough ((n - (w - 1)) / w + 1 <= S n / w)%nat by lia.
      replace (S n) with ((n - (w - 1)) + 1 * w)%nat by lia.
      rewrite Nat.div_add by lia. lia.
Qed.

(** ** Non-negativity of weighted sum over skipn of wNAF digits.
    For k in [0, 2^(len-1)), the weighted sum of the tail of wnaf_digits w k len
    equals the remainder after n steps, which is always non-negative. *)
Lemma weighted_sum_skipn_wnaf_nonneg : forall w k len n,
  (1 < w)%nat ->
  0 <= k < 2 ^ Z.of_nat (len - 1) ->
  (n <= len)%nat ->
  0 <= weighted_sum (skipn n (wnaf_digits w k len)) 0.
Proof.
  intros w k len n Hw [Hk0 Hklt] Hnlen.
  destruct len as [|len'].
  { (* len = 0: n = 0, skipn 0 of empty = empty, weighted_sum [] 0 = 0 *)
    assert (n = 0%nat) by lia. subst n. simpl. lia. }
  replace (S len' - 1)%nat with len' in Hklt by lia.
  replace (S len') with (n + (S len' - n))%nat at 1 by lia.
  rewrite skipn_wnaf_digits.
  set (k' := wnaf_remainder w k n).
  assert (Hk' : 0 <= k') by (subst k'; apply wnaf_remainder_nonneg; auto).
  pose proof (wnaf_sum_remainder w (S len' - n) k' Hw Hk') as Hsr.
  unfold wsum in Hsr.
  assert (Hcomp : forall w0 k0 a b,
    wnaf_remainder w0 (wnaf_remainder w0 k0 a) b =
    wnaf_remainder w0 k0 (a + b)%nat).
  { clear. intros w0 k0 a. revert k0. induction a; intros; simpl; auto. }
  unfold k' in Hsr. rewrite Hcomp in Hsr.
  replace (n + (S len' - n))%nat with (S len') in Hsr by lia.
  pose proof (wnaf_remainder_zero w len' k Hw (conj Hk0 Hklt)) as Hrz.
  rewrite Hrz in Hsr.
  rewrite Z.mul_0_r, Z.add_0_r in Hsr.
  fold k' in Hsr. rewrite Hsr. exact Hk'.
Qed.

(** ** Concrete tests *)

Example wnaf_test_13 :
  wnaf_digits 4 13 5 = [-3; 0; 0; 0; 1].
Proof. vm_compute. reflexivity. Qed.

Example wnaf_test_sum_13 : wsum [-3; 0; 0; 0; 1] = 13.
Proof. vm_compute. reflexivity. Qed.

Example wnaf_test_127 : wsum (wnaf_digits 4 127 8) = 127.
Proof. vm_compute. reflexivity. Qed.

Example wnaf_test_255 : wsum (wnaf_digits 4 255 9) = 255.
Proof. vm_compute. reflexivity. Qed.

Example wnaf_test_1000 : wsum (wnaf_digits 4 1000 11) = 1000.
Proof. vm_compute. reflexivity. Qed.
