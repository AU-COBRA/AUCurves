(** * wNAF Shamir scalar multiplication -- Gallina spec + correctness. *)

From Stdlib Require Import ZArith Lia List.
Require Import Bedrock.Field.Synthesis.Examples.wNAF.
Import ListNotations.
Local Open Scope Z_scope.

Section WNAFShamir.
  Context {G : Type}.
  Context {add : G -> G -> G} {zero : G} {opp : G -> G}.
  Context {mul : Z -> G -> G}.

  Context (add_assoc : forall a b c, add a (add b c) = add (add a b) c).
  Context (add_comm : forall a b, add a b = add b a).
  Context (add_zero_r : forall a, add a zero = a).
  Context (add_zero_l : forall a, add zero a = a).
  Context (mul_0 : forall P, mul 0 P = zero).
  Context (mul_1 : forall P, mul 1 P = P).
  Context (mul_add : forall a b P, mul (a + b) P = add (mul a P) (mul b P)).
  Context (mul_opp : forall n P, mul (-n) P = opp (mul n P)).
  Context (mul_mul : forall a b P, mul a (mul b P) = mul (a * b) P).
  Context (mul_distr_add : forall n P Q, mul n (add P Q) = add (mul n P) (mul n Q)).
  Context (mul_zero_r : forall n, mul n zero = zero).

  Declare Scope G_scope.
  Local Infix "+" := add : G_scope.
  Local Infix "*" := mul : G_scope.
  Local Open Scope G_scope.

  Definition wnaf_cond_add (d : Z) (P : G) (acc : G) : G :=
    if d =? 0 then acc else acc + d * P.

  Fixpoint wnaf_shamir_loop (ds1 ds2 : list Z)
           (P Phi : G) (acc : G) (pos : nat) : G :=
    match pos with
    | O => acc
    | S n =>
      let acc' := acc + acc in
      let d1 := nth n ds1 0 in
      let acc'' := wnaf_cond_add d1 P acc' in
      let d2 := nth n ds2 0 in
      wnaf_shamir_loop ds1 ds2 P Phi (wnaf_cond_add d2 Phi acc'') n
    end.

  Definition wnaf_shamir (w len : nat) (k1 k2 : Z) (P Phi : G) : G :=
    wnaf_shamir_loop (wnaf_digits w k1 (S len)) (wnaf_digits w k2 (S len))
                     P Phi zero (S len).

  (* -- Helpers -- *)

  Lemma wnaf_cond_add_spec d P acc :
    wnaf_cond_add d P acc = acc + d * P.
  Proof.
    unfold wnaf_cond_add. destruct (d =? 0) eqn:E.
    - apply Z.eqb_eq in E. subst. rewrite mul_0, add_zero_r. reflexivity.
    - reflexivity.
  Qed.

  Lemma mul_2_double n P : (2 * n)%Z * P = (n * P) + (n * P).
  Proof. replace (2*n)%Z with (n+n)%Z by lia. rewrite mul_add. reflexivity. Qed.

  Lemma weighted_sum_app : forall ds1 ds2 p,
    weighted_sum (ds1 ++ ds2) p =
    (weighted_sum ds1 p + weighted_sum ds2 (p + length ds1))%Z.
  Proof.
    induction ds1 as [|d rest IH]; intros ds2 p; simpl.
    - replace (p + 0)%nat with p by lia. lia.
    - rewrite IH. replace (S p + length rest)%nat with (p + S (length rest))%nat by lia.
      lia.
  Qed.

  Lemma firstn_succ_app : forall {A} n (ds : list A) d,
    (n < length ds)%nat ->
    firstn (S n) ds = firstn n ds ++ [nth n ds d].
  Proof.
    intros A n. induction n; intros [|x rest] d Hlen; simpl in *; try lia.
    - reflexivity.
    - f_equal. apply IHn. lia.
  Qed.

  Lemma weighted_sum_firstn_succ ds n :
    weighted_sum (firstn (S n) ds) 0 =
    (weighted_sum (firstn n ds) 0 + nth n ds 0 * 2 ^ Z.of_nat n)%Z.
  Proof.
    destruct (Nat.lt_ge_cases n (length ds)) as [Hlt|Hge].
    - rewrite (firstn_succ_app n ds 0 Hlt).
      rewrite weighted_sum_app. simpl.
      rewrite firstn_length_le by lia. lia.
    - rewrite !firstn_all2 by lia.
      rewrite nth_overflow by lia. lia.
  Qed.

  Lemma wnaf_digits_length w k len : length (wnaf_digits w k len) = len.
  Proof. revert k. induction len; simpl; auto. Qed.

  (* -- Loop invariant -- *)

  Lemma loop_inv ds1 ds2 P Phi acc pos :
    wnaf_shamir_loop ds1 ds2 P Phi acc pos =
      (2 ^ Z.of_nat pos)%Z * acc
      + (weighted_sum (firstn pos ds1) 0)%Z * P
      + (weighted_sum (firstn pos ds2) 0)%Z * Phi.
  Proof.
    revert acc. induction pos as [|n IH]; intros acc.
    - simpl. rewrite !mul_0, !add_zero_r, mul_1. reflexivity.
    - simpl wnaf_shamir_loop. rewrite !wnaf_cond_add_spec. rewrite IH.
      set (d1 := nth n ds1 0). set (d2 := nth n ds2 0).
      set (w1 := weighted_sum (firstn n ds1) 0).
      set (w2 := weighted_sum (firstn n ds2) 0).
      set (p := (2 ^ Z.of_nat n)%Z).
      (* Distribute: p * ((acc+acc) + d1*P + d2*Phi) *)
      rewrite !mul_distr_add.
      (* p*acc + p*acc = (2*p)*acc *)
      rewrite <- mul_2_double.
      replace (2 * p)%Z with (2 ^ Z.of_nat (S n))%Z
        by (subst p; rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; lia).
      (* p * (d1 * P) = (p * d1) * P *)
      rewrite !mul_mul.
      (* Rewrite firstn (S n) *)
      rewrite !weighted_sum_firstn_succ.
      subst d1 d2 w1 w2 p.
      replace (weighted_sum (firstn n ds1) 0 + nth n ds1 0 * 2 ^ Z.of_nat n)%Z
        with (2 ^ Z.of_nat n * nth n ds1 0 + weighted_sum (firstn n ds1) 0)%Z by lia.
      replace (weighted_sum (firstn n ds2) 0 + nth n ds2 0 * 2 ^ Z.of_nat n)%Z
        with (2 ^ Z.of_nat n * nth n ds2 0 + weighted_sum (firstn n ds2) 0)%Z by lia.
      rewrite !mul_add.
      (* AC rearrangement of 5 group terms *)
      rewrite <- !add_assoc.
      rewrite (add_assoc (mul (2 ^ Z.of_nat n * nth n ds2 0) Phi)
                         (mul (weighted_sum (firstn n ds1) 0) P)
                         (mul (weighted_sum (firstn n ds2) 0) Phi)).
      rewrite (add_comm (mul (2 ^ Z.of_nat n * nth n ds2 0) Phi)
                        (mul (weighted_sum (firstn n ds1) 0) P)).
      rewrite <- (add_assoc (mul (weighted_sum (firstn n ds1) 0) P)
                            (mul (2 ^ Z.of_nat n * nth n ds2 0) Phi)
                            (mul (weighted_sum (firstn n ds2) 0) Phi)).
      reflexivity.
  Qed.

  (* -- Main theorem -- *)

  Theorem wnaf_shamir_correct w len k1 k2 P Phi :
    (1 < w)%nat ->
    0 <= k1 < 2 ^ Z.of_nat len ->
    0 <= k2 < 2 ^ Z.of_nat len ->
    wnaf_shamir w len k1 k2 P Phi = (k1 * P) + (k2 * Phi).
  Proof.
    intros Hw Hk1 Hk2. unfold wnaf_shamir. rewrite loop_inv.
    (* 2^(S len) * zero = zero *)
    rewrite mul_zero_r, add_zero_l.
    (* firstn (S len) (wnaf_digits _ _ (S len)) = wnaf_digits ... *)
    rewrite !firstn_all2 by (rewrite wnaf_digits_length; lia).
    (* wsum(digits) = k *)
    pose proof (wnaf_correct w (S len) k1 Hw ltac:(lia)
      ltac:(replace (S len - 1)%nat with len by lia; exact Hk1)) as E1.
    pose proof (wnaf_correct w (S len) k2 Hw ltac:(lia)
      ltac:(replace (S len - 1)%nat with len by lia; exact Hk2)) as E2.
    unfold wsum in E1, E2. rewrite E1, E2. reflexivity.
  Qed.

End WNAFShamir.
