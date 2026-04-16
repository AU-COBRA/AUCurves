(** * Single-scalar wNAF scalar multiplication spec.

    For curves without GLV endomorphism (BN254, BN256, P-256, etc.),
    wNAF provides ~1.4x speedup over binary scalar multiplication by
    reducing the number of non-zero digits (and hence point additions).

    Loop invariant: acc = scmul(weighted_sum(skipn n dk)) P
    where dk is the wNAF digit expansion of scalar k.

    This is simpler than the GLV variant (wNAF_ScalarMult.v) which
    uses two scalars and two points simultaneously. *)

From Stdlib Require Import ZArith Lia List.
Require Import Bedrock.Field.Synthesis.Examples.wNAF.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Horner evaluation for single scalar *)

Section SingleScalar.
  Context {G : Type}.
  Context (zero : G).
  Context (add : G -> G -> G).
  Context (add_id_r : forall P, add P zero = P).
  Context (add_id_l : forall P, add zero P = P).
  Context (add_assoc : forall P Q R, add P (add Q R) = add (add P Q) R).
  Context (add_comm : forall P Q, add P Q = add Q P).

  (** Scalar multiplication by repeated addition *)
  Fixpoint scmul_single (n : nat) (P : G) : G :=
    match n with
    | O => zero
    | S m => add P (scmul_single m P)
    end.

  Lemma scmul_single_0 : forall P, scmul_single 0 P = zero.
  Proof. reflexivity. Qed.

  Lemma scmul_single_1 : forall P, scmul_single 1 P = P.
  Proof. intros. simpl. apply add_id_r. Qed.

  Lemma scmul_single_add : forall a b P,
    scmul_single (a + b) P = add (scmul_single a P) (scmul_single b P).
  Proof.
    induction a as [|a' IH]; intros b P.
    - simpl. symmetry. apply add_id_l.
    - simpl. rewrite IH. apply add_assoc.
  Qed.

  (** Horner step for single scalar:
      weighted_sum(skipn n dk) = nth n dk + 2 * weighted_sum(skipn (S n) dk) *)
  Lemma skipn_cons_nth_local {A} (n : nat) (l : list A) (d : A) :
    (n < length l)%nat ->
    skipn n l = nth n l d :: skipn (S n) l.
  Proof.
    revert l. induction n as [|n' IH]; intros l Hlt.
    - destruct l; simpl in *; [lia|reflexivity].
    - destruct l as [|x rest]; simpl in *; [lia|].
      apply IH. lia.
  Qed.

  Lemma single_horner_step : forall dk n,
    (n < length dk)%nat ->
    weighted_sum (skipn n dk) 0 =
      nth n dk 0 + 2 * weighted_sum (skipn (S n) dk) 0.
  Proof.
    intros dk n Hlt.
    rewrite (skipn_cons_nth_local n dk 0 Hlt).
    unfold weighted_sum at 1. fold weighted_sum.
    rewrite weighted_sum_succ. lia.
  Qed.

  (** Double of accumulator: add acc acc = scmul(2*ws) P *)
  Lemma scmul_double : forall n P,
    add (scmul_single n P) (scmul_single n P) = scmul_single (n + n) P.
  Proof. intros. rewrite scmul_single_add. reflexivity. Qed.

End SingleScalar.

(** ** digit_point for single table *)

Section DigitPoint.
  Context {G : Type}.
  Context (zero : G).
  Context (add : G -> G -> G).
  Context (neg : G -> G).

  (** Lookup table: [1P, 3P, 5P, 7P] for window w=4 *)
  Context (table : list G).
  Context (Htable_len : length table = 4%nat).

  (** Table entry for positive odd index: table[(d-1)/2] = d*P *)
  Context (P : G).
  Context (Htable_correct : forall i, (i < 4)%nat ->
    nth i table zero = Nat.iter (2*i+1) (add P) zero).

  (** digit_point: given signed digit d, return d*P using table + negation *)
  Definition digit_point_single (d : Z) : G :=
    if d =? 0 then zero
    else
      let abs_d := Z.abs d in
      let idx := Z.to_nat ((abs_d - 1) / 2) in
      let entry := nth idx table zero in
      if d <? 0 then neg entry else entry.

End DigitPoint.
