Require Import Crypto.Algebra.Hierarchy.
Require Import ZArith Znumtheory.
Require Import Lia.
Require Import Logic.
From Coqprime Require Import Pmod. 
Section RepSquare.
Context {T op id} {monoid: @monoid T (@eq T) op id}.

Local Open Scope nat_scope.

Local Infix "*" := op.
Local Infix "=" := eq.

Fixpoint pow_pos (x : T) (n : positive) : T :=
match n with
    | xH => x
    | xO m => (pow_pos (x * x) m)
    | xI m => (pow_pos (x * x) m) * x
end.

Notation "x ^ n" := (pow_pos x n).

Fixpoint pow_nat (x : T) (n : nat) : T :=
match n with
    | O => id
    | S m => (pow_nat x m) * x
end.

Notation "x ^' n" := (pow_nat x n) (at level 80).

Ltac move_operand_left y H := 
  repeat (rewrite <- (associative y _ _); try (rewrite H; repeat rewrite associative)); repeat rewrite associative; try rewrite H.

Ltac apply_comm x y H := repeat rewrite associative; move_operand_left y H; repeat rewrite <- associative;
match goal with
  | |- (x * ?n1) = (x * ?n2) => assert (n1 = n2) as Haux by (apply_comm x y H); rewrite Haux; auto
  | _ => auto
end.

Lemma pow_nat_plus: forall x (n m : nat), (x ^' (n + m)) = (x ^' n) * (x ^' m).
Proof.
    intros x n m. induction m as [| m' IHm'].
        - rewrite right_identity; auto with zarith.
        - simpl; rewrite associative; rewrite <- IHm'; rewrite Nat.add_succ_r; auto.
Qed.

Lemma pow_pos_odd: forall x n, x ^ (n~1) = x^(n~0) * x.
Proof. auto. Qed.

Lemma pow_pos_ev: forall x n, (x^ (n ~0) = x ^ n * x ^ n) /\ x ^ n * x = x * x ^ n.
Proof.
    intros x n; generalize dependent x; simpl; induction n as [n' IHn'|n' IHn'|]; intros x; split; simpl; auto;
    repeat rewrite (proj1 (IHn' (_))); apply_comm x (x ^ n') (proj2 (IHn' x)).
Qed.

Lemma pow_pos_com: forall x n, x * x ^ n = x ^ n * x.
Proof. intros x n; symmetry; apply (proj2 (pow_pos_ev x n)). Qed.

Lemma pow_pos_distr: forall x n, (x * x) ^ n = x ^ n * x ^ n.
Proof.
    intros x n; pose proof pow_pos_ev as H; induction n as [n' IHn' |n' IHn' |]; try destruct (H (x * x) n') as [H0 _]; auto.
        - repeat rewrite pow_pos_odd; destruct (H x n') as [H1 _]; repeat rewrite H0; rewrite H1;
          repeat rewrite IHn'; apply_comm x (x ^ n') (pow_pos_com x n').
Qed.

Lemma repeated_square_correct: forall x n, pow_pos x n = pow_nat x (Pos.to_nat n).
Proof.
    intros x n; induction n as [n' IHn| |].
        - rewrite Pos2Nat.inj_xI; simpl; rewrite pow_nat_plus;
          rewrite Nat.add_0_r; rewrite <- IHn; rewrite pow_pos_distr; auto.
        - rewrite Pos2Nat.inj_xO; simpl; rewrite Nat.add_0_r; rewrite pow_nat_plus;
          rewrite <- IHn; apply pow_pos_distr.
        - simpl; rewrite left_identity; auto. 
Qed.

End RepSquare.