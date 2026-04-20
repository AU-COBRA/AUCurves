(** * IteratedSepPoints.v

    Shared infrastructure for the MSM WP proof
    ([BLS12_MSM.v]) and future bucketed-algorithm proofs (e.g. G2 MSM
    for batched KZG verification, Pedersen multiscalar).

    Split into three sections:

    - [RunningSum]: a pure Stdlib algebraic identity that says the
      two-register running-sum loop used in Pippenger's reduction
      computes [fold_right] of [(i+1) * bs[i]].  Abstract over any
      commutative monoid; instantiated below for the G1 context
      used in [BLS12_MSM.v].

    - [BLS12MSMBridge]: specialises the algebraic identity to
      [BLS12_MSM.reduce_buckets], so the WP proof can rewrite
      the spec-level computation into a shape convenient for the
      loop invariant.

    - [ArrayOfPoints]: wraps bedrock2's [array] predicate into a
      named [PointArray] for a caller-supplied "one point at
      address [p]" predicate, and derives [split_at] / [update_at]
      lemmas as thin rewrites over [array_index_nat_inbounds] and
      [array_append].  These are the workhorses for proving the
      inner distribution loop (single-cell mutation in a bucket
      array) and the running-sum loop.

    None of the lemmas here are specific to BLS12; the [RunningSum]
    and [ArrayOfPoints] sections are fully reusable.
*)

From Stdlib Require Import ZArith List PeanoNat.
Import ListNotations.
Local Open Scope Z_scope.

(* =================================================================== *)
(** * Part 1: running-sum algebraic identity (pure Stdlib).              *)
(* =================================================================== *)

Section RunningSum.
  (** Abstract commutative monoid. *)
  Context (G : Type).
  Context (zero : G) (op : G -> G -> G).
  Hypothesis op_assoc : forall a b c, op (op a b) c = op a (op b c).
  Hypothesis op_comm  : forall a b, op a b = op b a.
  Hypothesis op_zero_l : forall a, op zero a = a.

  Lemma op_zero_r : forall a, op a zero = a.
  Proof. intros a. rewrite op_comm. apply op_zero_l. Qed.

  (** 4-term rearrangement: [(a+b)+(c+d) = (a+c)+(b+d)].  Used several times below. *)
  Lemma op_4_swap a b c d : op (op a b) (op c d) = op (op a c) (op b d).
  Proof.
    rewrite op_assoc.
    rewrite <- (op_assoc b c d).
    rewrite (op_comm b c).
    rewrite (op_assoc c b d).
    rewrite <- op_assoc.
    reflexivity.
  Qed.

  (** [nat_scalar_mul n g] is [n·g] = [op g (op g (... g))] ([n] copies). *)
  Fixpoint nat_scalar_mul (n : nat) (g : G) : G :=
    match n with
    | O    => zero
    | S k  => op g (nat_scalar_mul k g)
    end.

  (** Plain sum of a list (left-associated with [op]). *)
  Fixpoint plain_sum (bs : list G) : G :=
    match bs with
    | []     => zero
    | b :: r => op b (plain_sum r)
    end.

  (** Scaled sum starting the coefficient at [start]:
      [scaled_sum_from k [b0; b1; ...; b_{n-1}] = k·b0 + (k+1)·b1 + ...]. *)
  Fixpoint scaled_sum_from (start : nat) (bs : list G) : G :=
    match bs with
    | []     => zero
    | b :: r => op (nat_scalar_mul start b) (scaled_sum_from (S start) r)
    end.

  Definition scaled_sum (bs : list G) : G := scaled_sum_from 1 bs.

  (** Helpers. *)
  Lemma nat_scalar_mul_succ n g :
    nat_scalar_mul (S n) g = op g (nat_scalar_mul n g).
  Proof. reflexivity. Qed.

  Lemma nat_scalar_mul_zero g : nat_scalar_mul 0 g = zero.
  Proof. reflexivity. Qed.

  (** Core algebraic step: bumping the starting coefficient by one
      adds exactly one copy of the plain sum. *)
  Lemma scaled_sum_from_S k bs :
    scaled_sum_from (S k) bs = op (plain_sum bs) (scaled_sum_from k bs).
  Proof.
    revert k. induction bs as [|b rest IH]; intros k.
    - simpl. rewrite op_zero_l. reflexivity.
    - simpl plain_sum. simpl scaled_sum_from. simpl nat_scalar_mul.
      rewrite (IH (S k)).
      (* LHS: op (op b (nat_scalar_mul k b)) (op (plain_sum rest) (scaled_sum_from (S k) rest))
         RHS: op (op b (plain_sum rest))     (op (nat_scalar_mul k b) (scaled_sum_from (S k) rest)).
         Both are (b + k·b + psum rest + s_{S k} rest) up to rearrangement. *)
      apply op_4_swap.
  Qed.

  (** The two-register update applied by the running-sum loop body. *)
  Definition rs_step (b : G) (p : G * G) : G * G :=
    let r' := op (fst p) b in
    (r', op (snd p) r').

  (** The core invariant: running-sum [fold_right] computes exactly
      [(plain_sum, scaled_sum)]. *)
  Theorem running_fold_invariant (bs : list G) :
    fold_right rs_step (zero, zero) bs
    = (plain_sum bs, scaled_sum bs).
  Proof.
    induction bs as [|b rest IH].
    - reflexivity.
    - cbn [fold_right]. rewrite IH.
      unfold rs_step. cbn [fst snd].
      (* Goal: (op (plain_sum rest) b, op (scaled_sum rest) (op (plain_sum rest) b))
             = (plain_sum (b :: rest), scaled_sum (b :: rest)). *)
      f_equal.
      + (* First component. *)
        simpl plain_sum. apply op_comm.
      + (* Second component:
           Goal: op (scaled_sum rest) (op (plain_sum rest) b) = scaled_sum (b :: rest). *)
        unfold scaled_sum. simpl.
        (* After simpl:
             op (scaled_sum_from 1 rest) (op (plain_sum rest) b)
             = op (op b zero) (scaled_sum_from 2 rest). *)
        rewrite op_zero_r.
        rewrite (scaled_sum_from_S 1 rest).
        (* Goal: op (scaled_sum_from 1 rest) (op (plain_sum rest) b)
               = op b (op (plain_sum rest) (scaled_sum_from 1 rest)) *)
        set (s := scaled_sum_from 1 rest).
        set (p := plain_sum rest).
        (* Goal: op s (op p b) = op b (op p s). *)
        rewrite (op_comm p b).                 (* op s (op b p) *)
        rewrite (op_comm s (op b p)).          (* op (op b p) s *)
        rewrite op_assoc.                      (* op b (op p s) *)
        reflexivity.
  Qed.

  (** Convenience: the value the bedrock2 loop will place in
      [window_sum] at exit equals [scaled_sum] of the bucket list. *)
  Corollary running_fold_snd (bs : list G) :
    snd (fold_right rs_step (zero, zero) bs) = scaled_sum bs.
  Proof. rewrite running_fold_invariant. reflexivity. Qed.

End RunningSum.

(* =================================================================== *)
(** * Part 2: [fold_left (rev)] ↔ [fold_right] shape gap.                *)
(*                                                                      *)
(*    [BLS12_MSM.reduce_buckets] is written with a left-fold over        *)
(*    [rev buckets].  This is equivalent (for our two-register update)  *)
(*    to a [fold_right] over [buckets].  This lemma closes the shape    *)
(*    gap so the caller can rewrite a left-fold expression into the     *)
(*    [running_fold_invariant] shape above without importing BLS12_MSM. *)
(* =================================================================== *)

Section FoldReshape.
  Context (G1 : Type).
  Context (g1_add : G1 -> G1 -> G1).

  (** [fold_left (flip f) (rev xs) z = fold_right f z xs]. *)
  Lemma fold_left_rev_right_rs (bs : list G1) (z : G1 * G1) :
    fold_left
      (fun p b =>
         let r' := g1_add (fst p) b in
         (r', g1_add (snd p) r'))
      (rev bs) z
    = fold_right (rs_step G1 g1_add) z bs.
  Proof.
    induction bs as [|b rest IH].
    - reflexivity.
    - change (rev (b :: rest)) with (rev rest ++ [b]).
      rewrite fold_left_app. rewrite IH.
      reflexivity.
  Qed.

End FoldReshape.

(* =================================================================== *)
(** * Part 3: bedrock2 [array]-of-points wrapper + update-at lemma.      *)
(* =================================================================== *)

Require Import coqutil.Map.Interface coqutil.Word.Interface.
Require Import coqutil.Byte.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic bedrock2.Lift1Prop.
Require Import bedrock2.Array.

Section ArrayOfPoints.
  Context {width : Z} {word : word.word width} {word_ok : word.ok word}.
  Context {mem : map.map word Byte.byte} {mem_ok : map.ok mem}.
  Context {T : Type} (point : word -> T -> mem -> Prop) (size : word).
  Context {default : T}.

  (** Array of equal-sized records at consecutive offsets. *)
  Definition PointArray (start : word) (xs : list T) : mem -> Prop :=
    array point size start xs.

  Local Open Scope sep_scope.

  (** Split off the [n]-th cell, when [n < length xs]. *)
  Lemma PointArray_split_at start xs n (H : (n < length xs)%nat) :
    iff1 (PointArray start xs)
         (PointArray start (firstn n xs) *
          point (word.add start (word.of_Z (word.unsigned size * Z.of_nat n)))
                (hd default (skipn n xs)) *
          PointArray (word.add (word.add start
                                 (word.of_Z (word.unsigned size * Z.of_nat n)))
                               size)
                     (skipn (S n) xs)).
  Proof.
    unfold PointArray.
    etransitivity.
    - apply (array_index_nat_inbounds (default:=default) _ _ xs start n H).
    - (* bedrock2 returns [A * (P * B)]; our statement has [(A * P) * B]. *)
      symmetry. apply sep_assoc.
  Qed.

  (** If the [n]-th cell was updated in-place, re-merge the array. *)
  Lemma PointArray_update_at start xs n v' (H : (n < length xs)%nat) :
    iff1 (PointArray start (firstn n xs) *
          point (word.add start (word.of_Z (word.unsigned size * Z.of_nat n))) v' *
          PointArray (word.add (word.add start
                                 (word.of_Z (word.unsigned size * Z.of_nat n)))
                               size)
                     (skipn (S n) xs))
         (PointArray start
            (firstn n xs ++ v' :: skipn (S n) xs)).
  Proof.
    unfold PointArray.
    symmetry.
    (* Goal: iff1 (array start (firstn n xs ++ v' :: skipn (S n) xs)) (split_form). *)
    rewrite array_append.
    (* The middle offset from [array_append] is
         start + size * length (firstn n xs).
       Replace [length (firstn n xs)] with [n] using [n < length xs]. *)
    replace (length (firstn n xs)) with n
      by (symmetry; apply firstn_length_le; Lia.lia).
    rewrite array_cons.
    (* Now the RHS of [iff1] is [A * (P * B)], while the LHS we want is [(A * P) * B]. *)
    symmetry. apply sep_assoc.
  Qed.

End ArrayOfPoints.
