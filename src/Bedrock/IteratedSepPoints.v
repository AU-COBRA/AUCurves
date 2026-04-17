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
    - simpl. rewrite IH.
      (* Goal:
           op (op b (nat_scalar_mul k b))
              (op (plain_sum rest) (scaled_sum_from (S k) rest))
         = op (op b (plain_sum rest))
              (op (nat_scalar_mul k b) (scaled_sum_from k rest)). *)
      rewrite IH.
      (* Now rhs' = op (op b (plain_sum rest))
                       (op (nat_scalar_mul k b)
                           (op (plain_sum rest) (scaled_sum_from k rest))). *)
      (* Use assoc + comm to pull the structure together.  Both sides
         are a five-way sum of:
           b, nat_scalar_mul k b, plain_sum rest, plain_sum rest, scaled_sum_from k rest.
         Reduce both sides to a canonical associated-right form. *)
      repeat rewrite op_assoc.
      f_equal.
      rewrite (op_comm (nat_scalar_mul k b) (plain_sum rest)).
      repeat rewrite op_assoc.
      f_equal.
      rewrite (op_comm (plain_sum rest) (nat_scalar_mul k b)).
      repeat rewrite op_assoc.
      reflexivity.
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
    - simpl. rewrite IH. cbn [rs_step fst snd].
      f_equal.
      + (* First component: op (plain_sum rest) b = plain_sum (b :: rest). *)
        simpl plain_sum. apply op_comm.
      + (* Second component:
           op (scaled_sum rest) (op (plain_sum rest) b) = scaled_sum (b :: rest). *)
        unfold scaled_sum. simpl scaled_sum_from.
        rewrite nat_scalar_mul_succ, nat_scalar_mul_zero, op_zero_r.
        rewrite scaled_sum_from_S.
        (* rhs = op b (op (plain_sum rest) (scaled_sum_from 1 rest)).
           lhs = op (scaled_sum_from 1 rest) (op (plain_sum rest) b). *)
        rewrite (op_comm (plain_sum rest) b).
        repeat rewrite op_assoc.
        rewrite (op_comm (scaled_sum_from 1 rest) b).
        repeat rewrite op_assoc.
        f_equal.
        apply op_comm.
  Qed.

  (** Convenience: the value the bedrock2 loop will place in
      [window_sum] at exit equals [scaled_sum] of the bucket list. *)
  Corollary running_fold_snd (bs : list G) :
    snd (fold_right rs_step (zero, zero) bs) = scaled_sum bs.
  Proof. rewrite running_fold_invariant. reflexivity. Qed.

End RunningSum.

(* =================================================================== *)
(** * Part 2: bridge to BLS12_MSM.reduce_buckets.                        *)
(*                                                                      *)
(*    [BLS12_MSM.reduce_buckets] is written with a left-fold over        *)
(*    [rev buckets], which is equivalent (for our two-register          *)
(*    update) to a [fold_right] over [buckets].  This section closes   *)
(*    that fold-shape gap so the WP proof can cite                      *)
(*    [scaled_sum]-style invariants directly.                           *)
(* =================================================================== *)

Require Import Bedrock.BLS12_MSM.

Section BLS12MSMBridge.
  Context (G1 : Type).
  Context (g1_identity : G1).
  Context (g1_add : G1 -> G1 -> G1).
  Hypothesis g1_add_assoc : forall a b c, g1_add (g1_add a b) c = g1_add a (g1_add b c).
  Hypothesis g1_add_comm  : forall a b, g1_add a b = g1_add b a.
  Hypothesis g1_add_identity_l : forall a, g1_add g1_identity a = a.

  (** The inner [go] fixpoint inside [reduce_buckets] unfolded as a
      [fold_left] over [rev buckets]. *)
  Lemma reduce_buckets_as_fold (bs : list G1) :
    reduce_buckets G1 g1_identity g1_add bs
    = snd (fold_left
             (fun p b =>
                let r' := g1_add (fst p) b in
                (r', g1_add (snd p) r'))
             (rev bs)
             (g1_identity, g1_identity)).
  Proof.
    unfold reduce_buckets.
    (* Generalize the initial state to arbitrary (r, a), which lets us
       induct on the list argument of the local [fix go]. *)
    assert (Hgo: forall rs r a,
      (fix go (bs0 : list G1) (running acc : G1) {struct bs0} : G1 :=
         match bs0 with
         | [] => acc
         | b :: rest =>
             let running' := g1_add running b in
             let acc' := g1_add acc running' in
             go rest running' acc'
         end) rs r a
      = snd (fold_left (fun p b =>
                          let r' := g1_add (fst p) b in
                          (r', g1_add (snd p) r'))
                       rs (r, a))).
    { intros rs. induction rs as [|b rest IH]; intros r a.
      - reflexivity.
      - simpl. apply IH. }
    apply Hgo.
  Qed.

  (** [fold_left (flip f) (rev xs) z = fold_right f z xs]. *)
  Lemma fold_left_rev_right_rs (bs : list G1) (z : G1 * G1) :
    fold_left
      (fun p b =>
         let r' := g1_add (fst p) b in
         (r', g1_add (snd p) r'))
      (rev bs) z
    = fold_right (rs_step G1 g1_add) z bs.
  Proof.
    induction bs as [|b rest IH]; simpl.
    - reflexivity.
    - rewrite fold_left_app. simpl. rewrite IH.
      reflexivity.
  Qed.

  (** Headline bridge: [reduce_buckets] equals [scaled_sum]. *)
  Theorem reduce_buckets_eq_scaled_sum (bs : list G1) :
    reduce_buckets G1 g1_identity g1_add bs
    = scaled_sum G1 g1_identity g1_add bs.
  Proof.
    rewrite reduce_buckets_as_fold.
    rewrite fold_left_rev_right_rs.
    rewrite running_fold_snd; auto.
  Qed.

End BLS12MSMBridge.

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
    - (* bedrock2 returns [A * (P * B)]; we want [(A * P) * B]. *)
      cancel.
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
    (* Apply [split_at] to the already-updated list, then rewrite the
       [firstn/skipn/hd] facts to collapse back to [firstn n xs] /
       [skipn (S n) xs] / [v'] respectively. *)
    set (xs' := firstn n xs ++ v' :: skipn (S n) xs).
    assert (Hfn : length (firstn n xs) = n).
    { rewrite List.firstn_length. Lia.lia. }
    assert (Hn' : (n < length xs')%nat).
    { unfold xs'. rewrite List.app_length. simpl.
      rewrite List.skipn_length. Lia.lia. }
    assert (Hfirstn : firstn n xs' = firstn n xs).
    { unfold xs'. rewrite List.firstn_app, Hfn.
      replace (n - n)%nat with 0%nat by Lia.lia.
      rewrite List.firstn_O. rewrite List.app_nil_r.
      rewrite List.firstn_firstn. rewrite Nat.min_id. reflexivity. }
    assert (Hskn_full : skipn n xs' = v' :: skipn (S n) xs).
    { unfold xs'. rewrite List.skipn_app, Hfn.
      replace (n - n)%nat with 0%nat by Lia.lia.
      rewrite (List.skipn_all2 (firstn n xs)) by Lia.lia.
      simpl. reflexivity. }
    assert (Hskipn : skipn (S n) xs' = skipn (S n) xs).
    { change (S n) with (1 + n)%nat.
      rewrite <- List.skipn_skipn. rewrite Hskn_full. reflexivity. }
    pose proof (PointArray_split_at start xs' n Hn') as Hsplit.
    rewrite Hfirstn, Hskipn, Hskn_full in Hsplit. simpl hd in Hsplit.
    symmetry. exact Hsplit.
  Qed.

End ArrayOfPoints.
