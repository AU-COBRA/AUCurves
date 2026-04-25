(** * BLS12_MSM_BucketSplit: L3 sep-logic helpers for Phase B

    Extract / re-merge one bucket triple (at index [d]) and one point
    triple (at index [n]) out of the L3 [msm_bls12_distribute_wp]
    invariant sep.  Companion to [BLS12_MSM_WindowBridge].

    Each lemma is parametric over the single-cell predicate [point]
    (instantiated at [FElem (Some tight_bounds)] in [BLS12_MSM.v]) and
    the cell [size] (instantiated at [word.of_Z felem_size_in_bytes]).
    The [ScalarsArray] component shows up as an opaque [Sc] frame
    since Phase B does not touch it.

    The post-split sep keeps each triple contiguous (bucket / points)
    so [seprewrite_in PointArray_update_at Hm] matches syntactically. *)

From Stdlib Require Import ZArith List Lia.
Require Import coqutil.Word.Interface.
Require Import coqutil.Map.Interface.
Require Import coqutil.Byte.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Array.
Require Import Bedrock.IteratedSepPoints.

Import ListNotations.
Local Open Scope Z_scope.

(** Keep [firstn] / [skipn] opaque so [seprewrite_in] matches
    syntactically instead of unfolding the fixpoint bodies. *)
Arguments firstn : simpl never.
Arguments skipn  : simpl never.

Section L3BucketSplit.
  Context {width : Z} {word : word.word width} {word_ok : word.ok word}.
  Context {mem : map.map word Byte.byte} {mem_ok : map.ok mem}.
  Context {T : Type} (point : word -> T -> mem -> Prop) (size : word).
  Context {default : T}.

  Local Open Scope sep_scope.

  Local Notation off k := (word.of_Z (word.unsigned size * Z.of_nat k)).

  (** [hd default (skipn n xs) = nth n xs default] when [n < length xs].
      Follows [skipn_S_eq_gen]'s shape from [BLS12_MSM.v]. *)
  Lemma hd_skipn_nth (xs : list T) (n : nat) :
    (n < length xs)%nat ->
    hd default (skipn n xs) = nth n xs default.
  Proof.
    revert n. induction xs as [|x rest IH]; intros [|n'] Hn; cbn in *; try lia.
    - reflexivity.
    - apply IH. lia.
  Qed.

  Lemma skipn_S_eq (xs : list T) (n : nat) :
    (n < length xs)%nat ->
    skipn n xs = nth n xs default :: skipn (S n) xs.
  Proof.
    revert n. induction xs as [|x rest IH]; intros [|n'] Hn; cbn in *; try lia.
    - reflexivity.
    - apply IH. lia.
  Qed.

  (** Split one bucket triple (at index [d]) and one point triple (at
      index [n]) out of the L3 invariant sep.  Each triple stays
      contiguous in the output so a follow-up [seprewrite_in] with
      [PointArray_update_at] matches cleanly. *)
  Lemma L3_bucket_point_split
      (buckets_x buckets_y buckets_z ppx ppy ppz : word)
      (bs_x bs_y bs_z px py pz : list T)
      (d n : nat)
      (Sc R : mem -> Prop) (m : mem) :
    (d < length bs_x)%nat -> (d < length bs_y)%nat -> (d < length bs_z)%nat ->
    (n < length px)%nat -> (n < length py)%nat -> (n < length pz)%nat ->
    (PointArray point size buckets_x bs_x
     * PointArray point size buckets_y bs_y
     * PointArray point size buckets_z bs_z
     * Sc
     * PointArray point size ppx px
     * PointArray point size ppy py
     * PointArray point size ppz pz
     * R)%sep m ->
    ((PointArray point size buckets_x (firstn d bs_x)
      * point (word.add buckets_x (off d)) (nth d bs_x default)
      * PointArray point size (word.add (word.add buckets_x (off d)) size)
                   (skipn (S d) bs_x))
     * (PointArray point size buckets_y (firstn d bs_y)
        * point (word.add buckets_y (off d)) (nth d bs_y default)
        * PointArray point size (word.add (word.add buckets_y (off d)) size)
                     (skipn (S d) bs_y))
     * (PointArray point size buckets_z (firstn d bs_z)
        * point (word.add buckets_z (off d)) (nth d bs_z default)
        * PointArray point size (word.add (word.add buckets_z (off d)) size)
                     (skipn (S d) bs_z))
     * Sc
     * (PointArray point size ppx (firstn n px)
        * point (word.add ppx (off n)) (nth n px default)
        * PointArray point size (word.add (word.add ppx (off n)) size)
                     (skipn (S n) px))
     * (PointArray point size ppy (firstn n py)
        * point (word.add ppy (off n)) (nth n py default)
        * PointArray point size (word.add (word.add ppy (off n)) size)
                     (skipn (S n) py))
     * (PointArray point size ppz (firstn n pz)
        * point (word.add ppz (off n)) (nth n pz default)
        * PointArray point size (word.add (word.add ppz (off n)) size)
                     (skipn (S n) pz))
     * R)%sep m.
  Proof.
    intros Hdx Hdy Hdz Hnx Hny Hnz Hm.
    pose proof (PointArray_split_at (T:=T) (default:=default)
                  point size buckets_x bs_x d Hdx) as Hbx.
    pose proof (PointArray_split_at (T:=T) (default:=default)
                  point size buckets_y bs_y d Hdy) as Hby.
    pose proof (PointArray_split_at (T:=T) (default:=default)
                  point size buckets_z bs_z d Hdz) as Hbz.
    pose proof (PointArray_split_at (T:=T) (default:=default)
                  point size ppx px n Hnx) as Hpx.
    pose proof (PointArray_split_at (T:=T) (default:=default)
                  point size ppy py n Hny) as Hpy.
    pose proof (PointArray_split_at (T:=T) (default:=default)
                  point size ppz pz n Hnz) as Hpz.
    rewrite (hd_skipn_nth bs_x d Hdx) in Hbx.
    rewrite (hd_skipn_nth bs_y d Hdy) in Hby.
    rewrite (hd_skipn_nth bs_z d Hdz) in Hbz.
    rewrite (hd_skipn_nth px n Hnx) in Hpx.
    rewrite (hd_skipn_nth py n Hny) in Hpy.
    rewrite (hd_skipn_nth pz n Hnz) in Hpz.
    seprewrite_in Hbx Hm.
    seprewrite_in Hby Hm.
    seprewrite_in Hbz Hm.
    seprewrite_in Hpx Hm.
    seprewrite_in Hpy Hm.
    seprewrite_in Hpz Hm.
    ecancel_assumption.
  Qed.

  (** Re-merge: buckets updated with new values [bx' by' bz'], points
      merged back with their original values. *)
  Lemma L3_bucket_triple_merge
      (buckets_x buckets_y buckets_z ppx ppy ppz : word)
      (bs_x bs_y bs_z px py pz : list T)
      (bx' by' bz' : T)
      (d n : nat)
      (Sc R : mem -> Prop) (m : mem) :
    (d < length bs_x)%nat -> (d < length bs_y)%nat -> (d < length bs_z)%nat ->
    (n < length px)%nat -> (n < length py)%nat -> (n < length pz)%nat ->
    ((PointArray point size buckets_x (firstn d bs_x)
      * point (word.add buckets_x (off d)) bx'
      * PointArray point size (word.add (word.add buckets_x (off d)) size)
                   (skipn (S d) bs_x))
     * (PointArray point size buckets_y (firstn d bs_y)
        * point (word.add buckets_y (off d)) by'
        * PointArray point size (word.add (word.add buckets_y (off d)) size)
                     (skipn (S d) bs_y))
     * (PointArray point size buckets_z (firstn d bs_z)
        * point (word.add buckets_z (off d)) bz'
        * PointArray point size (word.add (word.add buckets_z (off d)) size)
                     (skipn (S d) bs_z))
     * Sc
     * (PointArray point size ppx (firstn n px)
        * point (word.add ppx (off n)) (nth n px default)
        * PointArray point size (word.add (word.add ppx (off n)) size)
                     (skipn (S n) px))
     * (PointArray point size ppy (firstn n py)
        * point (word.add ppy (off n)) (nth n py default)
        * PointArray point size (word.add (word.add ppy (off n)) size)
                     (skipn (S n) py))
     * (PointArray point size ppz (firstn n pz)
        * point (word.add ppz (off n)) (nth n pz default)
        * PointArray point size (word.add (word.add ppz (off n)) size)
                     (skipn (S n) pz))
     * R)%sep m ->
    (PointArray point size buckets_x
                (firstn d bs_x ++ bx' :: skipn (S d) bs_x)
     * PointArray point size buckets_y
                  (firstn d bs_y ++ by' :: skipn (S d) bs_y)
     * PointArray point size buckets_z
                  (firstn d bs_z ++ bz' :: skipn (S d) bs_z)
     * Sc
     * PointArray point size ppx px
     * PointArray point size ppy py
     * PointArray point size ppz pz
     * R)%sep m.
  Proof.
    intros Hdx Hdy Hdz Hnx Hny Hnz Hm.
    pose proof (PointArray_update_at (T:=T)
                  point size buckets_x bs_x d bx' Hdx) as Hbx.
    pose proof (PointArray_update_at (T:=T)
                  point size buckets_y bs_y d by' Hdy) as Hby.
    pose proof (PointArray_update_at (T:=T)
                  point size buckets_z bs_z d bz' Hdz) as Hbz.
    pose proof (PointArray_update_at (T:=T)
                  point size ppx px n (nth n px default) Hnx) as Hpx.
    pose proof (PointArray_update_at (T:=T)
                  point size ppy py n (nth n py default) Hny) as Hpy.
    pose proof (PointArray_update_at (T:=T)
                  point size ppz pz n (nth n pz default) Hnz) as Hpz.
    assert (Hpx_eq : (firstn n px ++ nth n px default :: skipn (S n) px)%list = px).
    { rewrite <- (skipn_S_eq px n Hnx). apply firstn_skipn. }
    assert (Hpy_eq : (firstn n py ++ nth n py default :: skipn (S n) py)%list = py).
    { rewrite <- (skipn_S_eq py n Hny). apply firstn_skipn. }
    assert (Hpz_eq : (firstn n pz ++ nth n pz default :: skipn (S n) pz)%list = pz).
    { rewrite <- (skipn_S_eq pz n Hnz). apply firstn_skipn. }
    rewrite Hpx_eq in Hpx.
    rewrite Hpy_eq in Hpy.
    rewrite Hpz_eq in Hpz.
    seprewrite_in Hbx Hm.
    seprewrite_in Hby Hm.
    seprewrite_in Hbz Hm.
    seprewrite_in Hpx Hm.
    seprewrite_in Hpy Hm.
    seprewrite_in Hpz Hm.
    ecancel_assumption.
  Qed.

End L3BucketSplit.
