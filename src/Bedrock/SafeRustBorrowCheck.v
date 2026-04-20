(** * SafeRustBorrowCheck.v
 *
 * A borrow checker for [rust_cmd], together with a soundness theorem:
 * borrow-checked programs preserve their argument variables across calls.
 *
 * This replaces per-function separation logic pre/postconditions
 * for the memory-safety part of correctness proofs.
 *
 * Instead of one 400-line WP proof per function proving
 *
 *   sep (FElem src1_ptr a) (FElem src2_ptr b) (FElem dst_ptr _)
 *
 * one call to [borrow_ok] checks the whole program, proved sound once here.
 *
 * Contents:
 *   §1  borrow_ok : rust_cmd → bool
 *   §2  call_aliases_false_ne — borrow_ok implies no-alias
 *   §3  located_update_other_lookup — frame property for located_update
 *   §4  borrow_ok_call_frame — main soundness theorem
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Bool.Bool.
Import ListNotations.
Local Open Scope string_scope.

Require Import Bedrock.SafeRustSimulation.

(* ================================================================ *)
(* §1. Borrow checker                                               *)
(* ================================================================ *)

(** [borrow_ok c] holds iff every [RCall] in [c] has its destination
    variable distinct from all argument variables.

    [RCloneCall] is structurally safe by design: the clone variable
    breaks the dest–arg alias before the inner call runs.  We still
    check that the inner call's destination doesn't alias its args. *)
Fixpoint borrow_ok (c : rust_cmd) : bool :=
  match c with
  | RSkip                       => true
  | RSeq c1 c2                  => borrow_ok c1 && borrow_ok c2
  | RLetZero _ _ body           => borrow_ok body
  | RLetU64Zero _ body          => borrow_ok body
  | RScalarSet _ _              => true
  | RCall _ dest args           => negb (call_aliases dest args)
  | RCloneCall _ _ _ dest args  => negb (call_aliases dest args)
  | RIfNz _ ct cf               => borrow_ok ct && borrow_ok cf
  | RWhileNz _ body             => borrow_ok body
  | RLimbStore _ _ _            => true
  end.

(* ================================================================ *)
(* §2. call_aliases_false_ne                                        *)
(* ================================================================ *)

(** If [call_aliases dest args = false], then for every arg in args,
    [dest.loc_var ≠ arg.loc_var]. *)
Lemma call_aliases_false_ne :
  forall (dest : located) (args : list located) (arg : located),
    call_aliases dest args = false ->
    List.In arg args ->
    loc_var dest <> loc_var arg.
Proof.
  intros dest args arg Hca Hin Heq.
  unfold call_aliases in Hca.
  assert (Htrue : List.existsb (located_uses (loc_var dest)) args = true).
  { apply List.existsb_exists.
    exists arg. split; [exact Hin |].
    unfold located_uses. rewrite Heq. apply String.eqb_refl. }
  rewrite Htrue in Hca. discriminate.
Qed.

(* ================================================================ *)
(* §3. Frame property for located_update                           *)
(* ================================================================ *)

(** Updating [loc1] in a state does not change the value at [loc2]
    when their base variables differ.

    This is the analogue of the separation logic frame rule:
    writing to [dest] leaves [src] unchanged because they are at
    distinct named variables (playing the role of distinct addresses). *)
Lemma located_update_other_lookup :
  forall (rs : rust_state)
         (loc1 : located)
         (v : rust_val (loc_dst loc1))
         (rs' : rust_state)
         (loc2 : located),
    loc_var loc1 <> loc_var loc2 ->
    located_update rs loc1 v = Some rs' ->
    located_lookup rs' loc2 = located_lookup rs loc2.
Proof.
  intros rs loc1 v rs' loc2 Hne Hupd.
  unfold located_update in Hupd.
  destruct (lookup_t (rs_tower rs) (loc_var loc1)) as [[t val] |] eqn:_Hl;
    [| discriminate].
  destruct (tower_type_eq_dec t (loc_src loc1)) as [_Ht |]; [| discriminate].
  injection Hupd as Hrs'. subst rs'.
  unfold located_lookup, rs_set_tower. simpl.
  rewrite (lookup_t_update_other (rs_tower rs) (loc_var loc1) (loc_var loc2) _ Hne).
  reflexivity.
Qed.

(* ================================================================ *)
(* §4. Main soundness theorem                                       *)
(* ================================================================ *)

Section BorrowCheckSoundness.

Variable N : nat.
Variable u64_max : nat.
Variable leaf_spec :
  string ->
  forall (dt : tower_type) (in_ts : list tower_type),
    rust_val dt ->
    list { t : tower_type & rust_val t } ->
    rust_val dt.

(** For a borrow-checked [RCall f dest args], every argument variable
    is unchanged after the call executes.

    This is the property that separation logic postconditions of the
    form [sep (FElem src1_ptr a) (FElem src2_ptr b) ...] express —
    here derived automatically from [borrow_ok] instead of per-function
    manual proof. *)
Theorem borrow_ok_call_frame :
  forall f (dest : located) (args : list located) (rs rs' : rust_state),
    borrow_ok (RCall f dest args) = true ->
    rust_exec N u64_max leaf_spec (RCall f dest args) rs rs' ->
    forall (arg : located),
      List.In arg args ->
      located_lookup rs' arg = located_lookup rs arg.
Proof.
  intros f dest args rs rs' Hbok Hexec arg Hin.
  simpl in Hbok. apply negb_true_iff in Hbok.
  assert (Hne : loc_var dest <> loc_var arg)
    by (apply call_aliases_false_ne with (args := args); assumption).
  inversion Hexec; subst.
  eapply located_update_other_lookup; [exact Hne | eassumption].
Qed.

(** Convenience: [borrow_ok] of a sequence implies both parts. *)
Lemma borrow_ok_seq_l : forall c1 c2,
  borrow_ok (RSeq c1 c2) = true -> borrow_ok c1 = true.
Proof.
  intros c1 c2 H. simpl in H. apply Bool.andb_true_iff in H. tauto.
Qed.

Lemma borrow_ok_seq_r : forall c1 c2,
  borrow_ok (RSeq c1 c2) = true -> borrow_ok c2 = true.
Proof.
  intros c1 c2 H. simpl in H. apply Bool.andb_true_iff in H. tauto.
Qed.

(** More general frame: any variable with a different base name from
    [dest] is unchanged by a [RCall], regardless of whether it
    appears in [args].  No [borrow_ok] hypothesis needed. *)
Theorem call_frame_non_dest :
  forall f (dest : located) (args : list located) (rs rs' : rust_state)
         (loc2 : located),
    rust_exec N u64_max leaf_spec (RCall f dest args) rs rs' ->
    loc_var dest <> loc_var loc2 ->
    located_lookup rs' loc2 = located_lookup rs loc2.
Proof.
  intros f dest args rs rs' loc2 Hexec Hne.
  inversion Hexec; subst.
  eapply located_update_other_lookup; [exact Hne | eassumption].
Qed.

(* ================================================================ *)
(* §5. dests_of — program write-set                               *)
(* ================================================================ *)

End BorrowCheckSoundness.

(** [dests_of c] enumerates the base variable names that [c] may write
    to during any execution.  Used by [seq_frame] below. *)
Fixpoint dests_of (c : rust_cmd) : list string :=
  match c with
  | RSkip                       => []
  | RSeq c1 c2                  => dests_of c1 ++ dests_of c2
  | RLetZero x _ body           => x :: dests_of body
  | RLetU64Zero _ body          => dests_of body
  | RScalarSet _ _              => []
  | RCall _ dest _              => [loc_var dest]
  | RCloneCall x _ _ dest _     => x :: [loc_var dest]
  | RIfNz _ ct cf               => dests_of ct ++ dests_of cf
  | RWhileNz _ body             => dests_of body
  | RLimbStore loc _ _          => [loc_var loc]
  end.

(* ================================================================ *)
(* §6. seq_frame — general frame for programs                     *)
(* ================================================================ *)

(** Helper: setting a different tower variable doesn't change [loc]'s lookup.
    [located_lookup] does not depend on the BigStep section variables, so
    these helpers live outside any section. *)
Lemma located_lookup_set_tower_other :
  forall rs x v (loc : located),
    x <> loc_var loc ->
    located_lookup (rs_set_tower rs x v) loc = located_lookup rs loc.
Proof.
  intros rs x v loc Hne.
  unfold located_lookup, rs_set_tower. simpl.
  rewrite lookup_t_update_other; [reflexivity | exact Hne].
Qed.

Lemma located_lookup_set_scalar_other :
  forall rs x v (loc : located),
    located_lookup (rs_set_scalar rs x v) loc = located_lookup rs loc.
Proof.
  intros rs x v loc.
  unfold located_lookup, rs_set_scalar. simpl. reflexivity.
Qed.

Lemma located_lookup_remove_other :
  forall tower scalar x (loc : located),
    x <> loc_var loc ->
    located_lookup {| rs_tower := remove_var tower x; rs_scalar := scalar |} loc =
    located_lookup {| rs_tower := tower; rs_scalar := scalar |} loc.
Proof.
  intros tower scalar x loc Hne.
  unfold located_lookup. simpl.
  rewrite lookup_t_remove_other; [reflexivity | exact Hne].
Qed.

Section SeqFrame.

Variable N : nat.
Variable u64_max : nat.
Variable leaf_spec :
  string ->
  forall (dt : tower_type) (in_ts : list tower_type),
    rust_val dt ->
    list { t : tower_type & rust_val t } ->
    rust_val dt.

(** [seq_frame]: if [loc_var loc] is not in [dests_of c], then any
    execution of [c] preserves [located_lookup rs loc].

    Proved for all constructors, 0 admits.

    The [RCloneCall] case is closed by including [x] (the clone variable)
    in [dests_of]: the precondition [~ In (loc_var loc) (dests_of c)] then
    directly yields both [x <> loc_var loc] and [loc_var dest <> loc_var loc],
    making the three-step chain (remove_other → inner IH → set_other) provable
    without any freshness assumption. *)
Theorem seq_frame :
  forall (c : rust_cmd) (rs rs' : rust_state) (loc : located),
    rust_exec N u64_max leaf_spec c rs rs' ->
    ~ List.In (loc_var loc) (dests_of c) ->
    located_lookup rs' loc = located_lookup rs loc.
Proof.
  intros c rs rs' loc Hexec Hnotin.
  induction Hexec; simpl in Hnotin.

  - (* XR_skip *) reflexivity.

  - (* XR_seq c1 c2 *)
    assert (Hn1 : ~ List.In (loc_var loc) (dests_of c1)).
    { intro Hc. apply Hnotin. apply List.in_app_iff. left. exact Hc. }
    assert (Hn2 : ~ List.In (loc_var loc) (dests_of c2)).
    { intro Hc. apply Hnotin. apply List.in_app_iff. right. exact Hc. }
    etransitivity; [apply IHHexec2; exact Hn2 | apply IHHexec1; exact Hn1].

  - (* XR_let_zero *)
    assert (Hne : x <> loc_var loc) by (intro Hc; apply Hnotin; now left).
    assert (Hn : ~ List.In (loc_var loc) (dests_of c)) by
      (intro Hc; apply Hnotin; now right).
    etransitivity; [apply IHHexec; exact Hn |
                    apply located_lookup_set_tower_other; exact Hne].

  - (* XR_let_u64_zero *)
    etransitivity; [apply IHHexec; exact Hnotin |
                    apply located_lookup_set_scalar_other].

  - (* XR_scalar_set *) apply located_lookup_set_scalar_other.

  - (* XR_if_true *)
    apply IHHexec.
    intro Hc. apply Hnotin. apply List.in_app_iff. left. exact Hc.

  - (* XR_if_false *)
    apply IHHexec.
    intro Hc. apply Hnotin. apply List.in_app_iff. right. exact Hc.

  - (* XR_while_false *) reflexivity.

  - (* XR_while_true *)
    etransitivity; [apply IHHexec2; exact Hnotin |
                    apply IHHexec1; exact Hnotin].

  - (* XR_call *)
    assert (Hne : loc_var dest <> loc_var loc)
      by (intro Hc; apply Hnotin; now left).
    eapply located_update_other_lookup; [exact Hne | eassumption].

  - (* XR_clone_call *)
    (* dests_of (RCloneCall x …) = x :: [loc_var dest], so hNotIn gives both: *)
    assert (Hxne : x <> loc_var loc)
      by (intro Hc; apply Hnotin; now left).
    assert (Hne_dest : loc_var call_dest <> loc_var loc)
      by (intro Hc; apply Hnotin; right; now left).
    assert (H_inner : located_lookup rs_inner loc =
                      located_lookup (rs_set_tower rs x (exist_tval (loc_dst dest) old_dest_v)) loc).
    { eapply call_frame_non_dest; [exact Hexec | exact Hne_dest]. }
    subst rs'.
    rewrite (located_lookup_remove_other (rs_tower rs_inner) (rs_scalar rs_inner) x loc Hxne).
    change (located_lookup rs_inner loc = located_lookup rs loc).
    rewrite H_inner.
    apply located_lookup_set_tower_other. exact Hxne.

  - (* XR_limb_store *)

    assert (Hne : loc_var loc0 <> loc_var loc)
      by (intro Hc; apply Hnotin; now left).
    eapply located_update_other_lookup; [exact Hne | eassumption].
Qed.

End SeqFrame.
