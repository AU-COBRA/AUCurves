(** * Ed25519 borrow checker
 *
 * Parallel to [SafeRustBorrowCheck.v] (BLS12).  Provides:
 *   §1  borrow_ok_ed : rust_cmd_ed → bool
 *   §2  call_aliases_false_ne — borrow_ok implies no-alias
 *   §3  Frame property (parameterized over a frame-respecting
 *       callee_post)
 *   §4  Soundness theorem
 *
 * Architectural note: BLS12's borrow_check is proved sound against an
 * inductive [rust_exec] that has explicit XR_call : rs_inner =
 * located_update rs dest leaf_spec.  Ed25519's [rust_exec_ed] uses an
 * opaque [callee_post] oracle, so the soundness theorem here is
 * parameterized over a frame-respecting predicate on callee_post:
 * any callee writing ONLY to its dest preserves args.
 *
 * Reference: [SafeRustBorrowCheck.v].
 * Plan: [R10_RUSTCMD_PORT_PLAN.md] Week 2 Day 7-8.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Bool.Bool.
Import ListNotations.
Local Open Scope string_scope.

Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.

(* ================================================================ *)
(* §1. Borrow checker                                               *)
(* ================================================================ *)

(** Does [d.loc_var] appear in any of [args]'s loc_var fields? *)
Definition located_uses_ed (target : String.string) (l : located_ed) : bool :=
  String.eqb target l.(loc_var).

Definition call_aliases_ed (dest : located_ed) (args : list located_ed) : bool :=
  List.existsb (located_uses_ed dest.(loc_var)) args.

(** Multi-output alias check: does any name in [dests] appear in [args],
    OR does the same name appear twice in [dests]?  Used by [REdCallN].
    Returns [true] if a problem exists (mirroring [call_aliases_ed]). *)
Fixpoint dests_pairwise_dup (dests : list located_ed) : bool :=
  match dests with
  | [] => false
  | d :: rest =>
      List.existsb (located_uses_ed d.(loc_var)) rest
      || dests_pairwise_dup rest
  end.

Definition dest_in_args_ed (dests args : list located_ed) : bool :=
  List.existsb (fun d => List.existsb (located_uses_ed d.(loc_var)) args) dests.

Definition call_aliases_n_ed (dests args : list located_ed) : bool :=
  dests_pairwise_dup dests || dest_in_args_ed dests args.

(** [borrow_ok_ed c] holds iff every [REdCall] in [c] has its
    destination variable distinct from all argument variables.
    Same idea as BLS12's borrow_ok but for the Ed25519 command set. *)
Fixpoint borrow_ok_ed (c : rust_cmd_ed) : bool :=
  match c with
  | REdSkip                       => true
  | REdSeq c1 c2                  => borrow_ok_ed c1 && borrow_ok_ed c2
  | REdLetZero _ _ body           => borrow_ok_ed body
  | REdLetU64 _ _ body            => borrow_ok_ed body
  | REdScalarSet _ _              => true
  | REdCall _ dest args           => negb (call_aliases_ed dest args)
  | REdIfNz _ ct cf               => borrow_ok_ed ct && borrow_ok_ed cf
  | REdWhileNz _ body             => borrow_ok_ed body
  | REdByteStore _ _ _            => true
  | REdByteLoad _ _ _             => true
  | REdFor _ _ body               => borrow_ok_ed body
  | REdSelect _ _ _ _             => true
      (* CT conditional move: reads two source slots, writes one
         dest slot.  No aliasing concern at the borrow-check level —
         in real Rust output the two sources are read into local
         u64 lanes via [subtle::Choice], merged with a mask, then
         stored to dest, so even if a source aliases dest the reads
         complete before the write.  Always borrow-ok. *)
  | REdCallN _ dests args         => negb (call_aliases_n_ed dests args)
  end.

(* ================================================================ *)
(* §2. call_aliases_false_ne                                        *)
(* ================================================================ *)

Lemma call_aliases_ed_false_ne :
  forall (dest : located_ed) (args : list located_ed) (arg : located_ed),
    call_aliases_ed dest args = false ->
    List.In arg args ->
    dest.(loc_var) <> arg.(loc_var).
Proof.
  intros dest args arg Hca Hin Heq.
  unfold call_aliases_ed in Hca.
  assert (Htrue : List.existsb (located_uses_ed dest.(loc_var)) args = true).
  { apply List.existsb_exists.
    exists arg. split; [exact Hin |].
    unfold located_uses_ed. rewrite Heq. apply String.eqb_refl. }
  rewrite Htrue in Hca. discriminate.
Qed.

(* ================================================================ *)
(* §3. Frame property                                               *)
(* ================================================================ *)

(** [callee_frame_respecting]: a callee_post oracle that writes ONLY
    to dest (in the rs_tower_ed sense).  For any var x ≠ dest.loc_var,
    the tower lookup at x is preserved. *)
Definition callee_frame_respecting
    (callee_post :
      String.string -> list located_ed -> located_ed ->
      rust_state_ed -> rust_state_ed -> Prop) : Prop :=
  forall fname args dest rs1 rs2,
    callee_post fname args dest rs1 rs2 ->
    forall x, x <> dest.(loc_var) ->
      lookup_t_ed (rs_tower_ed rs2) x = lookup_t_ed (rs_tower_ed rs1) x.

(* ================================================================ *)
(* §4. Soundness theorem                                            *)
(* ================================================================ *)

(** For a borrow-checked [REdCall f dest args], every argument
    variable's tower lookup is unchanged after the call executes
    — provided the callee_post oracle is frame-respecting.
    Mirrors [borrow_ok_call_frame] in BLS12. *)
Theorem borrow_ok_ed_call_frame :
  forall callee_post callee_post_n,
    callee_frame_respecting callee_post ->
    forall f (dest : located_ed) (args : list located_ed) rs rs',
      borrow_ok_ed (REdCall f dest args) = true ->
      rust_exec_ed callee_post callee_post_n (REdCall f dest args) rs rs' ->
      forall (arg : located_ed),
        List.In arg args ->
        lookup_t_ed (rs_tower_ed rs') arg.(loc_var) =
        lookup_t_ed (rs_tower_ed rs) arg.(loc_var).
Proof.
  intros callee_post callee_post_n Hframe f dest args rs rs' Hbok Hexec arg Hin.
  cbn in Hbok. apply Bool.negb_true_iff in Hbok.
  assert (Hne : dest.(loc_var) <> arg.(loc_var))
    by (apply call_aliases_ed_false_ne with (args := args); assumption).
  inversion Hexec as [| | | | | ? ? ? ? ? Hcp | | | | | | | | | |]; subst.
  apply (Hframe f args dest rs rs' Hcp arg.(loc_var)).
  congruence.
Qed.

(** Convenience: [borrow_ok_ed] of a sequence implies both parts. *)
Lemma borrow_ok_ed_seq_l : forall c1 c2,
  borrow_ok_ed (REdSeq c1 c2) = true -> borrow_ok_ed c1 = true.
Proof. intros c1 c2 H; cbn in H; apply Bool.andb_true_iff in H; tauto. Qed.

Lemma borrow_ok_ed_seq_r : forall c1 c2,
  borrow_ok_ed (REdSeq c1 c2) = true -> borrow_ok_ed c2 = true.
Proof. intros c1 c2 H; cbn in H; apply Bool.andb_true_iff in H; tauto. Qed.

(** General frame: any tower variable with a different name from
    dest is unchanged by a [REdCall], regardless of args. *)
Theorem call_frame_non_dest_ed :
  forall callee_post callee_post_n,
    callee_frame_respecting callee_post ->
    forall f (dest : located_ed) (args : list located_ed) rs rs' (x : String.string),
      rust_exec_ed callee_post callee_post_n (REdCall f dest args) rs rs' ->
      x <> dest.(loc_var) ->
      lookup_t_ed (rs_tower_ed rs') x = lookup_t_ed (rs_tower_ed rs) x.
Proof.
  intros callee_post callee_post_n Hframe f dest args rs rs' x Hexec Hne.
  inversion Hexec as [| | | | | ? ? ? ? ? Hcp | | | | | | | | | |]; subst.
  exact (Hframe f args dest rs rs' Hcp x Hne).
Qed.

(* ================================================================ *)
(* §5. dests_of_ed — program write-set                              *)
(* ================================================================ *)

Fixpoint dests_of_ed (c : rust_cmd_ed) : list String.string :=
  match c with
  | REdSkip                       => []
  | REdSeq c1 c2                  => dests_of_ed c1 ++ dests_of_ed c2
  | REdLetZero x _ body           => x :: dests_of_ed body
  | REdLetU64 _ _ body            => dests_of_ed body
  | REdScalarSet _ _              => []
  | REdCall _ dest _              => [dest.(loc_var)]
  | REdIfNz _ ct cf               => dests_of_ed ct ++ dests_of_ed cf
  | REdWhileNz _ body             => dests_of_ed body
  | REdByteStore loc _ _          => [loc.(loc_var)]
  | REdByteLoad x _ _             => [x]
  | REdFor _ _ body               => dests_of_ed body
  | REdSelect _ _ _ dest          => [dest.(loc_var)]
  | REdCallN _ dests _            => List.map loc_var dests
  end.

(* ================================================================ *)
(* §6. Multi-output (REdCallN) frame property                         *)
(* ================================================================ *)

(** Multi-output frame-respecting predicate: any callee_post_n that
    writes ONLY to slots in [dests] preserves all other tower
    bindings.  Mirrors [callee_frame_respecting] for the multi-dest
    oracle. *)
Definition callee_n_frame_respecting
    (callee_post_n :
      String.string -> list located_ed -> list located_ed ->
      rust_state_ed -> rust_state_ed -> Prop) : Prop :=
  forall fname dests args rs1 rs2,
    callee_post_n fname dests args rs1 rs2 ->
    forall x,
      (forall d, List.In d dests -> x <> d.(loc_var)) ->
      lookup_t_ed (rs_tower_ed rs2) x = lookup_t_ed (rs_tower_ed rs1) x.

(** Helper: when [call_aliases_n_ed dests args = false], every dest
    name differs from every arg name. *)
Lemma call_aliases_n_ed_false_dest_ne_arg :
  forall (dests args : list located_ed) (d a : located_ed),
    call_aliases_n_ed dests args = false ->
    List.In d dests ->
    List.In a args ->
    d.(loc_var) <> a.(loc_var).
Proof.
  intros dests args d a Hca Hd Ha Heq.
  unfold call_aliases_n_ed in Hca.
  apply Bool.orb_false_iff in Hca as [_Hdup Hin].
  unfold dest_in_args_ed in Hin.
  assert (Htrue : List.existsb
                    (fun d' => List.existsb (located_uses_ed d'.(loc_var)) args)
                    dests = true).
  { apply List.existsb_exists.
    exists d. split; [exact Hd|].
    apply List.existsb_exists.
    exists a. split; [exact Ha|].
    unfold located_uses_ed. rewrite Heq. apply String.eqb_refl. }
  rewrite Htrue in Hin. discriminate.
Qed.

(** For a borrow-checked [REdCallN f dests args], every argument
    variable's tower lookup is unchanged after the call executes
    — provided the callee_post_n oracle is frame-respecting w.r.t.
    its dest list. *)
Theorem borrow_ok_ed_calln_frame :
  forall callee_post callee_post_n,
    callee_n_frame_respecting callee_post_n ->
    forall f (dests args : list located_ed) rs rs',
      borrow_ok_ed (REdCallN f dests args) = true ->
      rust_exec_ed callee_post callee_post_n (REdCallN f dests args) rs rs' ->
      forall (arg : located_ed),
        List.In arg args ->
        lookup_t_ed (rs_tower_ed rs') arg.(loc_var) =
        lookup_t_ed (rs_tower_ed rs) arg.(loc_var).
Proof.
  intros callee_post callee_post_n Hframe f dests args rs rs' Hbok Hexec arg Hin.
  cbn in Hbok. apply Bool.negb_true_iff in Hbok.
  inversion Hexec as [| | | | | | | | | | | | | | | ? ? ? ? ? Hcpn]; subst.
  apply (Hframe f dests args rs rs' Hcpn arg.(loc_var)).
  intros d Hd Heq.
  pose proof (call_aliases_n_ed_false_dest_ne_arg dests args d arg Hbok Hd Hin) as Hne.
  apply Hne; symmetry; exact Heq.
Qed.

(** Non-dest tower frame: any tower variable with name distinct from
    every dest in the list is unchanged by an [REdCallN]. *)
Theorem calln_frame_non_dest_ed :
  forall callee_post callee_post_n,
    callee_n_frame_respecting callee_post_n ->
    forall f (dests args : list located_ed) rs rs' (x : String.string),
      rust_exec_ed callee_post callee_post_n (REdCallN f dests args) rs rs' ->
      (forall d, List.In d dests -> x <> d.(loc_var)) ->
      lookup_t_ed (rs_tower_ed rs') x = lookup_t_ed (rs_tower_ed rs) x.
Proof.
  intros callee_post callee_post_n Hframe f dests args rs rs' x Hexec Hne.
  inversion Hexec as [| | | | | | | | | | | | | | | ? ? ? ? ? Hcpn]; subst.
  exact (Hframe f dests args rs rs' Hcpn x Hne).
Qed.
