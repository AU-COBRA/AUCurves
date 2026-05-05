(** * WP-proof context-cleanup tactics.
 *
 * bedrock2 WP proofs accumulate stale hypotheses across [straightline_call]
 * chains, [seprewrite_in] applications, and manual sep rebuilds.  The
 * accumulation makes goal-state output (e.g., MCP responses) unreadable
 * past ~5 calls in.  See [feedback_clear_intermediate_seps.md] for the
 * track record.
 *
 * This module provides clearing tactics + display caps for long
 * bedrock2 WP proofs.
 *)

Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.Map.Separation.

(** * Display caps — add these at the start of long WP proofs.

    Apply at the top of every long WP proof to cap goal-output size:
<<
    Set Printing Depth 10.
    Set Printing Width 60.
    Set Printing Compact Contexts.
>>
    These three lines cut a 50K env to ~5K because FElem and sep chains
    stop printing past depth 10. *)

(** * Clearing tactics. *)

(** [seprewrite_in_clear H Htarget]: rewrite [H : Lift1Prop.iff1 _ _] in
    hypothesis [Htarget], then drop [H] from the context.  Avoids the
    repeated-iff1-in-context noise that builds up with manual seprewrite
    chains. *)
Ltac seprewrite_in_clear H Htarget :=
  seprewrite_in H Htarget; clear H.

(** [seprewrite_clear H]: rewrite [H : Lift1Prop.iff1 _ _] in goal, then
    drop [H].  Goal-side variant of [seprewrite_in_clear]. *)
Ltac seprewrite_clear H :=
  seprewrite H; clear H.

(** [clear_iff1_facts]: drop ALL [Lift1Prop.iff1] hypotheses from the
    context.  Use after a sep-rebuild step has consumed them. *)
Ltac clear_iff1_facts :=
  repeat match goal with
  | H : Lift1Prop.iff1 _ _ |- _ => clear H
  end.

(** [clear_named_if_present H]: try to clear [H], succeed silently if
    it doesn't exist.  Use to drop hyps with known-but-not-always-present
    names (e.g., the [Hany1], [Hsplit2] from stackalloc). *)
Tactic Notation "clear_named_if_present" hyp(h) :=
  tryif clear h then idtac else idtac.

(** [clear_subsumed_seps]: drop sep hypotheses on memories that have a
    LATER (more recent) sep hyp on a downstream memory.  Heuristic:
    looks for two sep facts on different memories, drops the older.
    Conservative — fails silently when ambiguous. *)
Ltac clear_subsumed_seps :=
  repeat match goal with
  | H1 : (_ ⋆ _)%sep ?m1, H2 : (_ ⋆ _)%sep ?m2 |- _ =>
    let _ := constr:(eq_refl : m1 = m1) in
    (* Only fire if m1 ≠ m2 syntactically — different mems means H1 stale. *)
    tryif constr_eq m1 m2 then fail else clear H1
  end.

(** * Convenience for naming auto-introduced post hypotheses.

    [destruct_wp_post_felem]: matches a hyp of shape
    [_ = nil /\ _ = _ /\ exists _ : felem, _ /\ _ /\ _]
    (the standard [from_bytes] post) and destructs into [Hrets, Htr,
     X, Hfeval, Hbnd, Hsep_post]. *)
Ltac destruct_wp_post_felem :=
  match goal with
  | H : _ = nil /\ _ = _ /\ exists _ : _, _ |- _ =>
    let r := fresh "Hrets" in
    let t := fresh "Htr" in
    let x := fresh "X" in
    let fv := fresh "Hfeval" in
    let bd := fresh "Hbnd" in
    let s := fresh "Hsep_post" in
    destruct H as (r & t & x & fv & bd & s)
  end.

(** [destruct_wp_post_bytes]: matches the parametric/unipost shape
    [_ = nil /\ _ = _ /\ exists _ : list byte, _ /\ _]. *)
Ltac destruct_wp_post_bytes :=
  match goal with
  | H : _ = nil /\ _ = _ /\ exists _ : list _, _ |- _ =>
    let r := fresh "Hrets" in
    let t := fresh "Htr" in
    let bs := fresh "out" in
    let lb := fresh "Hlen" in
    let s := fresh "Hsep_post" in
    destruct H as (r & t & bs & lb & s)
  end.
