(** * StrongCorrectnessTactics — reusable Ltac for protocol strong-correctness
 *
 *  Common boilerplate factored out of:
 *    - [End2End.Ed25519.Sign_Strong_Correctness]
 *    - [End2End.Ed25519.Verify_Strong_Correctness]
 *    - [End2End.XEdDSA.Sign_Strong_Correctness]
 *    - [End2End.Lizard.Strong_Correctness] (inject + extract)
 *
 *  Two recurring patterns are captured here:
 *
 *  1.  Frame propagation across a callee_post.  After peeling a call
 *      step from a [rust_exec_ed] hypothesis the user is left with a
 *      [frames_except rs1 rs2 dst] conjunct ([Hframe]) and a swarm of
 *      [slot_holds rs1 x bs] hypotheses for the live "passenger"
 *      slots (the seed/msg/sig_out/... slots that the call doesn't
 *      touch).  Each of those must be re-stated as
 *      [slot_holds rs2 x bs] before continuing, gated on [x <> dst].
 *      That is mechanically uniform but verbose: 20+ lines per call,
 *      30-100+ lines per protocol.  [frame_through_call] / [frame_through_call_with]
 *      do all of them at once.
 *
 *  2.  Slot propagation across the leading [REdLetZero] allocation
 *      block.  Each [REdLetZero] [rs_set_tower_ed]'s a fresh location;
 *      the input slots must be transported via [slot_holds_set_tower_other].
 *      [slot_holds_through_alloc_block] applies this for one slot.
 *
 *  Optional generic peel macros are provided ([peel_let_zero_block],
 *  [peel_call_seq_generic]) but the existing per-protocol peel tactics
 *  in each [Strong_Correctness.v] are still preferred when they need
 *  to destructure protocol-specific [strong_callee_post_*] payloads.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.Sign_Strong_Correctness.
Import ListNotations.

(* ================================================================ *)
(* §A.1. Frame propagation: default discriminate side condition       *)
(* ================================================================ *)

(** [frame_through_call Hframe] rewrites every [slot_holds rs ?x ?bs]
    hypothesis in scope into [slot_holds rs' ?x ?bs] using the frame
    [Hframe : frames_except rs rs' dst].  The side condition
    [?x <> dst] is discharged by [discriminate] (suitable when the
    slot names are bare string-literal Definitions).

    The [progress] guard prevents infinite looping on the same
    hypothesis: after a successful [apply ... in H], [H]'s type
    is rewritten to [slot_holds rs' x bs] and the next match round
    no longer fires on the old [rs] pattern (because the pattern
    matched is [slot_holds ?rs ?x ?bs] with [?rs] uniform across the
    iteration — see remarks in [frame_through_call_with] below). *)
Ltac frame_through_call Hframe :=
  repeat
    match goal with
    | H : slot_holds ?rs ?x ?bs |- _ =>
        (* Only fire on the pre-frame state — the [Hframe]'s lhs. *)
        match type of Hframe with
        | frames_except rs _ _ =>
            apply (slot_holds_frame _ _ _ _ _ Hframe) in H; [|discriminate]
        end
    end.

(* ================================================================ *)
(* §A.2. Frame propagation: user-supplied neq tactic                  *)
(* ================================================================ *)

(** [frame_through_call_with Hframe neq_tac] is like
    [frame_through_call] but uses [neq_tac] to discharge the
    inequality side condition.  Use this when slot names are wrapped
    in opaque combinators ([LE_TBytes loc_var] etc.) that
    [discriminate] does not see through directly — the typical
    [neq_tac] in this codebase is

      Ltac neq_var :=
        cbn [LE_TBytes loc_var];
        cbv [v_seed v_msg ...];
        discriminate.

    The user supplies that tactic by name. *)
Ltac frame_through_call_with Hframe neq_tac :=
  repeat
    match goal with
    | H : slot_holds ?rs ?x ?bs |- _ =>
        match type of Hframe with
        | frames_except rs _ _ =>
            apply (slot_holds_frame _ _ _ _ _ Hframe) in H; [|neq_tac]
        end
    end.

(* ================================================================ *)
(* §A.3. Helper lemma: chained [REdLetZero] propagation               *)
(* ================================================================ *)

(** [slot_holds_set_tower_other_repeat]: tactic shorthand for the
    chain

      repeat (apply slot_holds_set_tower_other; [discriminate|]);
      exact <H>

    which propagates a [slot_holds] hypothesis [H] across an arbitrary
    number of [rs_set_tower_ed] updates on different keys.  Used in
    Stage A of every strong-correctness proof to lift the precondition
    slot hypotheses across the protocol's leading [REdLetZero] block. *)
Ltac slot_holds_set_tower_other_repeat H :=
  repeat (apply slot_holds_set_tower_other; [discriminate|]); exact H.

(** Same, but with a user-supplied side tactic. *)
Ltac slot_holds_set_tower_other_repeat_with H neq_tac :=
  repeat (apply slot_holds_set_tower_other; [neq_tac|]); exact H.

(* ================================================================ *)
(* §A.4. [peel_all_let_zero] — peel leading REdLetZero allocations    *)
(* ================================================================ *)

(** [peel_all_let_zero] inverts every leading [REdLetZero] cell in a
    [rust_exec_ed] hypothesis (i.e. the leading allocation block at
    the start of each protocol body).  After this the hypothesis has
    the form [rust_exec_ed _ _ _ <inner-body> rs_alloc rs2] where
    [rs_alloc] is the state after all the fresh-slot allocations. *)
Ltac peel_all_let_zero :=
  repeat
    match goal with
    | H : rust_exec_ed _ _ _ (REdLetZero _ _ _) _ _ |- _ =>
        inversion H; subst; clear H
    end.

(* ================================================================ *)
(* §A.5. Generic [peel_call_seq] for callees whose [callee_post]      *)
(*       is a single conjunct [frames_except /\ <rest>].              *)
(* ================================================================ *)

(** Generic peel for a protocol whose [strong_callee_post_X] has
    shape [frames_except rs1 rs2 dst /\ Pres] (Lizard inject/extract
    fit this).  After

        peel_call_seq_generic Hexec callee_post_name Hframe Hres

    the running execution hypothesis [Hexec] is rebound to the
    residual rest, with new hypotheses [Hframe] and [Hres].  When the
    callee_post has more than two conjuncts (e.g. Ed25519's
    [frames_except /\ scalar_frame /\ result]), users write a
    protocol-specific peel tactic; see [peel_call_seq] in
    [Sign_Strong_Correctness.v] for that pattern. *)
Ltac peel_call_seq_generic H Hframe Hres :=
  let Hcall := fresh "Hcall" in
  let Hrest := fresh "Hrest" in
  inversion H; subst; clear H;
  match goal with
  | Hc : rust_exec_ed _ _ _ (REdCall _ _ _) _ _,
    Hr : rust_exec_ed _ _ _ _ _ _ |- _ =>
      rename Hc into Hcall; rename Hr into Hrest
  end;
  inversion Hcall; subst; clear Hcall;
  match goal with
  | Hc : _ /\ _ |- _ =>
      destruct Hc as [Hframe Hres]
  end;
  rename Hrest into H.

(** [peel_last_call_generic]: same as above but for the terminal call
    (no [REdSeq], no residual). *)
Ltac peel_last_call_generic H Hframe Hres :=
  inversion H; subst; clear H;
  match goal with
  | Hc : _ /\ _ |- _ =>
      destruct Hc as [Hframe Hres]
  end.
