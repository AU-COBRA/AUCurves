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
(* §A.2b. Frame propagation through a [rs_set_scalar_ed]-shifted LHS  *)
(* ================================================================ *)

(** **Convertibility gap (flagged in commit 5620503).**  After an
    [REdLetU64] step (e.g. Ed25519 sign's [v_msg_len], Schnorr sign's
    [sn_chal_hash_len], Schnorr verify's [sn_verify_chal_len], XEdDSA
    sign's [xs_chal_hash_len]) the running execution hypothesis is
    over a state of shape [rs_set_scalar_ed rs0 k v].  When the next
    callee_post is peeled, the [Hframe] hypothesis is
    [frames_except (rs_set_scalar_ed rs0 k v) rs1 dst] — its LHS does
    NOT syntactically equal [rs0] even though [slot_holds] reads only
    the tower env and is therefore definitionally equal under that
    shift.

    [slot_holds_rs_set_scalar_ed] is the matching rewrite lemma.  Its
    statement is essentially [slot_holds (rs_set_scalar_ed rs k v) y bs
    = slot_holds rs y bs] (provable by [reflexivity], since
    [rs_tower_ed] of a [rs_set_scalar_ed] record reduces to the
    underlying [rs_tower_ed]).

    With this lemma in hand, [frame_through_call_conv_with] handles
    the convertibility gap by first normalising the [Hframe] hypothesis
    so its LHS matches whichever shape the existing [slot_holds]
    hypotheses are in, and then dispatching to the standard
    [frame_through_call_with] loop.

    Two-direction tactic: tries Hframe in shape
       [frames_except rs0                 rs1 dst]  (already normal), AND
       [frames_except (rs_set_scalar_ed rs0 k v) rs1 dst]
    by [change]-folding the latter to the former on each slot_holds
    that matches the underlying [rs0]. *)
Lemma slot_holds_rs_set_scalar_ed :
  forall rs x v y bs,
    slot_holds (rs_set_scalar_ed rs x v) y bs <-> slot_holds rs y bs.
Proof. intros; reflexivity. Qed.

(** [frame_through_call_conv_with Hframe neq_tac]: identical to
    [frame_through_call_with], but uses convertibility-aware unification
    so that [slot_holds rs0 y bs] hypotheses can be framed by an
    [Hframe : frames_except (rs_set_scalar_ed rs0 k v) rs1 dst] (and
    vice-versa).

    Implementation note: we use the standard apply-with-conversion
    pattern — the [apply (slot_holds_frame _ _ _ _ _ Hframe) in H]
    unifier sees [slot_holds_frame]'s first state argument as the
    [rs1] of [frames_except rs1 rs2 dst], which is the [Hframe] LHS;
    and it sees the third (slot-holds input) state argument as that
    same [rs1].  Coq's [apply] uses higher-order pattern unification
    here that goes via convertibility, so it succeeds whenever the
    two state expressions are convertible (which is exactly our case
    after a [rs_set_scalar_ed] update).

    The trick is that the outer [match] needs to fire on a
    [slot_holds] hypothesis whose state expression is the underlying
    [rs0] — bare [match type of Hframe with frames_except rs _ _ end]
    fails when the LHS is [rs_set_scalar_ed rs0 k v] and the hypothesis
    is [slot_holds rs0 y bs] (different syntactic shapes).  We solve
    that by using [tryif] to try the original match, and otherwise
    falling back to the [rs_set_scalar_ed]-specific shape. *)
Ltac frame_through_call_conv_with Hframe neq_tac :=
  (* Phase 1: greedy syntactic frame (handles all "normal" calls).
     Identical to [frame_through_call_with]. *)
  frame_through_call_with Hframe neq_tac;
  (* Phase 2: lift any remaining [slot_holds rs0 x bs] hypothesis
     whose [rs0] is the underlying tower-state of an
     [rs_set_scalar_ed rs0 k v] Hframe LHS.

     We pre-normalise H with [change] to the Hframe-LHS shape; the
     [change] succeeds by record-projection iota whenever rs0 is the
     base of an [rs_set_scalar_ed] sitting in Hframe's LHS.  After
     [change], Phase-1 style syntactic framing succeeds. *)
  let rec lift_one :=
    match type of Hframe with
    | frames_except ?rs_lhs _ _ =>
        match goal with
        | H : slot_holds ?rs ?x ?bs |- _ =>
            (* Try to lift: succeeds only when [change] succeeds, i.e.,
               when rs0 (= rs here) is the base of rs_lhs's
               [rs_set_scalar_ed]. *)
            change (slot_holds rs_lhs x bs) in H;
            apply (slot_holds_frame _ _ _ _ _ Hframe) in H; [|neq_tac]
        end
    end in
  repeat (lift_one;
          (* Run Phase 1 again to sweep up any newly-converted hyps
             alongside the rest. *)
          frame_through_call_with Hframe neq_tac).

(** Alias: [frame_through_call_conv Hframe] = the conv-aware version
    with [discriminate] as the side tactic. *)
Ltac frame_through_call_conv Hframe :=
  frame_through_call_conv_with Hframe discriminate.

(** [frame_after_let_u64 Hframe neq_tac]: explicit handler for the
    post-[REdLetU64] situation.  This is just an alias for
    [frame_through_call_conv_with] but named to match the call site
    where it's typically deployed (right after the LetU64 step's
    [Hframe] has been peeled).

    Use this name in proofs where the convertibility shift makes the
    intent clearer; mechanically it's identical to
    [frame_through_call_conv_with]. *)
Ltac frame_after_let_u64 Hframe neq_tac :=
  frame_through_call_conv_with Hframe neq_tac.

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
