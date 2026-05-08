(** * SepCallReflect — Reflective replacement for [straightline_call].

    Research feasibility test (~1h spike).  Replaces
    [bedrock2.ProgramLogic.straightline_call] with a thinner tactic that
    avoids the [Proper_call + eabstract (solve [Morphisms.solve_proper])]
    combination.  Each [straightline_call] expansion currently emits ~30
    KB of proof term across many call sites in
    [Scalarmult_Impl_64.ed25519_scalarmult_base_correct] which punishes
    Qed kernel-check.

    The bedrock2 [WeakestPrecondition.call] is just a notation for
    [Semantics.call] (see [WeakestPrecondition.v:124]), and
    [Semantics.weaken_call] is a Qed-sealed lemma directly equivalent to
    the [Proper_call] instance combined with a single
    [pointwise_relation]-impl chain.  We use [weaken_call] DIRECTLY,
    skipping class resolution and the [eabstract] subterm.

    ** Design rationale (Outcome B, restricted)
    ---------------------------------------------
    The user requested a [vm_compute]-driven boolean check.  In contrast
    to [seps_pick_iff1_decb] (which lifts a [seps] permutation index out
    of the proof term), there is no obvious decidable side-condition in
    a [WeakestPrecondition.call] discharge: the spec hypothesis directly
    matches the goal up to post-weakening, and the post-weakening is the
    user's residual proof obligation.  So the right "reflective"
    replacement is structural: collapse the [Proper_call]-tower into one
    [weaken_call] application.  No [vm_compute] needed, and no
    typeclass-pre-resolution trap (which would otherwise reproduce the
    [SepDeep.deep_ecancel] OOM symptom — see
    [Scalarmult_Impl_64.v:34-50] STATUS comment).

    ** Restrictions
    ---------------
    Same as [straightline_call]: looks for [WeakestPrecondition.call _ ?f
    _ _ _ _] in the goal and a hypothesis of type [callee_spec
    functions].  Works for ANY [spec_of] shape (parametric in the spec).
    Trade-off: the post-weakening obligation is left UNFOLDED — the
    caller still does [intros ? ? ? ?] etc. as before, but the pre-call
    Proper bloat is gone.

    ** Wiring trial 2026-05-08 — DROP-IN BLOCKED
    -------------------------------------------
    Tried swapping [straightline_call] -> [vm_call] at two of R10's four
    call sites in [Scalarmult_Impl_64.ed25519_scalarmult_base_correct]:

      1. Line 628 (1st [from_bytes]):  the b1 call site at line 712
         hard-codes the auto-introduced memory variable [a0].
         [straightline_call]'s [intros ? ? ? ?] yielded [a0] (the
         third intro slot picks up an [a0] name in this context);
         [vm_call] yielded a different name, breaking the downstream
         [assert (Hsep_b1 : ... a0)].  Fixable with explicit
         [intros tr0 m0 a0 H] but invasive.

      2. Line 771 (parametric call):  the [match goal with H : _ = nil
         /\ _ = _ /\ exists _ : list Init.Byte.byte, _ |- _ => destruct H
         ...]  at line 789 expects the hyp coming out of the call to
         have a specific 3-conjunct shape.  [straightline_call] (via
         [Proper_call])  produces this shape; [vm_call] (via
         [weaken_call]) produces an iso but textually-different shape
         (likely a [Basics.flip]-wrapped variant from how Proper unifies
         the post argument).  Coq's structural match doesn't see
         through the wrapper, fails with "No matching clauses for
         match" at line 789.  Fixable with [unfold] or a richer match
         pattern.

    Conclusion: [vm_call] is sound + ~40% smaller proof terms
    (synthetic), but a true drop-in for [straightline_call] needs (a)
    explicit-name [intros] OR (b) a normalizer to make the post hyp's
    syntactic shape match what existing Ltac patterns expect.  Both
    fixable; deferred.  The infrastructure here is reusable for the
    next session that takes one of those paths, OR for fresh proofs
    written against [vm_call]'s output shape from the start. *)

From Stdlib Require Import List ZArith String.
Require Import coqutil.Word.Interface coqutil.Map.Interface.
Require Import bedrock2.Semantics bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties bedrock2.ProgramLogic.

Local Open Scope string_scope.

(** [reflect_call_post]: the workhorse.  Equivalent to
    [Semantics.weaken_call] reshaped to match a [WeakestPrecondition.call]
    goal directly.  Fully Qed-sealed. *)
Section Reflect.
  Context {width : Z} {BW : Bitwidth.Bitwidth width}
          {word : word.word width} {mem : map.map word Init.Byte.byte}
          {locals : map.map String.string word}
          {ext_spec : ExtSpec}
          {word_ok : word.ok word}
          {mem_ok : map.ok mem}
          {locals_ok : map.ok locals}
          {ext_spec_ok : ext_spec.ok ext_spec}.

  Lemma reflect_call_post :
    forall (functions : env) (fname : String.string)
           (tr : trace) (m : mem) (args : list word)
           (post1 post2 : trace -> mem -> list word -> Prop),
      WeakestPrecondition.call functions fname tr m args post1 ->
      (forall tr' m' rets, post1 tr' m' rets -> post2 tr' m' rets) ->
      WeakestPrecondition.call functions fname tr m args post2.
  Proof.
    intros. eapply Semantics.weaken_call; eassumption.
  Qed.

End Reflect.

(** [vm_call] — drop-in lighter alternative to [straightline_call].

    Goal: [WeakestPrecondition.call functions f tr m args post].

    Looks up a hypothesis [Hcall : callee_spec functions] (where
    [callee_spec] is the unique [spec_of f] instance), applies
    [reflect_call_post] with [post1] := the body of [Hcall] (fully
    eapply'd), and leaves the user with the post-weakening obligation
    [forall tr' m' rets, post1 tr' m' rets -> post tr' m' rets], pre-
    introduced via [intros ? ? ? ?] so it matches the existing
    [straightline_call] interface.

    Difference from [straightline_call]:
      - No [Proper_call] eapply, so no class-resolution overhead.
      - No [eabstract (solve [Morphisms.solve_proper])] tower, which
        usually inflates the proof term with [_subproof] abstractions.

    This is just [eapply Semantics.weaken_call; cycle 1; [eapply Hcall |
    intros ? ? ? ?]] under the hood, but written as a NEW tactic so it
    coexists with [straightline_call] in the file. *)
Ltac vm_call :=
  lazymatch goal with
  | |- WeakestPrecondition.call ?functions ?callee _ _ _ _ =>
    let callee_spec := lazymatch constr:(_:spec_of callee) with ?s => s end in
    let Hcall := lazymatch goal with H: callee_spec functions |- _ => H end in
    eapply reflect_call_post;
      [ eapply Hcall | intros ? ? ? ? ]
  end.

(** ** Synthetic test — Outcome A success criterion.

    Build a tiny synthetic 1-call WP goal in two ways.  Compare proof-
    term sizes with [Print Term Size] (or via [Time Qed.] kernel time).

    To minimize harness boilerplate we use a fully abstract [spec_of]:
    the goal looks like [WeakestPrecondition.call e f tr m args post]
    and the hypothesis is [forall tr m args, P -> call e f tr m args
    post0].  Both [vm_call] and [straightline_call] should solve this. *)
Section Test.
  Local Open Scope string_scope.
  Context {width : Z} {BW : Bitwidth.Bitwidth width}
          {word : word.word width} {mem : map.map word Init.Byte.byte}
          {locals : map.map String.string word}
          {ext_spec : ExtSpec}
          {word_ok : word.ok word}
          {mem_ok : map.ok mem}
          {locals_ok : map.ok locals}
          {ext_spec_ok : ext_spec.ok ext_spec}.

  (* A toy spec: callee "foo" takes one arg, no return; pre = True;
     post = (fun tr' m' rets => tr' = tr /\ m' = m /\ rets = nil). *)
  Local Instance spec_of_foo : spec_of "foo" :=
    fun functions =>
      forall tr m a, True -> WeakestPrecondition.call functions "foo" tr m
                                                      (cons a nil)
                       (fun tr' m' rets => tr' = tr /\ m' = m /\ rets = nil).

  (* Test goal: given the foo spec, prove a call site whose post is
     a trivial weakening (drop the rets=nil clause).
     Proof via vm_call: *)
  Lemma test_vm_call (functions : env) (Hcall : spec_of_foo functions)
        (tr : trace) (m : mem) (a : word) :
    WeakestPrecondition.call functions "foo" tr m (cons a nil)
      (fun tr' m' _ => tr' = tr /\ m' = m).
  Proof.
    vm_call.
    (* Goal 1: True (the pre).  Goal 2 (after intros ? ? ? ?):
       given (tr' = tr /\ m' = m /\ rets = nil), prove (tr' = tr /\ m' = m). *)
    - exact I.
    - destruct H as (Htr & Hm & _). split; assumption.
  Qed.

  (* Same lemma, proven via the upstream straightline_call. *)
  Lemma test_straightline_call (functions : env) (Hcall : spec_of_foo functions)
        (tr : trace) (m : mem) (a : word) :
    WeakestPrecondition.call functions "foo" tr m (cons a nil)
      (fun tr' m' _ => tr' = tr /\ m' = m).
  Proof.
    straightline_call.
    - exact I.
    - destruct H as (Htr & Hm & _). split; assumption.
  Qed.

End Test.

(** ** Proof-term size comparison — empirical result (2026-05-08)

    Build with the lines below uncommented to re-verify on this machine:

      Set Printing Depth 100000.
      Set Printing Width 200.
      Print test_vm_call.
      Print test_straightline_call.

    Measured on the synthetic 1-call test above (rocq-9, [(mode native)],
    width-parametric Section context, abstract [spec_of "foo"]):

      | Tactic              | Chars  | Lines |
      |---------------------|--------|-------|
      | [vm_call]           | 1503   | 16    |
      | [straightline_call] | 2520   | 34    |

    Delta: ~40% chars / ~52% lines smaller.  The bloat in the
    [straightline_call] term lives in the three nested
    [Morphisms.pointwise_relation] casts that the [Proper_call]
    application threads through (one per [pointwise_relation] in the
    [Proper_call] type) and which the kernel re-elaborates on Qed.
    [vm_call] applies [weaken_call] directly, sidestepping all three.

    Caveat: this is the BEST CASE.  In real call sites the
    [eabstract (solve [Morphisms.solve_proper])] path also adds
    [_subproof] abstractions that bloat the .vo further.  We did NOT
    measure those — that would require porting [vm_call] to a real call
    site (e.g. one of the 4 [straightline_call] hits in
    [Scalarmult_Impl_64.v]) and timing the lemma's [Qed].  The user can
    drop in [vm_call] for [straightline_call] in any of those four sites
    to test on a realistic proof; the [intros ? ? ? ?] post-introduction
    pattern is identical.

    The vm_compute angle of the request was speculative — there is NO
    decidable side-condition in a [WeakestPrecondition.call] discharge
    (cf. [seps_pick_iff1_decb]'s index bound).  The reflective gain
    here is pure structural simplification.  See file header for design
    rationale. *)
