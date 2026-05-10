(** * RustCmdRupicolaTactics — Tier 5 tactic infrastructure
 *
 *  An [Ltac]-level dispatcher for the [compile_red_*] lemma family in
 *  [RustCmdRupicola.v] (Tier 1+2), [RustCmdRupicolaTyped.v] (Tier 3),
 *  and [RustCmdRupicolaEd25519.v] (Tier 4).  Mirrors Rupicola's
 *  [compile_step] in
 *  [fiat-crypto/rupicola/src/Rupicola/Lib/Compiler.v] (line ~755).
 *
 *  The user proves a [rhoare callee_post rs c pred] goal by repeatedly
 *  applying [compile_step]: for each [rust_cmd_ed] constructor head,
 *  dispatch the corresponding compile lemma.  Side conditions
 *  (sexpr evaluation, callee-frame disjointness, byte-store bounds,
 *  loop measure/invariant) become subgoals that the user discharges
 *  manually — exactly like Rupicola where [compile] leaves residual
 *  obligations to the caller.
 *
 *  ** Dispatch table
 *
 *    REdSkip          -> compile_red_skip       (post becomes pred rs)
 *    REdSeq c0 c1     -> compile_red_seq        (eapply: 2 subgoals,
 *                                                pred0 inferred)
 *    REdLetZero       -> compile_red_let_zero   (intro v + Hwf, body)
 *    REdLetU64        -> compile_red_let_u64    (eapply: subgoal for
 *                                                eval + body)
 *    REdScalarSet     -> compile_red_scalar_set (eapply: subgoal for
 *                                                eval + post)
 *    REdCall          -> compile_red_call       (intro rs' + Hcp,
 *                                                user destructs the
 *                                                strong_callee_post
 *                                                branch)
 *    REdIfNz          -> compile_red_if_nz      (intros for both arms)
 *    REdWhileNz       -> manual                 (requires a measure
 *                                                + invariant — print
 *                                                hint and stop)
 *    REdByteStore     -> compile_red_byte_store (eapply: subgoals for
 *                                                idx, val, type, get,
 *                                                post)
 *    REdByteLoad      -> compile_red_byte_load  (eapply: subgoals for
 *                                                idx, type, get, nth,
 *                                                post)
 *
 *  ** Residual side conditions
 *
 *  After [compile] runs, the user is left with:
 *    - [eval_sexpr_ed rs e = Some v] for [REdLetU64] / [REdScalarSet]
 *      / [REdByteStore] / [REdByteLoad] / [REdIfNz];
 *    - [callee_post fname args dst rs rs' -> pred rs'] for each
 *      [REdCall] (the user destructs the relevant branch of
 *      [strong_callee_post] and uses [slot_holds_inj] /
 *      [slot_holds_frame] from [Sign_Strong_Correctness.v]);
 *    - the byte-store / byte-load load-current-bytes hypotheses.
 *
 *  The Tier-4 lemmas in [RustCmdRupicolaEd25519.v] already package the
 *  per-callee work for the canonical Ed25519 sub-patterns; this module
 *  is for the residual surface that doesn't have a Tier-4 lemma yet.
 *
 *  Status (2026-05-10): [compile_step] + [compile] Ltac defined; demo
 *  theorem [demo_sha512_correct] Qed using [compile] driver.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.RustCmdRupicola.
Require Import Bedrock.End2End.Ed25519.Sign_Strong_Correctness.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. compile_step — head-constructor dispatcher                   *)
(* ================================================================ *)

(** Apply the appropriate [compile_red_*] lemma based on the head
    constructor of the [rust_cmd_ed] in the current [rhoare] goal.
    For lemmas whose obligations include a [forall]-quantified body
    (let_zero, call, if_nz), [intros] is run automatically so the user
    sees the per-state subgoal directly. *)
Ltac compile_step :=
  lazymatch goal with
  | |- rhoare _ _ REdSkip _ =>
      apply compile_red_skip
  | |- rhoare _ _ (REdSeq _ _) _ =>
      eapply compile_red_seq
  | |- rhoare _ _ (REdLetZero _ _ _) _ =>
      apply compile_red_let_zero; intros
  | |- rhoare _ _ (REdLetU64 _ _ _) _ =>
      eapply compile_red_let_u64
  | |- rhoare _ _ (REdScalarSet _ _) _ =>
      eapply compile_red_scalar_set
  | |- rhoare _ _ (REdCall _ _ _) _ =>
      apply compile_red_call; intros
  | |- rhoare _ _ (REdIfNz _ _ _) _ =>
      apply compile_red_if_nz; intros
  | |- rhoare _ _ (REdWhileNz _ _) _ =>
      fail "compile_step: REdWhileNz needs measure + invariant; apply compile_red_while_nz manually with explicit M, lt, inv"
  | |- rhoare _ _ (REdByteStore _ _ _) _ =>
      eapply compile_red_byte_store
  | |- rhoare _ _ (REdByteLoad _ _ _) _ =>
      eapply compile_red_byte_load
  (* After [eapply compile_red_seq], the second subgoal has shape
     [forall rs_mid, pred0 rs_mid -> rhoare ... c1 pred1].  Strip
     the binders so the inner [rhoare] becomes the next dispatch
     target. *)
  | |- forall _, _ -> rhoare _ _ _ _ =>
      intros
  | |- _ =>
      fail "compile_step: not a rhoare goal or unrecognized head constructor"
  end.

(** Repeated [compile_step] until no progress.  Side conditions become
    subgoals; the user discharges them.  The [progress] guard is built
    into [compile_step]'s [fail] branch. *)
Ltac compile := repeat compile_step.

(* ================================================================ *)
(* §2. compile_callee — per-leaf strong_callee_post destructor      *)
(* ================================================================ *)

(** When the call is to a known Ed25519 leaf, [compile_step] has
    already applied [compile_red_call] and run [intros], leaving a
    hypothesis [Hcp : strong_callee_post fname args dst rs rs']
    (or some fresh name) in context.  [strong_callee_post] unfolds
    to a conjunction of a frame fact and a [match fname, args]
    dispatch that reduces to the leaf's [exists ...] body.
    [compile_callee] destructs that conjunction and reduces the
    [match] for the most common single-source leaf names.

    For multi-source branches (scalar_muladd, memmove pairs), prefer
    the Tier-4 lemmas in [RustCmdRupicolaEd25519.v] which collapse
    the per-call destructure into one rewrite. *)
Ltac compile_callee :=
  match goal with
  | H : strong_callee_post "sha512_64" _ _ _ _ |- _ =>
      let Hframe := fresh "Hframe" in
      let Hbranch := fresh "Hbranch" in
      destruct H as [Hframe Hbranch]; cbn in Hbranch
  | H : strong_callee_post "scalar_reduce" _ _ _ _ |- _ =>
      let Hframe := fresh "Hframe" in
      let Hbranch := fresh "Hbranch" in
      destruct H as [Hframe Hbranch]; cbn in Hbranch
  | H : strong_callee_post "ed25519_compress" _ _ _ _ |- _ =>
      let Hframe := fresh "Hframe" in
      let Hbranch := fresh "Hbranch" in
      destruct H as [Hframe Hbranch]; cbn in Hbranch
  | H : strong_callee_post "ed25519_scalarmult_base" _ _ _ _ |- _ =>
      let Hframe := fresh "Hframe" in
      let Hbranch := fresh "Hbranch" in
      destruct H as [Hframe Hbranch]; cbn in Hbranch
  | H : strong_callee_post "clamp_64" _ _ _ _ |- _ =>
      let Hframe := fresh "Hframe" in
      let Hbranch := fresh "Hbranch" in
      destruct H as [Hframe Hbranch]; cbn in Hbranch
  | H : strong_callee_post "memmove_a_from_h" _ _ _ _ |- _ =>
      let Hframe := fresh "Hframe" in
      let Hbranch := fresh "Hbranch" in
      destruct H as [Hframe Hbranch]; cbn in Hbranch
  | H : strong_callee_post "memmove_prefix_from_h" _ _ _ _ |- _ =>
      let Hframe := fresh "Hframe" in
      let Hbranch := fresh "Hbranch" in
      destruct H as [Hframe Hbranch]; cbn in Hbranch
  end.

(* ================================================================ *)
(* §3. Demo theorem — single sha512 call                            *)
(* ================================================================ *)

(** Minimal end-to-end demonstration that the framework + dispatcher
    work together.  The protocol [demo_sha512_rs] hashes [input] (a
    user-supplied input slot) into [buf] then halts.  The compile
    driver applies [compile_red_seq] + [compile_red_call] + [compile_red_skip]
    via [compile_step] dispatch, leaving the [strong_callee_post]
    obligation as the only manual work.

    A purely Tier-4 alternative would use
    [compile_red_sha512_then_reduce] from [RustCmdRupicolaEd25519.v]
    when one wants to also reduce mod L; here we keep the demo at the
    Tier-1 level so it exercises [compile_step] dispatch directly. *)
Definition demo_sha512_rs (input_loc buf_loc : located_ed) : rust_cmd_ed :=
  REdSeq (REdCall "sha512_64" buf_loc [input_loc]) REdSkip.

Theorem demo_sha512_correct :
  forall (rs : rust_state_ed) (input_var buf_var : var) (n : nat)
         (input_bs : list Byte.byte),
    slot_holds rs input_var input_bs ->
    Datatypes.length input_bs = n ->
    rhoare strong_callee_post rs
      (demo_sha512_rs
         {| loc_var := input_var; loc_type := TBytes n |}
         {| loc_var := buf_var;   loc_type := TBytes 64 |})
      (fun rs' => slot_holds rs' buf_var (sha512_full_spec input_bs)).
Proof.
  intros rs input_var buf_var n input_bs Hin _Hin_len.
  unfold demo_sha512_rs.
  (* Drive the constructor structure with the dispatcher.  After
     [compile], we have two subgoals (sharing an evar [?pred0] from
     [eapply compile_red_seq]):
       SG1: [?pred0 rs'] with [Hcp : strong_callee_post "sha512_64"
              ... rs rs'] in context (the call obligation).
       SG2: [pred rs_mid] with [Hpred0 : ?pred0 rs_mid] in context
              (the post-skip leftover, where [pred] is the original
              user post). *)
  compile.
  - (* SG1: discharge the call obligation by destructing the
       sha512_64 branch of strong_callee_post.  Pick
       [?pred0 := fun rs' => slot_holds rs' buf_var
                  (sha512_full_spec input_bs)] implicitly via Htgt. *)
    compile_callee.
    destruct Hbranch as [src_bs [Hsrc Htgt]].
    pose proof (slot_holds_inj _ _ _ _ Hsrc Hin) as Heq; subst src_bs.
    exact Htgt.
  - (* SG2: [Hpred0 : slot_holds rs_mid buf_var
                       (sha512_full_spec input_bs)] (the evar from
       SG1 unified to this) and the goal is the same.  Direct. *)
    assumption.
Qed.

(** ** Print Assumptions sanity (run after build):
        Print Assumptions demo_sha512_correct.
    Should report parameters from [Sign_Strong_Correctness.v]
    (sha512_full_spec, scalar_reduce_spec, ...) — these are the
    Gallina specs imported as [Parameter] there.  No new axioms
    introduced by this file. *)

(** ** How to use [compile] in your own protocols

    1. State the goal as
         [rhoare strong_callee_post rs MY_PROTOCOL (fun rs' => ...)].
    2. [intros] / [unfold MY_PROTOCOL].
    3. Run [compile].  The structural [REdSeq]/[REdCall] skeleton
       collapses; the residual goals are one per [REdCall] (plus the
       [REdSkip] terminator if present).
    4. For each [REdCall] subgoal, run [compile_callee] (or destructure
       [strong_callee_post] manually); use [slot_holds_inj] to identify
       source bytes and [slot_holds_frame] to carry side slots through
       the call's frame.
    5. Discharge byte-store / byte-load load-current hypotheses by
       [eassumption] or by tracking the slot through prior writes.
    6. For [REdLetU64] / [REdScalarSet], discharge the
       [eval_sexpr_ed] obligation via [reflexivity] or [cbn] +
       arithmetic.
    7. For [REdWhileNz], do NOT use [compile_step]; manually
       [eapply compile_red_while_nz] with an explicit measure
       (typically [nat] + [Peano.lt]) and invariant.

    For the Ed25519 sign body, the Tier-4 lemmas in
    [RustCmdRupicolaEd25519.v] collapse 7+ calls into 4 invocations
    that are direct one-shot rewrites — preferable to running
    [compile] all the way down.

    Roadmap:
    - Add [compile_callee] arms for memmove pairs (multi-source).
    - Hint database [compile_db] with [Hint Resolve] for each
      [compile_red_*] (alternative dispatch path via [eauto with
      compile_db]).
    - [Derive ... SuchThat ... As ...] automation à la Rupicola so
      the protocol body is _synthesized_ from the Gallina reference.
*)
