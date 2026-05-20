(** * RustCmdSafegcdTactics — automation for the mechanical AST
 *    walkthrough of [fe25519_invert_producer_admitted] in
 *    [Fe25519InvertBound_Closed.v] (and the analogous chain
 *    walkthrough for safegcd / inversion successors).
 *
 *  Four tactics:
 *
 *    [discharge_leaf_call]   — close a goal of the form
 *      [exists rs2, Hexec_b (REdCall name dest args) rs1 rs2 /\ P rs2 /\ ...]
 *      by applying the right per-leaf [Fe25519BoundLeafProducers] lemma
 *      (sqr/mul/copy) based on [name].
 *
 *    [discharge_letzero_bound] — close a goal
 *      [exists rs2, Hexec_b (REdLetZero x TFp25519 body) rs1 rs2 /\ ...]
 *      by binding [v := vfp25519_zero], proving well-formedness, then
 *      threading the input [Fp25519_holds_bound] forward via
 *      [let_zero_preserves_holds_bound] and leaving the body goal
 *      open for the next tactic.
 *
 *    [seq_step_thread] — for [REdSeq c1 c2], peel c1 by applying the
 *      relevant leaf/letzero tactic, then recurse into c2 with the
 *      threaded "current holds" context.
 *
 *    [sqrN_step_chain]     — wraps the existing [sqrN_correct]
 *      analogue for in-context application against the
 *      [REdFor "_i" n (REdSeq (sqr_call ...) (copy_call ...))]
 *      idiom embedded in [fe25519_invert_body].  Currently uses the
 *      consumer form (the bound producer for sqrN is upstream future
 *      work — for now this tactic falls back to leaving the goal
 *      open with a clear marker).
 *
 *  Each tactic accepts the *name* of the "current [Fp25519_holds_bound]
 *  for the source slot" hypothesis as a tactic argument.  After the
 *  tactic fires, the renamed/updated hypothesis for the next step is
 *  introduced in the proof context under a discoverable name.
 *
 *  Compression target: each tactic invocation replaces ~30 LoC of
 *  the mechanical pattern from [producer_2step_demo].  Smoke-tested
 *  in [Fe25519InvertBound_Closed.v] §1 (Phase-2 deliverable).
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.Curve25519.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.Fe25519InvertBody.
Require Import Bedrock.End2End.Ed25519.Fe25519InvertCorrect.
Require Import Bedrock.End2End.Ed25519.Fe25519InvertBoundInstantiation.
Require Import Bedrock.End2End.Ed25519.Fe25519BoundLeafProducers.
Require Import Bedrock.End2End.Ed25519.Fe25519SqrN_Producer.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Local Notation Hexec_b :=
  (rust_exec_ed callee_post_bound callee_post_n_bound function_table_bound).

(* ================================================================== *)
(* §1. discharge_leaf_call                                             *)
(* ================================================================== *)

(** [discharge_leaf_call] is implemented as the dispatch of
    [apply_sqr_producer] / [apply_mul_producer] / [apply_copy_producer]
    below.  The dispatch is by hand because the producer signatures
    differ in arity (sqr/copy: one source; mul: two), and the
    destination + source [located_ed]s are scoped by the surrounding
    chain — they cannot be reliably read from the goal once the AST
    is unfolded inline (the variable names live INSIDE the [REdCall]
    term, not in the typing context). *)

(** [apply_sqr_producer dst src Hne Hsrc]
    [apply_copy_producer dst src Hne Hsrc]
    [apply_mul_producer dst a b Hne_a Hne_b HsrcA HsrcB]
    — produce a fresh rs2 + Hexec/Hdest/Hframe quadruple for the
      named leaf, given the destination [dst : located_ed], source
      [src] (or [a, b]), disequations between dst and source(s),
      and [Hsrc : Fp25519_holds_bound rs1 src.(loc_var) x] (or two).

    The intermediate state is named [rs2_<leaf>]; the threaded
    [Fp25519_holds_bound] hypothesis on the post-state is named
    [Hdest_<leaf>]; the frame predicate is [Hframe_<leaf>].

    These names are stable across the chain so subsequent invocations
    can pass [Hdest_sqr] (etc.) directly as the [Hsrc] for the next
    leaf. *)
(** Producer-leaf tactics.  Each takes:
      [dst : located_ed], [src(s) : located_ed],
      [Hdt : dst.(loc_type) = TFp25519],
      [Hst : src.(loc_type) = TFp25519],
      [Hne : dst.(loc_var) <> src.(loc_var)],
      [Hsrc : Fp25519_holds_bound rs src.(loc_var) x].

    When [dst] is constructed as [LFp v], its [loc_type] reduces to
    [TFp25519] definitionally, so [eq_refl] can be passed for [Hdt].
    For [src = a_loc] (a section variable), an explicit hypothesis is
    needed. *)
(** [apply_sqr_producer dst src xv Hdt Hst Hne Hsrc] —
    where [xv : F p] is the source slot's algebraic value.
    [Hsrc : Fp25519_holds_bound rs1 src.(loc_var) xv]. *)
(** Apply the sqr producer.  Takes destination, source, source-type
    proof [Hst], disequation [Hne], and the source holds-hypothesis
    [Hsrc].  Destination's type is assumed [TFp25519] (which holds
    when [dst] is constructed as [LFp _]).  Source's algebraic value
    [x] is inferred from [Hsrc]. *)
Ltac apply_sqr_producer dst src Hst Hne Hsrc :=
  let Hprod := fresh "Hprod_sqr" in
  let rs2 := fresh "rs2_sqr" in
  let Hexec := fresh "Hexec_sqr" in
  let Hdest := fresh "Hdest_sqr" in
  let Hframe := fresh "Hframe_sqr" in
  pose proof (sqr_producer_bound _ dst src _
                (@eq_refl tower_type_ed TFp25519) Hst Hne Hsrc) as Hprod;
  destruct Hprod as [rs2 [Hexec [Hdest Hframe]]].

Ltac apply_copy_producer dst src Hst Hne Hsrc :=
  let Hprod := fresh "Hprod_copy" in
  let rs2 := fresh "rs2_copy" in
  let Hexec := fresh "Hexec_copy" in
  let Hdest := fresh "Hdest_copy" in
  let Hframe := fresh "Hframe_copy" in
  pose proof (copy_producer_bound _ dst src _
                (@eq_refl tower_type_ed TFp25519) Hst Hne Hsrc) as Hprod;
  destruct Hprod as [rs2 [Hexec [Hdest Hframe]]].

(** [apply_mul_producer dst a b Hat Hbt Hne_a Hne_b HsrcA HsrcB]
      Mul-leaf producer.  [Hat/Hbt] are the source-type proofs;
      [Hne_a/Hne_b] are dst <> a/b; [HsrcA/HsrcB] the source-holds
      hypotheses.  Algebraic values inferred from holds-hypotheses. *)
Ltac apply_mul_producer dst a b Hat Hbt Hne_a Hne_b HsrcA HsrcB :=
  let Hprod := fresh "Hprod_mul" in
  let rs2 := fresh "rs2_mul" in
  let Hexec := fresh "Hexec_mul" in
  let Hdest := fresh "Hdest_mul" in
  let Hframe := fresh "Hframe_mul" in
  pose proof (mul_producer_bound _ dst a b _ _
                (@eq_refl tower_type_ed TFp25519) Hat Hbt
                Hne_a Hne_b HsrcA HsrcB) as Hprod;
  destruct Hprod as [rs2 [Hexec [Hdest Hframe]]].

(* ================================================================== *)
(* §2. discharge_letzero_bound                                         *)
(* ================================================================== *)

(** [discharge_letzero_bound Hsrc Hne] — peel a [REdLetZero x TFp25519
    body] introduction at the head of a producer existential goal,
    introducing the updated tower state under [vfp25519_zero], and
    threading [Hsrc : Fp25519_holds_bound rs1 srcname x] forward to
    the new state via [let_zero_preserves_holds_bound].
    [Hne] is the disequation [srcname <> x].

    Replaces the ~5 LoC pattern:
        eapply (rexec_let_zero callee_post_bound ... "x" TFp25519 vfp25519_zero).
        { apply zero_limbs_ed_length. }
        ...thread Hsrc forward via let_zero_preserves_holds_bound...
*)
Ltac apply_letzero_bound :=
  eapply (rexec_let_zero callee_post_bound callee_post_n_bound
            function_table_bound _ TFp25519 vfp25519_zero);
  [ unfold well_formed_ed, vfp25519_zero; apply zero_limbs_ed_length | ].

(** Update [Hsrc] in place: replace it with a new holds claim against
    the post-letzero state.  Use after [apply_letzero_bound] peels
    the [REdLetZero] frame.  [Hsrc] is the OLD holds hypothesis (about
    rs1); [Hne_src_x] is the disequation [src_var <> letzero_var].

    [t] and [v] are explicit because the new holds-claim's state
    [rs_set_tower_ed rs x (exist_tval_ed t v)] needs them. *)
Ltac thread_holds_through_letzero Hsrc Hne_src_x :=
  let Hsrc_new := fresh Hsrc "_lz" in
  pose proof (let_zero_preserves_holds_bound _ _ TFp25519 vfp25519_zero
                _ _ Hne_src_x Hsrc) as Hsrc_new.

(* ================================================================== *)
(* §3. seq_step_thread                                                 *)
(* ================================================================== *)

(** [seq_step_thread] — peel a leading [REdSeq c1 c2] by [eapply
    rexec_seq] when applied to a [Hexec_b (REdSeq c1 c2) rs1 ?rs3]
    goal (with [?rs3] existential).  Produces two sub-goals
    [Hexec_b c1 rs1 ?rs2] and [Hexec_b c2 ?rs2 ?rs3], with
    [?rs2] shared.

    The intermediate [?rs2] is left as an evar to be unified by the
    [c1] subgoal's witness. *)
Ltac seq_step_thread :=
  eapply (rexec_seq callee_post_bound callee_post_n_bound
                    function_table_bound).

(** [seq_step_skip_thread] — peel a leading [REdSeq REdSkip c2] by
    [eapply rexec_seq; [apply rexec_skip|]].  Common idiom in
    [fe25519_invert_body]'s post-letzero sub-AST. *)
Ltac seq_step_skip_thread :=
  eapply (rexec_seq callee_post_bound callee_post_n_bound
                    function_table_bound);
  [ apply (rexec_skip callee_post_bound callee_post_n_bound
                      function_table_bound) | ].

(* ================================================================== *)
(* §4. sqrN_step_chain                                                 *)
(* ================================================================== *)

(** [apply_sqrN_producer n acc scratch Hne_as Hacc] — produce
    [Hexec_b (sqrN n acc scratch) rs1 ?rs2] together with the
    post-condition [Fp25519_holds_bound ?rs2 acc (F.pow x (2^n))],
    where [Hacc : Fp25519_holds_bound rs1 acc x] and
    [Hne_as : acc <> scratch].

    Introduces [rs2_sqrN], [Hexec_sqrN], [Hdest_sqrN], [Hframe_sqrN]
    into the context — names parallel to [apply_sqr_producer] for
    chain-level uniformity. *)
Ltac apply_sqrN_producer n acc scratch Hne_as Hacc :=
  let Hprod := fresh "Hprod_sqrN" in
  let rs2 := fresh "rs2_sqrN" in
  let Hexec := fresh "Hexec_sqrN" in
  let Hdest := fresh "Hdest_sqrN" in
  let Hframe := fresh "Hframe_sqrN" in
  pose proof (sqrN_producer_bound n acc scratch _ _
                Hne_as Hacc) as Hprod;
  destruct Hprod as [rs2 [Hexec [Hdest Hframe]]].

(** [sqrN_step_chain] — alias for [apply_sqrN_producer], mirroring
    the [peel_letzero] / [peel_seq] family of names. *)
Tactic Notation "sqrN_step_chain" constr(n) constr(acc) constr(scratch)
                                  hyp(Hne) hyp(Hacc) :=
  apply_sqrN_producer n acc scratch Hne Hacc.

(* ================================================================== *)
(* §5. Tactic notation aliases (for readability in call-site usage)    *)
(* ================================================================== *)

Tactic Notation "produce_sqr" uconstr(dst) uconstr(src)
                                hyp(Hst) hyp(Hne)
                                hyp(Hsrc) :=
  apply_sqr_producer dst src Hst Hne Hsrc.

Tactic Notation "produce_copy" uconstr(dst) uconstr(src)
                                 hyp(Hst) hyp(Hne)
                                 hyp(Hsrc) :=
  apply_copy_producer dst src Hst Hne Hsrc.

Tactic Notation "produce_mul" uconstr(dst) uconstr(a) uconstr(b)
                                hyp(Hat) hyp(Hbt)
                                hyp(Hne_a) hyp(Hne_b)
                                hyp(Hsa) hyp(Hsb) :=
  apply_mul_producer dst a b Hat Hbt Hne_a Hne_b Hsa Hsb.

Tactic Notation "peel_letzero" :=
  apply_letzero_bound.

Tactic Notation "peel_seq" :=
  seq_step_thread.

Tactic Notation "peel_seq_skip" :=
  seq_step_skip_thread.

Tactic Notation "thread_letzero" constr(Hsrc) constr(Hne) :=
  thread_holds_through_letzero Hsrc Hne.
