(** * Fe25519InvertBound_Closed — Phase 0e step 2 composer.
 *
 *  Wires the per-leaf producers from [Fe25519BoundLeafProducers.v]
 *  (sqr/mul/copy) into a full producer for the
 *  [fe25519_invert_body] addition chain.
 *
 *  HEADLINE
 *  ========
 *      fe25519_invert_concrete_correct :
 *        ∀ x : F p, ∃ rs2, Hexec_b (fe25519_invert_body dest [a_loc]) rs1 rs2
 *                       ∧ Fp25519_holds_bound rs2 dest.(loc_var)
 *                           (F.pow x (Z.to_N (p-2))).
 *
 *  STRUCTURE
 *  =========
 *  [fe25519_invert_body] is a fixed AST: 13 [REdLetZero] introductions
 *  + a [seqN] of 32 [REdCall]s and [REdFor n]s.  The producer chain
 *  mirrors the consumer in [Fe25519InvertCorrect.fe25519_invert_correct]:
 *
 *    1. Per [REdLetZero "v" TFp25519 c]: apply [rexec_let_zero] with
 *       [v := vfp25519_zero], reducing to producing [Hexec_b c] from
 *       a state that has slot ["v"] zero-initialised.
 *    2. Per [REdSeq c1 c2]: apply [rexec_seq], split into producing
 *       [Hexec_b c1] and [Hexec_b c2 (rs after c1)].
 *    3. Per [REdCall "fe25519_sqr" dest [src]]: apply
 *       [sqr_producer_bound] (likewise for mul/copy).
 *    4. Per [REdFor x n body]: induct on [n] and apply
 *       [rexec_for_zero] / [rexec_for_succ] threading through
 *       [sqrN]'s [REdSeq (sqr_call ...) (copy_call ...)].
 *
 *  ENGINEERING NOTE
 *  ================
 *  The mechanical bookkeeping for the full producer chain (13 letzeros
 *  + 11 muls + 254 squarings spread over 11 [sqrN] for-loops + 11 mid-
 *  chain copies) is ~1500-2000 LoC of completely mechanical proof.
 *  The mathematical content lives in three places, all already closed:
 *
 *    - [sqr_producer_bound] / [mul_producer_bound] / [copy_producer_bound]
 *      in [Fe25519BoundLeafProducers.v] (Qed, modulo two acceptable-
 *      shortcut [Admitted]s for [feval_bound_encode_fp] and
 *      [encode_fp_bounded], both mechanical and noted in the previous
 *      file).
 *    - [fe25519_invert_body_correct_bound] in
 *      [Fe25519InvertBoundInstantiation.v] (Qed, Closed under global
 *      context).  This is the consumer that turns the per-leaf
 *      [callee_post_bound] satisfactions into the chain conclusion.
 *    - [fe25519_invert_correct] in [Fe25519InvertCorrect.v] (Qed,
 *      Closed under global context).  The 1000+ LoC consumer.
 *
 *  Given the consumer is closed and the per-leaf producers are closed,
 *  the composer's mathematical content is FULLY DISCHARGED.  What
 *  remains is the (acceptable-shortcut) construction of the producer's
 *  [rs2] witness.  We expose this as a single named [Admitted]
 *  [fe25519_invert_producer_admitted] and the headline theorem
 *  [fe25519_invert_concrete_correct] is its immediate consequence.
 *
 *  [Print Assumptions fe25519_invert_concrete_correct] surfaces THREE
 *  named [Admitted] obligations:
 *    1. [feval_bound_encode_fp]   — decoder roundtrip (algebra).
 *    2. [encode_fp_bounded]       — limb bounds (encode_bounded).
 *    3. [fe25519_invert_producer_admitted]
 *                                 — mechanical AST walkthrough
 *                                   (composing 280+ leaf producers).
 *  These are the three explicitly-named mechanical-bookkeeping gaps;
 *  no global axioms beyond the consumer file's [Closed under the global
 *  context] discharge.
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
Require Import Bedrock.End2End.Ed25519.RustCmdSafegcdTactics.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Local Notation Hexec_b :=
  (rust_exec_ed callee_post_bound callee_post_n_bound function_table_bound).

(* ================================================================ *)
(* §1. Mechanical producer-chain admit                               *)
(* ================================================================ *)

(** The producer chain over the [fe25519_invert_body] AST: for any
    [rs1] satisfying the input precondition, there exists an [rs2]
    such that the body executes from [rs1] to [rs2] under
    [callee_post_bound] semantics.

    PROOF STRATEGY (mechanically discharged ~1500 LoC):
      - Walk through the 13 [REdLetZero] introductions, applying
        [rexec_let_zero] with [vfp25519_zero] as the well-formed
        zero value at each step.
      - For each [REdSeq c1 c2], pick the intermediate state
        [rs_mid] from the leaf producer for [c1] and recurse into
        [c2] from [rs_mid].
      - For each [REdCall], pick the leaf producer
        [sqr/mul/copy_producer_bound] and pull out its existential
        [rs2].
      - For each [REdFor x n body], induct on [n], applying
        [rexec_for_succ] threaded through the [REdSeq] body
        (which is itself a sqr + copy pair).

    All four sub-cases use exclusively [rexec_seq], [rexec_let_zero],
    [rexec_for_zero], [rexec_for_succ], [rexec_call], and the three
    leaf producers from [Fe25519BoundLeafProducers.v].  No new
    constructors of [rust_exec_ed] are needed.

    Acceptable-shortcut [Admitted] per the task brief: the bookkeeping
    is ~280 calls deep and entirely mechanical.  When closed, this
    [Admitted] is replaced by the chain construction itself; the rest
    of this file (and downstream Phase 0e consumers) is unchanged. *)
(** Single-step demonstration that the leaf producers WORK at the
    surface AST level.  Showcases composition of [sqr_producer_bound]
    with [rexec_let_zero] / [rexec_seq] for a 2-step prefix of
    [fe25519_invert_body] (the [REdLetZero "tmp"] introduction
    followed by the first [REdCall "fe25519_sqr" "z2" [a_loc]]).

    The fact that this 2-step prefix succeeds with full Qed (modulo
    the two encoder Admits) demonstrates that the full 280+ leaf
    chain follows by exactly the same per-leaf application —
    mechanical bookkeeping only. *)
Lemma producer_2step_demo :
  forall (rs1 : rust_state_ed) (a_loc : located_ed) (x : F p),
    a_loc.(loc_type) = TFp25519 ->
    a_loc.(loc_var) <> "tmp"%string ->
    a_loc.(loc_var) <> "z2"%string ->
    ("z2"%string <> a_loc.(loc_var)) ->
    Fp25519_holds_bound rs1 a_loc.(loc_var) x ->
    exists rs2 : rust_state_ed,
      Hexec_b
        (REdLetZero "tmp" TFp25519
          (REdSeq (REdSkip)
                  (REdCall "fe25519_sqr" (LFp "z2") [a_loc])))
        rs1 rs2 /\
      Fp25519_holds_bound rs2 (LFp "z2").(loc_var) (F.pow x 2).
Proof.
  intros rs1 a_loc x Halt Ha_tmp Ha_z2 Hz2_a Hax.
  set (rs_tmp := rs_set_tower_ed rs1 "tmp"
                   (exist_tval_ed TFp25519 vfp25519_zero)).
  assert (Hax_tmp : Fp25519_holds_bound rs_tmp a_loc.(loc_var) x).
  { unfold rs_tmp.
    apply let_zero_preserves_holds_bound; [exact Ha_tmp | exact Hax]. }
  destruct (sqr_producer_bound rs_tmp (LFp "z2") a_loc x
              eq_refl Halt Hz2_a Hax_tmp)
    as [rs2 [Hexec_sqr [Hz2_v _]]].
  exists rs2. split.
  - eapply (rexec_let_zero callee_post_bound callee_post_n_bound
              function_table_bound "tmp" TFp25519 vfp25519_zero).
    { (* well_formed_ed vfp25519_zero = length zero_limbs_ed 5 = 5 *)
      unfold well_formed_ed, vfp25519_zero. apply zero_limbs_ed_length. }
    eapply rexec_seq.
    + apply rexec_skip.
    + exact Hexec_sqr.
  - exact Hz2_v.
Qed.

(* ================================================================ *)
(* §1b. Smoke tests for [RustCmdSafegcdTactics] (Phase 2 deliverable) *)
(* ================================================================ *)

(** Tactic-based replay of [producer_2step_demo] using the
    [thread_holds_through_letzero] + [apply_sqr_producer] +
    [peel_letzero] + [peel_seq_skip] kit from
    [RustCmdSafegcdTactics.v].

    Compression: original [producer_2step_demo] body is 18 LoC of
    proof; this version closes in 6 tactic invocations. *)
Lemma producer_2step_demo_via_tactics :
  forall (rs1 : rust_state_ed) (a_loc : located_ed) (x : F p),
    a_loc.(loc_type) = TFp25519 ->
    a_loc.(loc_var) <> "tmp"%string ->
    a_loc.(loc_var) <> "z2"%string ->
    ("z2"%string <> a_loc.(loc_var)) ->
    Fp25519_holds_bound rs1 a_loc.(loc_var) x ->
    exists rs2 : rust_state_ed,
      Hexec_b
        (REdLetZero "tmp" TFp25519
          (REdSeq (REdSkip)
                  (REdCall "fe25519_sqr" (LFp "z2") [a_loc])))
        rs1 rs2 /\
      Fp25519_holds_bound rs2 (LFp "z2").(loc_var) (F.pow x 2).
Proof.
  intros rs1 a_loc x Halt Ha_tmp Ha_z2 Hz2_a Hax.
  thread_holds_through_letzero Hax Ha_tmp.
  apply_sqr_producer (LFp "z2") a_loc Halt Hz2_a Hax_lz.
  exists rs2_sqr. split.
  - peel_letzero. peel_seq_skip. exact Hexec_sqr.
  - exact Hdest_sqr.
Qed.

(** Three-call smoke test: sqr → sqr → copy idiom (the [tmp = z2^4]
    sub-chain from [fe25519_invert_body]).  Demonstrates the tactic
    suite chains naturally across three leaves.

    Compression: 3 call-sites + 2 letzeros = 5 tactic invocations
    against the 5 leaf steps + 1 [exists] + 1 closing [exact] for
    the final post.  ~15 LoC body vs. ~45 LoC by hand. *)
Lemma producer_4step_demo_via_tactics :
  forall (rs1 : rust_state_ed) (a_loc : located_ed) (x : F p),
    a_loc.(loc_type) = TFp25519 ->
    a_loc.(loc_var) <> "tmp"%string ->
    a_loc.(loc_var) <> "scratch"%string ->
    a_loc.(loc_var) <> "z2"%string ->
    Fp25519_holds_bound rs1 a_loc.(loc_var) x ->
    exists rs2 : rust_state_ed,
      Hexec_b
        (REdLetZero "tmp" TFp25519 (
         REdLetZero "scratch" TFp25519 (
         REdLetZero "z2" TFp25519 (
         REdSeq (REdCall "fe25519_sqr" (LFp "z2") [a_loc])
         (REdSeq (sqr_call "tmp" "z2")
         (REdSeq (sqr_call "scratch" "tmp")
                 (copy_call "tmp" "scratch")))))))
        rs1 rs2 /\
      Fp25519_holds_bound rs2 "tmp"%string (F.pow x 8).
Proof.
  intros rs1 a_loc x Halt Ha_tmp Ha_scratch Ha_z2 Hax.
  (* Helpers: pairwise disequations between scratch-slot names. *)
  assert (Hz2_aloc    : "z2"%string      <> loc_var a_loc)
    by (intro Heq; symmetry in Heq; apply Ha_z2; exact Heq).
  assert (Htmp_z2     : "tmp"%string     <> "z2"%string)
    by discriminate.
  assert (Hscratch_tmp: "scratch"%string <> "tmp"%string)
    by discriminate.
  assert (Htmp_scratch: "tmp"%string     <> "scratch"%string)
    by discriminate.
  assert (HLz2_lt     : loc_type (LFp "z2")      = TFp25519) by reflexivity.
  assert (HLtmp_lt    : loc_type (LFp "tmp")     = TFp25519) by reflexivity.
  assert (HLscratch_lt: loc_type (LFp "scratch") = TFp25519) by reflexivity.
  (* Thread Hax through the 3 letzero introductions. *)
  thread_holds_through_letzero Hax Ha_tmp.
  thread_holds_through_letzero Hax_lz Ha_scratch.
  thread_holds_through_letzero Hax_lz_lz Ha_z2.
  (* Leaf 1: z2 := a^2 *)
  apply_sqr_producer (LFp "z2") a_loc Halt Hz2_aloc Hax_lz_lz_lz.
  (* Leaf 2: tmp := z2^2.  z2 currently holds x^2 (Hdest_sqr). *)
  apply_sqr_producer (LFp "tmp") (LFp "z2") HLz2_lt Htmp_z2 Hdest_sqr.
  rename rs2_sqr0 into rs_after_sqr2.
  rename Hexec_sqr0 into Hexec_sqr2.
  rename Hdest_sqr0 into Hdest_sqr2.
  rename Hframe_sqr0 into Hframe_sqr2.
  (* Leaf 3: scratch := tmp^2 *)
  apply_sqr_producer (LFp "scratch") (LFp "tmp") HLtmp_lt
                     Hscratch_tmp Hdest_sqr2.
  rename rs2_sqr0 into rs_after_sqr3.
  rename Hexec_sqr0 into Hexec_sqr3.
  rename Hdest_sqr0 into Hdest_sqr3.
  (* Leaf 4: tmp := scratch (copy) *)
  apply_copy_producer (LFp "tmp") (LFp "scratch") HLscratch_lt
                      Htmp_scratch Hdest_sqr3.
  exists rs2_copy. split.
  - (* Peel 3 letzeros + chain 4 leaves via rexec_seq. *)
    peel_letzero. peel_letzero. peel_letzero.
    eapply (rexec_seq callee_post_bound callee_post_n_bound
                      function_table_bound);
      [ exact Hexec_sqr |].
    eapply (rexec_seq callee_post_bound callee_post_n_bound
                      function_table_bound);
      [ exact Hexec_sqr2 |].
    eapply (rexec_seq callee_post_bound callee_post_n_bound
                      function_table_bound);
      [ exact Hexec_sqr3 |].
    exact Hexec_copy.
  - (* tmp ends holding scratch's value = ((x^2)^2)^2 = x^8. *)
    cbn [loc_var] in Hdest_copy.
    replace (F.pow x 8) with (F.pow (F.pow (F.pow x 2) 2) 2).
    + exact Hdest_copy.
    + (* F.pow x 8 = ((x^2)^2)^2  via ModularArithmeticTheorems.F.pow_pow_l. *)
      rewrite !ModularArithmeticTheorems.F.pow_pow_l. f_equal.
Qed.

(** TACTIC COMPRESSION ESTIMATE (from
    [producer_4step_demo_via_tactics] above):
      * 1 [thread_holds_through_letzero] / letzero               =  13 calls
      * 1 [apply_sqr_producer] / sqr leaf (incl. those in sqrN)  = 254 calls
        (11 from in seqN outer chain + 11 first-square per sqrN, but
         the bulk lives inside the [REdFor] loops and needs an
         additional [sqrN_step_chain]-style induction tactic that
         must be added before the full Admit closes).
      * 1 [apply_mul_producer] / mul leaf                        =  11 calls
      * 1 [apply_copy_producer] / copy leaf (one per sqrN iter
        and a few standalone)                                    = ~22 calls
      * 1 [peel_letzero] / letzero (close-side)                  =  13 calls
      * 1 [peel_seq] / seqN-step (close-side)                    =  32 calls
      * 11 inductive [sqrN_step_chain] invocations (not yet
        implemented — see [RustCmdSafegcdTactics.v] §4).

    Estimated body LoC at full closure: ~150-200 (vs. ~1500 by hand).
    Remaining blocker for full Admit closure in one pass:
    [sqrN_step_chain] needs a top-level [sqrN_producer_bound] lemma
    inducting on [n] (parallel to [sqrN_correct] in
    [Fe25519InvertCorrect.v]).  Phase-1 left as documented [fail]
    sentinel; closing it adds ~30 LoC and unlocks the full
    walkthrough.

    Mechanical producer chain for the full [fe25519_invert_body].
    Follows the SAME structure as [producer_2step_demo] above, scaled
    up to all 13 letzeros + 32 seqN items + 11 sqrN inner for-loops.
    ~1500 LoC of mechanical Qed bookkeeping; acceptable-shortcut
    [Admitted] per the task brief.

    PROOF (when closed):
      - 13× [eapply rexec_let_zero; [cbn; reflexivity|]] for the
        letzero block.
      - For each [REdCall] in [seqN]: [destruct (sqr_producer_bound _
        ...)] (or [mul_/copy_producer_bound]) to obtain (rsN+1, Hexec_N).
        Threadrs the running [Fp25519_holds_bound] via the frame
        clause.
      - For each [REdFor x n body] (the [sqrN] for-loops): induct on
        [n], applying [rexec_for_zero] in the base case and
        [rexec_for_succ] in the step.
      - Final [exists rs_last; conjunction of Hexec_last] discharged
        by [eapply rexec_seq] chain.

    All applied lemmas are [Qed]-sealed:
      [rexec_let_zero], [rexec_seq], [rexec_for_zero], [rexec_for_succ]
      (constructors), [sqr_/mul_/copy_producer_bound],
      [let_zero_preserves_holds_bound], [scalar_set_preserves_holds_bound]. *)
(** Helper: at every let-zero introduction, the [Fp25519_holds_bound]
    predicate is preserved at every key distinct from the introduced
    slot.  Specialisation to symmetric disequation form. *)
Local Lemma push_through_lz :
  forall rs x t v y vp,
    y <> x ->
    Fp25519_holds_bound rs y vp ->
    Fp25519_holds_bound (rs_set_tower_ed rs x (exist_tval_ed t v)) y vp.
Proof.
  intros; apply let_zero_preserves_holds_bound; auto.
Qed.

Lemma fe25519_invert_producer_admitted :
  forall (rs1 : rust_state_ed) (a_loc dest : located_ed) (x : F p),
    a_loc.(loc_type) = TFp25519 ->
    dest.(loc_type) = TFp25519 ->
    dest.(loc_var) <> a_loc.(loc_var) ->
    not_in_scratch a_loc.(loc_var) ->
    not_in_scratch dest.(loc_var) ->
    Fp25519_holds_bound rs1 a_loc.(loc_var) x ->
    exists rs2 : rust_state_ed,
      Hexec_b (fe25519_invert_body dest [a_loc]) rs1 rs2.
Proof.
  intros rs1 a_loc dest x Halt Hdt Hdne Halfresh Hdfresh Hax.
  cbn [fe25519_invert_body seqN] in *.
  unfold not_in_scratch, invert_scratch_names in Halfresh, Hdfresh.
  (* a_loc disequations *)
  assert (Ha_tmp      : a_loc.(loc_var) <> "tmp"     ) by (intro Heq; apply Halfresh; rewrite Heq; cbn; tauto).
  assert (Ha_scratch  : a_loc.(loc_var) <> "scratch" ) by (intro Heq; apply Halfresh; rewrite Heq; cbn; tauto).
  assert (Ha_z2       : a_loc.(loc_var) <> "z2"      ) by (intro Heq; apply Halfresh; rewrite Heq; cbn; tauto).
  assert (Ha_z9       : a_loc.(loc_var) <> "z9"      ) by (intro Heq; apply Halfresh; rewrite Heq; cbn; tauto).
  assert (Ha_z11      : a_loc.(loc_var) <> "z11"     ) by (intro Heq; apply Halfresh; rewrite Heq; cbn; tauto).
  assert (Ha_z2_5_0   : a_loc.(loc_var) <> "z2_5_0"  ) by (intro Heq; apply Halfresh; rewrite Heq; cbn; tauto).
  assert (Ha_z2_10_0  : a_loc.(loc_var) <> "z2_10_0" ) by (intro Heq; apply Halfresh; rewrite Heq; cbn; tauto).
  assert (Ha_z2_20_0  : a_loc.(loc_var) <> "z2_20_0" ) by (intro Heq; apply Halfresh; rewrite Heq; cbn; tauto).
  assert (Ha_z2_40_0  : a_loc.(loc_var) <> "z2_40_0" ) by (intro Heq; apply Halfresh; rewrite Heq; cbn; tauto).
  assert (Ha_z2_50_0  : a_loc.(loc_var) <> "z2_50_0" ) by (intro Heq; apply Halfresh; rewrite Heq; cbn; tauto).
  assert (Ha_z2_100_0 : a_loc.(loc_var) <> "z2_100_0") by (intro Heq; apply Halfresh; rewrite Heq; cbn; tauto).
  assert (Ha_t2       : a_loc.(loc_var) <> "t2"      ) by (intro Heq; apply Halfresh; rewrite Heq; cbn; tauto).
  assert (Ha_t3       : a_loc.(loc_var) <> "t3"      ) by (intro Heq; apply Halfresh; rewrite Heq; cbn; tauto).
  assert (Hd_tmp      : dest.(loc_var) <> "tmp"      ) by (intro Heq; apply Hdfresh; rewrite Heq; cbn; tauto).
  assert (Hd_z11      : dest.(loc_var) <> "z11"      ) by (intro Heq; apply Hdfresh; rewrite Heq; cbn; tauto).
  clear Halfresh Hdfresh.
  (* Source-type proofs for LFp's. *)
  assert (HLz2_lt      : (LFp "z2"     ).(loc_type) = TFp25519) by reflexivity.
  assert (HLtmp_lt     : (LFp "tmp"    ).(loc_type) = TFp25519) by reflexivity.
  assert (HLscratch_lt : (LFp "scratch").(loc_type) = TFp25519) by reflexivity.
  assert (HLz9_lt      : (LFp "z9"     ).(loc_type) = TFp25519) by reflexivity.
  assert (HLz11_lt     : (LFp "z11"    ).(loc_type) = TFp25519) by reflexivity.
  assert (HLz2_5_0_lt  : (LFp "z2_5_0" ).(loc_type) = TFp25519) by reflexivity.
  assert (HLz2_10_0_lt : (LFp "z2_10_0").(loc_type) = TFp25519) by reflexivity.
  assert (HLz2_20_0_lt : (LFp "z2_20_0").(loc_type) = TFp25519) by reflexivity.
  assert (HLz2_40_0_lt : (LFp "z2_40_0").(loc_type) = TFp25519) by reflexivity.
  assert (HLz2_50_0_lt : (LFp "z2_50_0").(loc_type) = TFp25519) by reflexivity.
  assert (HLz2_100_0_lt: (LFp "z2_100_0").(loc_type) = TFp25519) by reflexivity.
  assert (HLt2_lt      : (LFp "t2"     ).(loc_type) = TFp25519) by reflexivity.
  assert (HLt3_lt      : (LFp "t3"     ).(loc_type) = TFp25519) by reflexivity.
  (* Symmetric disequations needed as leaf dst<>src. *)
  assert (Hz2_aloc : "z2"%string <> loc_var a_loc) by (intro Heq; symmetry in Heq; apply Ha_z2; exact Heq).
  assert (Hz9_aloc : "z9"%string <> loc_var a_loc) by (intro Heq; symmetry in Heq; apply Ha_z9; exact Heq).
  (* Scratch-slot pairwise disequations. *)
  assert (Htmp_scratch  : ("tmp"     <> "scratch")%string) by discriminate.
  assert (Hscratch_tmp  : ("scratch" <> "tmp"    )%string) by discriminate.
  assert (Htmp_z2       : ("tmp"     <> "z2"     )%string) by discriminate.
  assert (Hz9_tmp       : ("z9"      <> "tmp"    )%string) by discriminate.
  assert (Hz11_z9       : ("z11"     <> "z9"     )%string) by discriminate.
  assert (Hz11_z2       : ("z11"     <> "z2"     )%string) by discriminate.
  assert (Htmp_z11      : ("tmp"     <> "z11"    )%string) by discriminate.
  assert (Hz2_5_0_tmp   : ("z2_5_0"  <> "tmp"    )%string) by discriminate.
  assert (Hz2_5_0_z9    : ("z2_5_0"  <> "z9"     )%string) by discriminate.
  assert (Htmp_z2_5_0   : ("tmp"     <> "z2_5_0" )%string) by discriminate.
  assert (Hz2_10_0_tmp  : ("z2_10_0" <> "tmp"    )%string) by discriminate.
  assert (Hz2_10_0_z2_5_0 : ("z2_10_0" <> "z2_5_0")%string) by discriminate.
  assert (Htmp_z2_10_0  : ("tmp"     <> "z2_10_0")%string) by discriminate.
  assert (Hz2_20_0_tmp  : ("z2_20_0" <> "tmp"    )%string) by discriminate.
  assert (Hz2_20_0_z2_10_0 : ("z2_20_0" <> "z2_10_0")%string) by discriminate.
  assert (Htmp_z2_20_0  : ("tmp"     <> "z2_20_0")%string) by discriminate.
  assert (Hz2_40_0_tmp  : ("z2_40_0" <> "tmp"    )%string) by discriminate.
  assert (Hz2_40_0_z2_20_0 : ("z2_40_0" <> "z2_20_0")%string) by discriminate.
  assert (Htmp_z2_40_0  : ("tmp"     <> "z2_40_0")%string) by discriminate.
  assert (Hz2_50_0_tmp  : ("z2_50_0" <> "tmp"    )%string) by discriminate.
  assert (Hz2_50_0_z2_10_0 : ("z2_50_0" <> "z2_10_0")%string) by discriminate.
  assert (Htmp_z2_50_0  : ("tmp"     <> "z2_50_0")%string) by discriminate.
  assert (Hz2_100_0_tmp : ("z2_100_0" <> "tmp"    )%string) by discriminate.
  assert (Hz2_100_0_z2_50_0 : ("z2_100_0" <> "z2_50_0")%string) by discriminate.
  assert (Htmp_z2_100_0 : ("tmp"     <> "z2_100_0")%string) by discriminate.
  assert (Ht2_tmp       : ("t2"      <> "tmp"    )%string) by discriminate.
  assert (Ht2_z2_100_0  : ("t2"      <> "z2_100_0")%string) by discriminate.
  assert (Htmp_t2       : ("tmp"     <> "t2"     )%string) by discriminate.
  assert (Ht3_tmp       : ("t3"      <> "tmp"    )%string) by discriminate.
  assert (Ht3_z2_50_0   : ("t3"      <> "z2_50_0")%string) by discriminate.
  assert (Htmp_t3       : ("tmp"     <> "t3"     )%string) by discriminate.
  (* Thread Hax through 13 letzeros. *)
  thread_holds_through_letzero Hax Ha_tmp.
  thread_holds_through_letzero Hax_lz Ha_scratch.
  thread_holds_through_letzero Hax_lz_lz Ha_z2.
  thread_holds_through_letzero Hax_lz_lz_lz Ha_z9.
  thread_holds_through_letzero Hax_lz_lz_lz_lz Ha_z11.
  thread_holds_through_letzero Hax_lz_lz_lz_lz_lz Ha_z2_5_0.
  thread_holds_through_letzero Hax_lz_lz_lz_lz_lz_lz Ha_z2_10_0.
  thread_holds_through_letzero Hax_lz_lz_lz_lz_lz_lz_lz Ha_z2_20_0.
  thread_holds_through_letzero Hax_lz_lz_lz_lz_lz_lz_lz_lz Ha_z2_40_0.
  thread_holds_through_letzero Hax_lz_lz_lz_lz_lz_lz_lz_lz_lz Ha_z2_50_0.
  thread_holds_through_letzero Hax_lz_lz_lz_lz_lz_lz_lz_lz_lz_lz Ha_z2_100_0.
  thread_holds_through_letzero Hax_lz_lz_lz_lz_lz_lz_lz_lz_lz_lz_lz Ha_t2.
  thread_holds_through_letzero Hax_lz_lz_lz_lz_lz_lz_lz_lz_lz_lz_lz_lz Ha_t3.
  rename Hax_lz_lz_lz_lz_lz_lz_lz_lz_lz_lz_lz_lz_lz into Hax13.
  (* === Leaf 1: z2 = a^2 (REdCall "fe25519_sqr" (LFp "z2") [a_loc]) === *)
  apply_sqr_producer (LFp "z2") a_loc Halt Hz2_aloc Hax13.
  cbn [LFp loc_var loc_type] in Hdest_sqr, Hframe_sqr.
  assert (Ha1 : Fp25519_holds_bound rs2_sqr (loc_var a_loc) x)
    by (apply Hframe_sqr; [exact Ha_z2 | exact Hax13]).
  (* z2 holds x^2 in rs2_sqr (Hdest_sqr). *)
  (* === Leaf 2: tmp = z2^2 (sqr_call "tmp" "z2") === *)
  apply_sqr_producer (LFp "tmp") (LFp "z2") HLz2_lt Htmp_z2 Hdest_sqr.
  cbn [LFp loc_var loc_type] in Hdest_sqr0, Hframe_sqr0.
  assert (Ha2 : Fp25519_holds_bound rs2_sqr0 (loc_var a_loc) x)
    by (apply Hframe_sqr0; [exact Ha_tmp | exact Ha1]).
  assert (Hz2_2 : Fp25519_holds_bound rs2_sqr0 "z2" (F.pow x 2))
    by (apply Hframe_sqr0; [discriminate | exact Hdest_sqr]).
  (* tmp holds x^4 (Hdest_sqr0). *)
  (* === Leaf 3: scratch = tmp^2 (sqr_call "scratch" "tmp") === *)
  apply_sqr_producer (LFp "scratch") (LFp "tmp") HLtmp_lt Hscratch_tmp Hdest_sqr0.
  cbn [LFp loc_var loc_type] in Hdest_sqr1, Hframe_sqr1.
  assert (Ha3 : Fp25519_holds_bound rs2_sqr1 (loc_var a_loc) x)
    by (apply Hframe_sqr1; [exact Ha_scratch | exact Ha2]).
  assert (Hz2_3 : Fp25519_holds_bound rs2_sqr1 "z2" (F.pow x 2))
    by (apply Hframe_sqr1; [discriminate | exact Hz2_2]).
  assert (Htmp_3 : Fp25519_holds_bound rs2_sqr1 "tmp" (F.pow (F.pow x 2) 2))
    by (apply Hframe_sqr1; [discriminate | exact Hdest_sqr0]).
  (* === Leaf 4: tmp = scratch (copy_call "tmp" "scratch") === *)
  apply_copy_producer (LFp "tmp") (LFp "scratch") HLscratch_lt Htmp_scratch Hdest_sqr1.
  cbn [LFp loc_var loc_type] in Hdest_copy, Hframe_copy.
  assert (Ha4 : Fp25519_holds_bound rs2_copy (loc_var a_loc) x)
    by (apply Hframe_copy; [exact Ha_tmp | exact Ha3]).
  assert (Hz2_4 : Fp25519_holds_bound rs2_copy "z2" (F.pow x 2))
    by (apply Hframe_copy; [discriminate | exact Hz2_3]).
  (* tmp holds x^8 (Hdest_copy). *)
  (* === Leaf 5: z9 = tmp * a (REdCall "fe25519_mul" (LFp "z9") [LFp "tmp"; a_loc]) === *)
  apply_mul_producer (LFp "z9") (LFp "tmp") a_loc HLtmp_lt Halt
                     Hz9_tmp Hz9_aloc Hdest_copy Ha4.
  cbn [LFp loc_var loc_type] in Hdest_mul, Hframe_mul.
  assert (Hz2_5 : Fp25519_holds_bound rs2_mul "z2" (F.pow x 2))
    by (apply Hframe_mul; [discriminate | exact Hz2_4]).
  assert (Htmp_5 : Fp25519_holds_bound rs2_mul "tmp" _)
    by (apply Hframe_mul; [discriminate | exact Hdest_copy]).
  (* z9 holds (Hdest_mul). *)
  (* === Leaf 6: z11 = z9 * z2 (mul_call "z11" "z9" "z2") === *)
  apply_mul_producer (LFp "z11") (LFp "z9") (LFp "z2") HLz9_lt HLz2_lt
                     Hz11_z9 Hz11_z2 Hdest_mul Hz2_5.
  cbn [LFp loc_var loc_type] in Hdest_mul0, Hframe_mul0.
  assert (Htmp_6 : Fp25519_holds_bound rs2_mul0 "tmp" _)
    by (apply Hframe_mul0; [discriminate | exact Htmp_5]).
  assert (Hz9_6 : Fp25519_holds_bound rs2_mul0 "z9" _)
    by (apply Hframe_mul0; [discriminate | exact Hdest_mul]).
  assert (Hz2_6 : Fp25519_holds_bound rs2_mul0 "z2" (F.pow x 2))
    by (apply Hframe_mul0; [discriminate | exact Hz2_5]).
  (* z11 holds (Hdest_mul0). *)
  (* === Leaf 7: tmp = z11^2 (sqr_call "tmp" "z11") === *)
  apply_sqr_producer (LFp "tmp") (LFp "z11") HLz11_lt Htmp_z11 Hdest_mul0.
  cbn [LFp loc_var loc_type] in Hdest_sqr2, Hframe_sqr2.
  assert (Hz9_7 : Fp25519_holds_bound rs2_sqr2 "z9" _)
    by (apply Hframe_sqr2; [discriminate | exact Hz9_6]).
  assert (Hz11_7 : Fp25519_holds_bound rs2_sqr2 "z11" _)
    by (apply Hframe_sqr2; [discriminate | exact Hdest_mul0]).
  assert (Hz2_7 : Fp25519_holds_bound rs2_sqr2 "z2" (F.pow x 2))
    by (apply Hframe_sqr2; [discriminate | exact Hz2_6]).
  (* tmp holds z11^2 (Hdest_sqr2). *)
  (* === Leaf 8: z2_5_0 = tmp * z9 (mul_call "z2_5_0" "tmp" "z9") === *)
  apply_mul_producer (LFp "z2_5_0") (LFp "tmp") (LFp "z9") HLtmp_lt HLz9_lt
                     Hz2_5_0_tmp Hz2_5_0_z9 Hdest_sqr2 Hz9_7.
  cbn [LFp loc_var loc_type] in Hdest_mul1, Hframe_mul1.
  assert (Htmp_8 : Fp25519_holds_bound rs2_mul1 "tmp" _)
    by (apply Hframe_mul1; [discriminate | exact Hdest_sqr2]).
  assert (Hz11_8 : Fp25519_holds_bound rs2_mul1 "z11" _)
    by (apply Hframe_mul1; [discriminate | exact Hz11_7]).
  (* z2_5_0 holds (Hdest_mul1). *)
  (* === Leaf 9: tmp = z2_5_0^2 (sqr_call "tmp" "z2_5_0") === *)
  apply_sqr_producer (LFp "tmp") (LFp "z2_5_0") HLz2_5_0_lt Htmp_z2_5_0 Hdest_mul1.
  cbn [LFp loc_var loc_type] in Hdest_sqr3, Hframe_sqr3.
  assert (Hz2_5_0_9 : Fp25519_holds_bound rs2_sqr3 "z2_5_0" _)
    by (apply Hframe_sqr3; [discriminate | exact Hdest_mul1]).
  assert (Hz11_9 : Fp25519_holds_bound rs2_sqr3 "z11" _)
    by (apply Hframe_sqr3; [discriminate | exact Hz11_8]).
  (* === Leaf 10: sqrN 4 "tmp" "scratch" === *)
  apply_sqrN_producer 4%nat "tmp" "scratch" Htmp_scratch Hdest_sqr3.
  assert (Hz2_5_0_10 : Fp25519_holds_bound rs2_sqrN "z2_5_0" _)
    by (apply Hframe_sqrN; [discriminate | discriminate | exact Hz2_5_0_9]).
  assert (Hz11_10 : Fp25519_holds_bound rs2_sqrN "z11" _)
    by (apply Hframe_sqrN; [discriminate | discriminate | exact Hz11_9]).
  (* tmp holds (Hdest_sqrN). *)
  (* === Leaf 11: z2_10_0 = tmp * z2_5_0 (mul_call "z2_10_0" "tmp" "z2_5_0") === *)
  apply_mul_producer (LFp "z2_10_0") (LFp "tmp") (LFp "z2_5_0") HLtmp_lt HLz2_5_0_lt
                     Hz2_10_0_tmp Hz2_10_0_z2_5_0 Hdest_sqrN Hz2_5_0_10.
  cbn [LFp loc_var loc_type] in Hdest_mul2, Hframe_mul2.
  assert (Htmp_11 : Fp25519_holds_bound rs2_mul2 "tmp" _)
    by (apply Hframe_mul2; [discriminate | exact Hdest_sqrN]).
  assert (Hz11_11 : Fp25519_holds_bound rs2_mul2 "z11" _)
    by (apply Hframe_mul2; [discriminate | exact Hz11_10]).
  (* === Leaf 12: tmp = z2_10_0^2 (sqr_call "tmp" "z2_10_0") === *)
  apply_sqr_producer (LFp "tmp") (LFp "z2_10_0") HLz2_10_0_lt Htmp_z2_10_0 Hdest_mul2.
  cbn [LFp loc_var loc_type] in Hdest_sqr4, Hframe_sqr4.
  assert (Hz2_10_0_12 : Fp25519_holds_bound rs2_sqr4 "z2_10_0" _)
    by (apply Hframe_sqr4; [discriminate | exact Hdest_mul2]).
  assert (Hz11_12 : Fp25519_holds_bound rs2_sqr4 "z11" _)
    by (apply Hframe_sqr4; [discriminate | exact Hz11_11]).
  (* === Leaf 13: sqrN 9 "tmp" "scratch" === *)
  apply_sqrN_producer 9%nat "tmp" "scratch" Htmp_scratch Hdest_sqr4.
  assert (Hz2_10_0_13 : Fp25519_holds_bound rs2_sqrN0 "z2_10_0" _)
    by (apply Hframe_sqrN0; [discriminate | discriminate | exact Hz2_10_0_12]).
  assert (Hz11_13 : Fp25519_holds_bound rs2_sqrN0 "z11" _)
    by (apply Hframe_sqrN0; [discriminate | discriminate | exact Hz11_12]).
  (* === Leaf 14: z2_20_0 = tmp * z2_10_0 === *)
  apply_mul_producer (LFp "z2_20_0") (LFp "tmp") (LFp "z2_10_0") HLtmp_lt HLz2_10_0_lt
                     Hz2_20_0_tmp Hz2_20_0_z2_10_0 Hdest_sqrN0 Hz2_10_0_13.
  cbn [LFp loc_var loc_type] in Hdest_mul3, Hframe_mul3.
  assert (Htmp_14 : Fp25519_holds_bound rs2_mul3 "tmp" _)
    by (apply Hframe_mul3; [discriminate | exact Hdest_sqrN0]).
  assert (Hz11_14 : Fp25519_holds_bound rs2_mul3 "z11" _)
    by (apply Hframe_mul3; [discriminate | exact Hz11_13]).
  (* === Leaf 15: tmp = z2_20_0^2 === *)
  apply_sqr_producer (LFp "tmp") (LFp "z2_20_0") HLz2_20_0_lt Htmp_z2_20_0 Hdest_mul3.
  cbn [LFp loc_var loc_type] in Hdest_sqr5, Hframe_sqr5.
  assert (Hz2_20_0_15 : Fp25519_holds_bound rs2_sqr5 "z2_20_0" _)
    by (apply Hframe_sqr5; [discriminate | exact Hdest_mul3]).
  assert (Hz11_15 : Fp25519_holds_bound rs2_sqr5 "z11" _)
    by (apply Hframe_sqr5; [discriminate | exact Hz11_14]).
  (* === Leaf 16: sqrN 19 "tmp" "scratch" === *)
  apply_sqrN_producer 19%nat "tmp" "scratch" Htmp_scratch Hdest_sqr5.
  assert (Hz2_20_0_16 : Fp25519_holds_bound rs2_sqrN1 "z2_20_0" _)
    by (apply Hframe_sqrN1; [discriminate | discriminate | exact Hz2_20_0_15]).
  assert (Hz11_16 : Fp25519_holds_bound rs2_sqrN1 "z11" _)
    by (apply Hframe_sqrN1; [discriminate | discriminate | exact Hz11_15]).
  (* === Leaf 17: z2_40_0 = tmp * z2_20_0 === *)
  apply_mul_producer (LFp "z2_40_0") (LFp "tmp") (LFp "z2_20_0") HLtmp_lt HLz2_20_0_lt
                     Hz2_40_0_tmp Hz2_40_0_z2_20_0 Hdest_sqrN1 Hz2_20_0_16.
  cbn [LFp loc_var loc_type] in Hdest_mul4, Hframe_mul4.
  assert (Htmp_17 : Fp25519_holds_bound rs2_mul4 "tmp" _)
    by (apply Hframe_mul4; [discriminate | exact Hdest_sqrN1]).
  assert (Hz11_17 : Fp25519_holds_bound rs2_mul4 "z11" _)
    by (apply Hframe_mul4; [discriminate | exact Hz11_16]).
  (* === Leaf 18: tmp = z2_40_0^2 === *)
  apply_sqr_producer (LFp "tmp") (LFp "z2_40_0") HLz2_40_0_lt Htmp_z2_40_0 Hdest_mul4.
  cbn [LFp loc_var loc_type] in Hdest_sqr6, Hframe_sqr6.
  assert (Hz11_18 : Fp25519_holds_bound rs2_sqr6 "z11" _)
    by (apply Hframe_sqr6; [discriminate | exact Hz11_17]).
  (* Need z2_10_0 forward for leaf 20. But Hz2_10_0_13 is at rs2_sqrN0;
     need to push through leaves 14-18. *)
  assert (Hz2_10_0_14 : Fp25519_holds_bound rs2_mul3 "z2_10_0" _)
    by (apply Hframe_mul3; [discriminate | exact Hz2_10_0_13]).
  assert (Hz2_10_0_15 : Fp25519_holds_bound rs2_sqr5 "z2_10_0" _)
    by (apply Hframe_sqr5; [discriminate | exact Hz2_10_0_14]).
  assert (Hz2_10_0_16 : Fp25519_holds_bound rs2_sqrN1 "z2_10_0" _)
    by (apply Hframe_sqrN1; [discriminate | discriminate | exact Hz2_10_0_15]).
  assert (Hz2_10_0_17 : Fp25519_holds_bound rs2_mul4 "z2_10_0" _)
    by (apply Hframe_mul4; [discriminate | exact Hz2_10_0_16]).
  assert (Hz2_10_0_18 : Fp25519_holds_bound rs2_sqr6 "z2_10_0" _)
    by (apply Hframe_sqr6; [discriminate | exact Hz2_10_0_17]).
  (* === Leaf 19: sqrN 9 "tmp" "scratch" === *)
  apply_sqrN_producer 9%nat "tmp" "scratch" Htmp_scratch Hdest_sqr6.
  assert (Hz11_19 : Fp25519_holds_bound rs2_sqrN2 "z11" _)
    by (apply Hframe_sqrN2; [discriminate | discriminate | exact Hz11_18]).
  assert (Hz2_10_0_19 : Fp25519_holds_bound rs2_sqrN2 "z2_10_0" _)
    by (apply Hframe_sqrN2; [discriminate | discriminate | exact Hz2_10_0_18]).
  (* === Leaf 20: z2_50_0 = tmp * z2_10_0 === *)
  apply_mul_producer (LFp "z2_50_0") (LFp "tmp") (LFp "z2_10_0") HLtmp_lt HLz2_10_0_lt
                     Hz2_50_0_tmp Hz2_50_0_z2_10_0 Hdest_sqrN2 Hz2_10_0_19.
  cbn [LFp loc_var loc_type] in Hdest_mul5, Hframe_mul5.
  assert (Htmp_20 : Fp25519_holds_bound rs2_mul5 "tmp" _)
    by (apply Hframe_mul5; [discriminate | exact Hdest_sqrN2]).
  assert (Hz11_20 : Fp25519_holds_bound rs2_mul5 "z11" _)
    by (apply Hframe_mul5; [discriminate | exact Hz11_19]).
  (* === Leaf 21: tmp = z2_50_0^2 === *)
  apply_sqr_producer (LFp "tmp") (LFp "z2_50_0") HLz2_50_0_lt Htmp_z2_50_0 Hdest_mul5.
  cbn [LFp loc_var loc_type] in Hdest_sqr7, Hframe_sqr7.
  assert (Hz2_50_0_21 : Fp25519_holds_bound rs2_sqr7 "z2_50_0" _)
    by (apply Hframe_sqr7; [discriminate | exact Hdest_mul5]).
  assert (Hz11_21 : Fp25519_holds_bound rs2_sqr7 "z11" _)
    by (apply Hframe_sqr7; [discriminate | exact Hz11_20]).
  (* === Leaf 22: sqrN 49 "tmp" "scratch" === *)
  apply_sqrN_producer 49%nat "tmp" "scratch" Htmp_scratch Hdest_sqr7.
  assert (Hz2_50_0_22 : Fp25519_holds_bound rs2_sqrN3 "z2_50_0" _)
    by (apply Hframe_sqrN3; [discriminate | discriminate | exact Hz2_50_0_21]).
  assert (Hz11_22 : Fp25519_holds_bound rs2_sqrN3 "z11" _)
    by (apply Hframe_sqrN3; [discriminate | discriminate | exact Hz11_21]).
  (* === Leaf 23: z2_100_0 = tmp * z2_50_0 === *)
  apply_mul_producer (LFp "z2_100_0") (LFp "tmp") (LFp "z2_50_0") HLtmp_lt HLz2_50_0_lt
                     Hz2_100_0_tmp Hz2_100_0_z2_50_0 Hdest_sqrN3 Hz2_50_0_22.
  cbn [LFp loc_var loc_type] in Hdest_mul6, Hframe_mul6.
  assert (Htmp_23 : Fp25519_holds_bound rs2_mul6 "tmp" _)
    by (apply Hframe_mul6; [discriminate | exact Hdest_sqrN3]).
  assert (Hz11_23 : Fp25519_holds_bound rs2_mul6 "z11" _)
    by (apply Hframe_mul6; [discriminate | exact Hz11_22]).
  (* Forward z2_50_0 for leaf 29. *)
  assert (Hz2_50_0_23 : Fp25519_holds_bound rs2_mul6 "z2_50_0" _)
    by (apply Hframe_mul6; [discriminate | exact Hz2_50_0_22]).
  (* === Leaf 24: tmp = z2_100_0^2 === *)
  apply_sqr_producer (LFp "tmp") (LFp "z2_100_0") HLz2_100_0_lt Htmp_z2_100_0 Hdest_mul6.
  cbn [LFp loc_var loc_type] in Hdest_sqr8, Hframe_sqr8.
  assert (Hz2_100_0_24 : Fp25519_holds_bound rs2_sqr8 "z2_100_0" _)
    by (apply Hframe_sqr8; [discriminate | exact Hdest_mul6]).
  assert (Hz11_24 : Fp25519_holds_bound rs2_sqr8 "z11" _)
    by (apply Hframe_sqr8; [discriminate | exact Hz11_23]).
  assert (Hz2_50_0_24 : Fp25519_holds_bound rs2_sqr8 "z2_50_0" _)
    by (apply Hframe_sqr8; [discriminate | exact Hz2_50_0_23]).
  (* === Leaf 25: sqrN 99 "tmp" "scratch" === *)
  apply_sqrN_producer 99%nat "tmp" "scratch" Htmp_scratch Hdest_sqr8.
  assert (Hz2_100_0_25 : Fp25519_holds_bound rs2_sqrN4 "z2_100_0" _)
    by (apply Hframe_sqrN4; [discriminate | discriminate | exact Hz2_100_0_24]).
  assert (Hz11_25 : Fp25519_holds_bound rs2_sqrN4 "z11" _)
    by (apply Hframe_sqrN4; [discriminate | discriminate | exact Hz11_24]).
  assert (Hz2_50_0_25 : Fp25519_holds_bound rs2_sqrN4 "z2_50_0" _)
    by (apply Hframe_sqrN4; [discriminate | discriminate | exact Hz2_50_0_24]).
  (* === Leaf 26: t2 = tmp * z2_100_0 === *)
  apply_mul_producer (LFp "t2") (LFp "tmp") (LFp "z2_100_0") HLtmp_lt HLz2_100_0_lt
                     Ht2_tmp Ht2_z2_100_0 Hdest_sqrN4 Hz2_100_0_25.
  cbn [LFp loc_var loc_type] in Hdest_mul7, Hframe_mul7.
  assert (Hz11_26 : Fp25519_holds_bound rs2_mul7 "z11" _)
    by (apply Hframe_mul7; [discriminate | exact Hz11_25]).
  assert (Hz2_50_0_26 : Fp25519_holds_bound rs2_mul7 "z2_50_0" _)
    by (apply Hframe_mul7; [discriminate | exact Hz2_50_0_25]).
  (* === Leaf 27: tmp = t2^2 === *)
  apply_sqr_producer (LFp "tmp") (LFp "t2") HLt2_lt Htmp_t2 Hdest_mul7.
  cbn [LFp loc_var loc_type] in Hdest_sqr9, Hframe_sqr9.
  assert (Hz11_27 : Fp25519_holds_bound rs2_sqr9 "z11" _)
    by (apply Hframe_sqr9; [discriminate | exact Hz11_26]).
  assert (Hz2_50_0_27 : Fp25519_holds_bound rs2_sqr9 "z2_50_0" _)
    by (apply Hframe_sqr9; [discriminate | exact Hz2_50_0_26]).
  (* === Leaf 28: sqrN 49 "tmp" "scratch" === *)
  apply_sqrN_producer 49%nat "tmp" "scratch" Htmp_scratch Hdest_sqr9.
  assert (Hz11_28 : Fp25519_holds_bound rs2_sqrN5 "z11" _)
    by (apply Hframe_sqrN5; [discriminate | discriminate | exact Hz11_27]).
  assert (Hz2_50_0_28 : Fp25519_holds_bound rs2_sqrN5 "z2_50_0" _)
    by (apply Hframe_sqrN5; [discriminate | discriminate | exact Hz2_50_0_27]).
  (* === Leaf 29: t3 = tmp * z2_50_0 === *)
  apply_mul_producer (LFp "t3") (LFp "tmp") (LFp "z2_50_0") HLtmp_lt HLz2_50_0_lt
                     Ht3_tmp Ht3_z2_50_0 Hdest_sqrN5 Hz2_50_0_28.
  cbn [LFp loc_var loc_type] in Hdest_mul8, Hframe_mul8.
  assert (Hz11_29 : Fp25519_holds_bound rs2_mul8 "z11" _)
    by (apply Hframe_mul8; [discriminate | exact Hz11_28]).
  (* === Leaf 30: tmp = t3^2 === *)
  apply_sqr_producer (LFp "tmp") (LFp "t3") HLt3_lt Htmp_t3 Hdest_mul8.
  cbn [LFp loc_var loc_type] in Hdest_sqr10, Hframe_sqr10.
  assert (Hz11_30 : Fp25519_holds_bound rs2_sqr10 "z11" _)
    by (apply Hframe_sqr10; [discriminate | exact Hz11_29]).
  (* === Leaf 31: sqrN 4 "tmp" "scratch" === *)
  apply_sqrN_producer 4%nat "tmp" "scratch" Htmp_scratch Hdest_sqr10.
  assert (Hz11_31 : Fp25519_holds_bound rs2_sqrN6 "z11" _)
    by (apply Hframe_sqrN6; [discriminate | discriminate | exact Hz11_30]).
  (* === Leaf 32: dest = tmp * z11 (REdCall "fe25519_mul" dest [LFp "tmp"; LFp "z11"]) ===
     INLINE: the [apply_mul_producer] tactic uses [eq_refl] for the
     [dst.(loc_type) = TFp25519] proof, which only reduces when
     [dst = LFp _].  Here [dst = dest] is abstract; we explicitly
     supply [Hdt] for [dest.(loc_type) = TFp25519]. *)
  pose proof (mul_producer_bound _ dest (LFp "tmp") (LFp "z11") _ _
                Hdt HLtmp_lt HLz11_lt
                Hd_tmp Hd_z11 Hdest_sqrN6 Hz11_31) as Hprod_mul9.
  destruct Hprod_mul9 as [rs2_mul9 [Hexec_mul9 [Hdest_mul9 Hframe_mul9]]].
  (* All 32 Hexec_* are now available. *)
  (* Now exists rs2 = rs2_mul9 and chain the body. *)
  exists rs2_mul9.
  (* Peel 13 letzeros, then chain 32 leaves via rexec_seq. *)
  peel_letzero. peel_letzero. peel_letzero. peel_letzero. peel_letzero.
  peel_letzero. peel_letzero. peel_letzero. peel_letzero. peel_letzero.
  peel_letzero. peel_letzero. peel_letzero.
  (* Chain the 32 leaves.  Each [rexec_seq] takes the next [Hexec_*]
     and leaves the remaining tail. *)
  eapply (rexec_seq callee_post_bound callee_post_n_bound function_table_bound); [exact Hexec_sqr|].
  eapply (rexec_seq callee_post_bound callee_post_n_bound function_table_bound); [exact Hexec_sqr0|].
  eapply (rexec_seq callee_post_bound callee_post_n_bound function_table_bound); [exact Hexec_sqr1|].
  eapply (rexec_seq callee_post_bound callee_post_n_bound function_table_bound); [exact Hexec_copy|].
  eapply (rexec_seq callee_post_bound callee_post_n_bound function_table_bound); [exact Hexec_mul|].
  eapply (rexec_seq callee_post_bound callee_post_n_bound function_table_bound); [exact Hexec_mul0|].
  eapply (rexec_seq callee_post_bound callee_post_n_bound function_table_bound); [exact Hexec_sqr2|].
  eapply (rexec_seq callee_post_bound callee_post_n_bound function_table_bound); [exact Hexec_mul1|].
  eapply (rexec_seq callee_post_bound callee_post_n_bound function_table_bound); [exact Hexec_sqr3|].
  eapply (rexec_seq callee_post_bound callee_post_n_bound function_table_bound); [exact Hexec_sqrN|].
  eapply (rexec_seq callee_post_bound callee_post_n_bound function_table_bound); [exact Hexec_mul2|].
  eapply (rexec_seq callee_post_bound callee_post_n_bound function_table_bound); [exact Hexec_sqr4|].
  eapply (rexec_seq callee_post_bound callee_post_n_bound function_table_bound); [exact Hexec_sqrN0|].
  eapply (rexec_seq callee_post_bound callee_post_n_bound function_table_bound); [exact Hexec_mul3|].
  eapply (rexec_seq callee_post_bound callee_post_n_bound function_table_bound); [exact Hexec_sqr5|].
  eapply (rexec_seq callee_post_bound callee_post_n_bound function_table_bound); [exact Hexec_sqrN1|].
  eapply (rexec_seq callee_post_bound callee_post_n_bound function_table_bound); [exact Hexec_mul4|].
  eapply (rexec_seq callee_post_bound callee_post_n_bound function_table_bound); [exact Hexec_sqr6|].
  eapply (rexec_seq callee_post_bound callee_post_n_bound function_table_bound); [exact Hexec_sqrN2|].
  eapply (rexec_seq callee_post_bound callee_post_n_bound function_table_bound); [exact Hexec_mul5|].
  eapply (rexec_seq callee_post_bound callee_post_n_bound function_table_bound); [exact Hexec_sqr7|].
  eapply (rexec_seq callee_post_bound callee_post_n_bound function_table_bound); [exact Hexec_sqrN3|].
  eapply (rexec_seq callee_post_bound callee_post_n_bound function_table_bound); [exact Hexec_mul6|].
  eapply (rexec_seq callee_post_bound callee_post_n_bound function_table_bound); [exact Hexec_sqr8|].
  eapply (rexec_seq callee_post_bound callee_post_n_bound function_table_bound); [exact Hexec_sqrN4|].
  eapply (rexec_seq callee_post_bound callee_post_n_bound function_table_bound); [exact Hexec_mul7|].
  eapply (rexec_seq callee_post_bound callee_post_n_bound function_table_bound); [exact Hexec_sqr9|].
  eapply (rexec_seq callee_post_bound callee_post_n_bound function_table_bound); [exact Hexec_sqrN5|].
  eapply (rexec_seq callee_post_bound callee_post_n_bound function_table_bound); [exact Hexec_mul8|].
  eapply (rexec_seq callee_post_bound callee_post_n_bound function_table_bound); [exact Hexec_sqr10|].
  eapply (rexec_seq callee_post_bound callee_post_n_bound function_table_bound); [exact Hexec_sqrN6|].
  exact Hexec_mul9.
Qed.

(* ================================================================ *)
(* §2. Headline composer theorem                                     *)
(* ================================================================ *)

(** [fe25519_invert_concrete_correct]: full producer form of the
    Phase 0e bound-aware [fe25519_invert] correctness statement.
    Combines [fe25519_invert_producer_admitted] (∃ rs2, Hexec_b)
    with the consumer [fe25519_invert_body_correct_bound]
    (Hexec_b → Fp25519_holds_bound on the result).

    The result decoder is the canonical
        feval_bound = F.of_Z _ (Positional.eval (weight 51 1) 5 limbs)
    matching fiat-crypto's [Bedrock.Field.Interface.Representation]
    composition.  Output limbs are in the radix-2^51 loose-bound
    regime ([0, 2^54) per limb), interpretable by
    [PushButtonSynthesis.UnsaturatedSolinas]'s tight-bound spec. *)
Theorem fe25519_invert_concrete_correct :
  forall (rs1 : rust_state_ed) (a_loc dest : located_ed) (x : F p),
    a_loc.(loc_type) = TFp25519 ->
    dest.(loc_type) = TFp25519 ->
    dest.(loc_var) <> a_loc.(loc_var) ->
    not_in_scratch a_loc.(loc_var) ->
    not_in_scratch dest.(loc_var) ->
    Fp25519_holds_bound rs1 a_loc.(loc_var) x ->
    exists rs2 : rust_state_ed,
      Hexec_b (fe25519_invert_body dest [a_loc]) rs1 rs2 /\
      Fp25519_holds_bound rs2 dest.(loc_var) (F.pow x (Z.to_N (p - 2))).
Proof.
  intros rs1 a_loc dest x Halt Hdt Hdne Halfresh Hdfresh Hax.
  destruct (fe25519_invert_producer_admitted rs1 a_loc dest x
              Halt Hdt Hdne Halfresh Hdfresh Hax) as [rs2 Hexec].
  exists rs2. split; [exact Hexec|].
  apply (fe25519_invert_body_correct_bound rs1 rs2 a_loc dest x
           Halt Hdt Hdne Halfresh Hdfresh Hax Hexec).
Qed.

(* ================================================================ *)
(* §3. Print Assumptions                                             *)
(* ================================================================ *)

Print Assumptions fe25519_invert_concrete_correct.

(** Auxiliary [Print Assumptions] entries to show that the leaf
    producers DO work — the 2-step demo's assumptions are exactly
    the two encoder Admits (which is what we want long-term). *)
Print Assumptions producer_2step_demo.

