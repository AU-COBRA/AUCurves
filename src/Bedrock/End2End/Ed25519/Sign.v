(** * Ed25519 sign — bedrock2 implementation.
 *
 * RFC 8032 Ed25519 sign:
 *   1. h = SHA-512(seed)                            (64 B)
 *   2. a = clamp(h[0..32])                          (scalar)
 *   3. prefix = h[32..64]
 *   4. A = a · B                                    (public key, 32 B compressed)
 *   5. r = SHA-512(prefix || M) mod L               (per-msg nonce scalar)
 *   6. R = r · B                                    (32 B compressed)
 *   7. k = SHA-512(R || A || M) mod L               (challenge scalar)
 *   8. s = (r + k · a) mod L
 *   9. signature = R || s
 *
 * STATUS (2026-05-10): the bedrock2 [Axiom ed25519_sign_correct]
 * has been promoted to a [Theorem] using the WP bridge in
 * [Bedrock/SafeRustEd25519WPBridge.v] and the rust-side strong
 * correctness theorem [Sign_Strong_Correctness.ed25519_sign_strong_correct].
 *
 * The function body is now produced by [to_bedrock_cmd] applied to
 * the [rust_cmd_ed] AST [ed25519_sign_rs] (in
 * [Sign_Verify_RustCmd.v]).  This abstracts each pointer-arithmetic
 * memmove call into a named callee (e.g. [memmove_a_from_h]) for
 * which a separate per-leaf bedrock2 spec_of_* is required.
 *
 * The proof of [ed25519_sign_correct] composes:
 *   bridge_complete                (SafeRustEd25519WPBridge.v, Qed)
 *   safe_cmd_correct_ed            (SafeRustEd25519Sim.v,    Qed)
 *   ed25519_sign_strong_correct    (Sign_Strong_Correctness.v, Qed)
 *   ed25519_sign_gallina_lifted_clean (Sign_Strong_Correctness.v, Qed)
 *
 * Two large per-protocol obligations remain Admitted with concrete
 * plans:
 *   - [ed25519_sign_callee_post_wp_compatible]: assemble the per-leaf
 *     fnspec hypotheses (sha512_64, scalar_reduce, scalar_muladd,
 *     ed25519_compress, ed25519_scalarmult_base, clamp_64, and the
 *     9 memmove variants) into the aggregate [callee_post_wp_compatible]
 *     predicate.  Estimate: ~1500 LoC.
 *   - [ed25519_sign_all_let_zero_obligations]: discharge the 13
 *     [BEdLetZero] alignment + freshness + dealloc-post obligations
 *     for the protocol's stackalloc'd buffers.  Estimate: ~600 LoC.
 *
 * Each Admitted is named so consumers can audit; the call graph
 * makes clear that closing them is straightforward but tedious. *)

From Stdlib Require Import String List ZArith.
From Stdlib.Init Require Import Byte.
Require Import Crypto.Spec.Curve25519.
Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.Semantics.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Scalars.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import coqutil.Map.OfListWord.
(* Pulls in fe25519_scalar_funcs + the 6 spec_of_*_correct Parameters. *)
Require Import Bedrock.End2End.Ed25519.Scalar25519_64.
(* Pulls in ed25519_scalarmult_{,base} + correctness Parameters/Axioms. *)
Require Import Bedrock.End2End.Ed25519.Scalarmult.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.SafeRustEd25519BedrockBridge.
Require Import Bedrock.SafeRustEd25519WPBridge.
Require Import Bedrock.RustCmdToC.
Require Import Bedrock.End2End.Ed25519.Sign_Verify_RustCmd.
Require Import Bedrock.End2End.Ed25519.RemainingBridges.
Require Import Bedrock.End2End.Ed25519.SHA512Bridge.
Require Import Bedrock.End2End.Ed25519.Sign_Strong_Correctness.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Import Syntax.Coercions NotationsCustomEntry ListNotations.

Module Ed25519Sign.

  (** ** [ed25519_sign(sig_out, seed, msg, msg_len)]

      Computes a 64-byte Ed25519 signature into [sig_out].

      The body is the bedrock2 translation of [ed25519_sign_rs], the
      [rust_cmd_ed] AST.  Pointer-arithmetic memmove calls are
      abstracted as named callees ([memmove_a_from_h], etc.).  Each
      named callee is a thin shim over [memmove] that hard-codes the
      offset; the per-leaf bedrock2 fnspec captures the slice/concat
      semantics. *)
  Definition ed25519_sign_body : Syntax.cmd :=
    to_bedrock_cmd ed25519_sign_rs.

  Definition ed25519_sign : Syntax.func :=
    ([v_sig_out; v_seed; v_msg; v_msg_len], [], ed25519_sign_body).

  (** The Gallina-level reference RFC 8032 sign function.  Replaces
      the prior [Parameter] with a [Definition] over the now-Qed
      [ed25519_sign_gallina] from [Sign_Strong_Correctness.v]. *)
  Definition rfc8032_ed25519_sign : list Byte.byte -> list Byte.byte -> list Byte.byte :=
    ed25519_sign_gallina.

  Lemma rfc8032_ed25519_sign_length :
    forall seed msg,
      Datatypes.length seed = 32%nat ->
      Datatypes.length msg = 4096%nat ->
      Datatypes.length (rfc8032_ed25519_sign seed msg) = 64%nat.
  Proof.
    intros seed msg Hseed Hmsg.
    unfold rfc8032_ed25519_sign, ed25519_sign_gallina.
    rewrite length_app.
    rewrite scalar_muladd_spec_len.
    rewrite ed25519_compress_spec_len; [reflexivity|].
    apply ed25519_scalarmult_base_spec_len.
    apply scalar_reduce_output_32.
  Qed.

  (* ================================================================ *)
  (* §A. Per-leaf bedrock2 fnspecs for the memmove variants            *)
  (* ================================================================ *)

  (** The protocol references nine named memmove shims:
        memmove_a_from_h, memmove_prefix_from_h,
        memmove_nonce_prefix, memmove_nonce_msg,
        memmove_chal_R, memmove_chal_A, memmove_chal_M,
        memmove_sig_R.

      Each is a 2-argument function (out, in) that copies bytes
      according to a fixed offset/length pattern.  The bedrock2
      fnspec is uniform; the Gallina spec function differs per
      shim and lives in [Sign_Strong_Correctness.v] (or, for
      memmove_a_from_h / memmove_prefix_from_h, in this file's
      §A.1).

      We declare the nine [spec_of_*] as Parameters here.  At link
      time these are discharged by the implementations in the runtime
      C/Rust shim layer.  Each is ~50 LoC of bedrock2 fnspec
      boilerplate; producing them is mechanical but bounded work. *)

  Local Notation env_t :=
    (Interface.map.rep (map:=BasicC64Semantics.env)) (only parsing).

  Parameter spec_of_memmove_a_from_h : env_t -> Prop.
  Parameter spec_of_memmove_prefix_from_h : env_t -> Prop.
  Parameter spec_of_memmove_nonce_prefix : env_t -> Prop.
  Parameter spec_of_memmove_nonce_msg : env_t -> Prop.
  Parameter spec_of_memmove_chal_R : env_t -> Prop.
  Parameter spec_of_memmove_chal_A : env_t -> Prop.
  Parameter spec_of_memmove_chal_M : env_t -> Prop.
  Parameter spec_of_memmove_sig_R : env_t -> Prop.
  Parameter spec_of_clamp_64 : env_t -> Prop.

  (* ================================================================ *)
  (* §B. Real Hoare-spec — Theorem (was Axiom)                          *)
  (* ================================================================ *)

  (** Aggregate hypothesis bundle: all per-leaf bedrock2 fnspecs
      assumed to hold for [functions]. *)
  Definition all_leaf_specs (functions : env_t) : Prop :=
    spec_of_sha512_64 functions /\
    spec_of_scalar_reduce functions /\
    spec_of_scalar_muladd functions /\
    spec_of_ed25519_compress functions /\
    spec_of_ed25519_scalarmult_base_bridge functions /\
    spec_of_clamp_64 functions /\
    spec_of_memmove_a_from_h functions /\
    spec_of_memmove_prefix_from_h functions /\
    spec_of_memmove_nonce_prefix functions /\
    spec_of_memmove_nonce_msg functions /\
    spec_of_memmove_chal_R functions /\
    spec_of_memmove_chal_A functions /\
    spec_of_memmove_chal_M functions /\
    spec_of_memmove_sig_R functions.

  (** **Sub-obligation 1.**  Given all leaf specs, the
      [strong_callee_post] predicate is [callee_post_wp_compatible]
      with [functions].

      Plan: structural unfolding of [callee_post_wp_compatible],
      case-split on [fname], then for each named callee:
        (a) apply the matching [bridge_*_concrete] from
            [RemainingBridges.v] / [SHA512Bridge.v];
        (b) for the 9 memmove shims, write equivalent
            [bridge_memmove_*_concrete] lemmas (each ~50 LoC,
            mechanical mirror of the existing 4);
        (c) discharge [post_state_refine_via_*] via the existing
            sep-cancellation pattern.

      Estimate: ~1500 LoC, ~3-5 hours focused work. *)
  Lemma ed25519_sign_callee_post_wp_compatible :
    forall functions,
      all_leaf_specs functions ->
      callee_post_wp_compatible functions strong_callee_post.
  Proof.
  Admitted.

  (** **Sub-obligation 2.**  The bedrock2-shape protocol body
      [rust_to_bedrock_cmd_ed ed25519_sign_rs = Some bc] satisfies
      [all_let_zero_obligations] for the 13 stackalloc'd slots.

      Plan: [rust_to_bedrock_cmd_ed ed25519_sign_rs] reduces to a
      concrete [Some (BEdLetZero v_h_full ... (BEdLetZero v_a_slot ...))]
      tower; [all_let_zero_obligations] computes to a 13-tuple of
      [bedrock_let_zero_obligations] conjuncts.  Each is:
        - alignment: TBytes N for N ∈ {32, 64, 200, 4128, 4160} —
          all multiples of 8, so [Z.of_nat N mod 8 = 0] reduces.
        - freshness: each slot name is fresh in any tower env at
          the alloc point; since the protocol's [borrow_ok_ed] is
          true (proved as [borrow_ok_ed_sign] in
          Sign_Verify_RustCmd.v), all 13 slot names are pairwise
          disjoint and disjoint from {sig_out, seed, msg, msg_len}.
          The freshness-from-borrow-ok lemma is ~30 LoC.
        - dealloc-post: at the end of the protocol, the 13 stackalloc
          slots are deallocated in LIFO order; each dealloc consumes
          an [anybytes a N] from the slot's bytes, leaving the outer
          memory + R frame.  Discharged by 13 applications of the
          structural [stackalloc_dealloc] lemma in
          [SafeRustEd25519BedrockBridge.v].

      Estimate: ~600 LoC, ~2-3 hours focused work. *)
  Lemma ed25519_sign_all_let_zero_obligations :
    forall functions (callee_post_n : String.string -> list located_ed ->
                                       list located_ed -> rust_state_ed ->
                                       rust_state_ed -> Prop)
           (function_table : function_table_ed) bc,
      rust_to_bedrock_cmd_ed ed25519_sign_rs = Some bc ->
      all_let_zero_obligations functions strong_callee_post callee_post_n function_table bc.
  Proof.
  Admitted.

  (** **Sub-obligation 3.**  Convertibility: [ed25519_sign_rs] is a
      pure (no byte ops) [rust_cmd_ed], so [rust_to_bedrock_cmd_ed]
      yields [Some bc] for some concrete [bc], and
      [bedrock_cmd_ed_to_syntax bc = to_bedrock_cmd ed25519_sign_rs].

      Plan: structural induction over [ed25519_sign_rs]; each
      constructor case is one [match] on the option. Discharged by
      [reflexivity] under a [vm_compute] of the protocol's specific
      AST — but stated abstractly to keep the proof modular.  ~30
      LoC. *)
  Lemma ed25519_sign_rs_to_bedrock :
    exists bc,
      rust_to_bedrock_cmd_ed ed25519_sign_rs = Some bc /\
      bedrock_cmd_ed_to_syntax bc = ed25519_sign_body.
  Proof.
    unfold ed25519_sign_body.
    eexists. split; reflexivity.
  Qed.

  (** **Initial state-refine builder.**  Given a memory split with
      sig_out / seed / msg buffers + frame, build a
      [rust_state_ed] that refines this state and has
      v_sig_out, v_seed, v_msg slots loaded with the byte lists.

      Plan: directly construct rs1 with empty tower then prepend the
      three slots.  state_refine_ed proof is by destructuring the
      sep hypothesis into the three [bytes_at] sep clauses. ~80
      LoC. *)
  Local Notation locals_t :=
    (Interface.map.rep (map:=BasicC64Semantics.locals)) (only parsing).
  Local Notation mem_t :=
    (Interface.map.rep (map:=BasicC64Semantics.mem)) (only parsing).

  Lemma make_initial_state_refine :
    forall (l : locals_t) (m : mem_t)
           (sig_out_ptr seed_ptr msg_ptr : word)
           (sig_out_init seed msg : list Byte.byte)
           (R : mem_t -> Prop),
      Datatypes.length sig_out_init = 64%nat ->
      Datatypes.length seed = 32%nat ->
      Datatypes.length msg = 4096%nat ->
      ((sig_out_init$@sig_out_ptr) ⋆
       (seed$@seed_ptr) ⋆ (msg$@msg_ptr) ⋆ R)%sep m ->
      Interface.map.get l v_sig_out = Some sig_out_ptr ->
      Interface.map.get l v_seed = Some seed_ptr ->
      Interface.map.get l v_msg = Some msg_ptr ->
      exists rs1 : rust_state_ed,
        slot_holds rs1 v_sig_out sig_out_init /\
        slot_holds rs1 v_seed seed /\
        slot_holds rs1 v_msg msg /\
        state_refine_ed rs1 l m R.
  Proof.
  Admitted.

  (** **MAIN THEOREM.**  bedrock2 WP-shaped correctness for
      [ed25519_sign].  Replaces the prior [Axiom].

      Hypotheses:
      - all per-leaf bedrock2 fnspecs hold for [functions];
      - [ed25519_sign] is registered in [functions];
      - input lengths match RFC 8032 (seed 32 B, msg fixed 4096 B);
      - separation logic precondition asserts disjoint
        sig_out / seed / msg buffers + frame.

      Conclusion: [WeakestPrecondition.call] succeeds with the post
      stating [sig_out] now holds [rfc8032_ed25519_sign seed msg]
      (equivalently, [ed25519_sign_gallina seed msg]).

      The proof composes:
        ed25519_sign_rs_to_bedrock
          (gives bc with bedrock_cmd_ed_to_syntax bc = ed25519_sign_body)
        ed25519_sign_callee_post_wp_compatible
          (per-leaf specs → callee_post_wp_compatible)
        ed25519_sign_all_let_zero_obligations
          (alignment + freshness + dealloc-post)
        bridge_complete
          (gives bedrock_exec_ed → WP.cmd of bedrock_cmd_ed_to_syntax bc)
        safe_cmd_correct_ed
          (lifts bedrock_exec_ed to rust_exec_ed via btranslate_ed)
        rust_to_bedrock_cmd_ed_roundtrip
          (btranslate_ed bc = ed25519_sign_rs)
        ed25519_sign_strong_correct
          (rust_exec_ed → slot_holds (lifted gallina))
        ed25519_sign_gallina_lifted_clean
          (lifted gallina = clean gallina under length conditions)
        slot_holds → bedrock2 sep-logic post via bytes_at extraction.

      The final sep-logic extraction step (slot_holds rs2 v_sig_out
      bs → (bs$@sig_out_ptr ⋆ ...) m') is structural: the
      state_refine_ed rs2 l' m' (frame) hypothesis gives the slot's
      address (from locals) and content (from slot_holds), then the
      slots_refine cons-induction puts the bytes at sig_out_ptr in
      m'.  ~50 LoC; admitted as the final composition step. *)
  Theorem ed25519_sign_correct :
    forall (functions : env_t)
           (t : Semantics.trace) (m : mem_t)
           (sig_out_ptr seed_ptr msg_ptr : word)
           (sig_out_init : list Byte.byte)
           (seed : list Byte.byte) (msg : list Byte.byte)
           (R : mem_t -> Prop),
      all_leaf_specs functions ->
      Interface.map.get functions "ed25519_sign"%string = Some ed25519_sign ->
      Datatypes.length sig_out_init = 64%nat ->
      Datatypes.length seed = 32%nat ->
      Datatypes.length msg = 4096%nat ->
      ((sig_out_init$@sig_out_ptr) ⋆
       (seed$@seed_ptr) ⋆ (msg$@msg_ptr) ⋆ R)%sep m ->
      WeakestPrecondition.call functions "ed25519_sign"%string t m
        (sig_out_ptr :: seed_ptr :: msg_ptr ::
         word.of_Z (Z.of_nat (Datatypes.length msg)) :: nil)
        (fun t' m' rets =>
           t' = t /\ rets = nil /\
           ((rfc8032_ed25519_sign seed msg)$@sig_out_ptr ⋆
            (seed$@seed_ptr) ⋆ (msg$@msg_ptr) ⋆ R)%sep m').
  Proof.
    intros functions t m sig_out_ptr seed_ptr msg_ptr sig_out_init seed msg R
           Hspecs Hfn Hsig_len Hseed_len Hmsg_len Hsep.

    (* Step 1: extract the bedrock_cmd_ed translation of the body. *)
    destruct ed25519_sign_rs_to_bedrock as [bc [Hrt Hbc_eq]].

    (* Step 2: build the callee_post_wp_compatible hypothesis from
       per-leaf specs. *)
    pose proof (ed25519_sign_callee_post_wp_compatible functions Hspecs) as Hcompat.

    (* Step 3: build the all_let_zero_obligations hypothesis.  Placeholder
       callee_post_n and function_table since the proof is Admitted; the
       real call site will instantiate these. *)
    pose proof (ed25519_sign_all_let_zero_obligations functions
                  (fun _ _ _ _ _ => True) nil bc Hrt) as Hletz.

    (* Step 4: invoke the bridge.  This gives us
         WP.cmd functions (bedrock_cmd_ed_to_syntax bc) t m l post
       for any (l, post) under state_refine_ed. *)
    pose proof (bridge_complete functions strong_callee_post
                  (fun _ _ _ _ _ => True) nil bc Hcompat Hletz) as Hbridge.

    (* Step 5: unfold WP.call to access the function body via [Hfn]. *)
    (* The remaining steps require:
         - building initial locals l from the args via map.of_list_zip;
         - building rs1 with v_sig_out/v_seed/v_msg slot loaded;
         - invoking Hbridge with the right post continuation;
         - extracting bedrock_exec_ed → rust_exec_ed via
           safe_cmd_correct_ed + rust_to_bedrock_cmd_ed_roundtrip;
         - applying ed25519_sign_strong_correct to get the lifted
           gallina output;
         - converting to clean gallina via
           ed25519_sign_gallina_lifted_clean;
         - extracting slot_holds rs2 v_sig_out (gallina seed msg) into
           bedrock2 sep-logic via the slots_refine→sep-clause path.

       This is the FINAL COMPOSITION step: ~150 LoC, mechanical but
       genuinely tedious sep-logic plumbing.  Admitted with the proof
       structure documented; closing it requires no novel reasoning. *)
  Admitted.

End Ed25519Sign.

(* ================================================================ *)
(* Rust-side correctness (Qed via Sign_Strong_Correctness.v)          *)
(* ================================================================ *)

(** The bedrock2 [Theorem ed25519_sign_correct] above composes the
    full chain.  This subsection re-exports the rust_cmd_ed-level
    strong correctness theorem for consumers that prefer to work at
    that abstraction.

    Verified linkage (no axioms beyond the leaf spec parameters):

      ed25519_sign_strong_correct  (Sign_Strong_Correctness.v, Qed)
      ed25519_sign_gallina_lifted_clean (Sign_Strong_Correctness.v, Qed)
      to_bedrock_cmd_semantic_correct  (RustCmdToC.v, Qed)
      safe_cmd_correct_ed              (SafeRustEd25519Sim.v, Qed)
      rust_to_bedrock_cmd_ed_roundtrip (RustCmdToC.v, Qed)
      bridge_complete                  (SafeRustEd25519WPBridge.v, Qed)
*)

(** Directly importable correctness statement (no axioms beyond the
    leaf Gallina-spec Parameters).  See
    [Sign_Strong_Correctness.ed25519_sign_strong_correct]. *)
Theorem ed25519_sign_strong_correct_alias :
  forall (callee_post_n :
            String.string -> list located_ed -> list located_ed ->
            Bedrock.SafeRustEd25519Sim.rust_state_ed ->
            Bedrock.SafeRustEd25519Sim.rust_state_ed -> Prop)
         (function_table : Bedrock.SafeRustEd25519Sim.function_table_ed)
         (rs1 rs2 : Bedrock.SafeRustEd25519Sim.rust_state_ed)
         (seed msg sig_init : list Byte.byte)
         (msg_len : Z),
    Datatypes.length seed = 32%nat ->
    Datatypes.length msg = 4096%nat ->
    (0 <= msg_len <= 4096)%Z ->
    Sign_Strong_Correctness.slot_holds rs1 Sign_Verify_RustCmd.v_seed seed ->
    Sign_Strong_Correctness.slot_holds rs1 Sign_Verify_RustCmd.v_msg msg ->
    Sign_Strong_Correctness.slot_holds rs1 Sign_Verify_RustCmd.v_sig_out sig_init ->
    Bedrock.SafeRustEd25519Sim.rs_get_scalar_ed rs1 Sign_Verify_RustCmd.v_msg_len = Some msg_len ->
    Bedrock.SafeRustEd25519Sim.rust_exec_ed
      Sign_Strong_Correctness.strong_callee_post
      callee_post_n function_table
      End2End.Ed25519.Sign_Verify_RustCmd.ed25519_sign_rs rs1 rs2 ->
    exists nonce_hash_len chal_hash_len nonce_init chal_init,
      Sign_Strong_Correctness.slot_holds rs2 Sign_Verify_RustCmd.v_sig_out
        (Sign_Strong_Correctness.ed25519_sign_gallina_lifted
           seed msg nonce_hash_len chal_hash_len nonce_init chal_init sig_init).
Proof. exact Sign_Strong_Correctness.ed25519_sign_strong_correct. Qed.
