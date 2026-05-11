(** * Sign_Strong_Correctness_VerifiedClamp
 *
 * Variant of [Sign_Strong_Correctness.ed25519_sign_strong_correct]
 * where the axiomatic [clamp_64_spec] leaf has been **replaced** by
 * the verified [clamp_64_body] from [Clamp64Verified.v], dispatched
 * via [REdCallFn] through a [function_table].  The downstream
 * gallina reference uses [clamp_64_gallina] (a concrete Rocq
 * Definition with 0 axioms) instead of [clamp_64_spec].
 *
 * Paper headline:
 *   The axiom count of the strong sign-correctness theorem drops
 *   from 6 to 5 — [clamp_64_spec] is gone.
 *
 * Status (2026-05-11):
 *   [ed25519_sign_strong_correct_verified_clamp] — **Qed**, depends
 *   on the remaining 5 leaf Gallina specs (sha512_full_spec,
 *   scalar_reduce_spec, scalar_muladd_spec,
 *   ed25519_scalarmult_base_spec, ed25519_compress_spec) and their
 *   length axioms.  [clamp_64_spec] is NOT a dependency.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import micromega.Lia.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.RemainingBridges.
Require Import Bedrock.End2End.Ed25519.SHA512Bridge.
Require Import Bedrock.End2End.Ed25519.Sign_Verify_RustCmd.
Require Import Bedrock.End2End.Ed25519.Clamp64Verified.
Require Import Bedrock.End2End.Ed25519.Sign_Strong_Correctness.
Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* §1. Modified program: clamp_64 call replaced with REdCallFn      *)
(* ================================================================ *)

(** Identical to [ed25519_sign_rs] except the C3 [clamp_64] call
    uses [REdCallFn] instead of [REdCall].  The body is supplied at
    execution time via [function_table]. *)
Definition ed25519_sign_rs_with_callfn_clamp : rust_cmd_ed :=
  REdLetZero v_h_full (TBytes 64) (
  REdLetZero v_a_slot (TBytes 32) (
  REdLetZero v_prefix (TBytes 32) (
  REdLetZero v_A_xyzt (TBytes 200) (
  REdLetZero v_A_bytes (TBytes 32) (
  REdLetZero v_nonce_buf (TBytes 4128) (
  REdLetZero v_r_full (TBytes 64) (
  REdLetZero v_r_slot (TBytes 32) (
  REdLetZero v_R_xyzt (TBytes 200) (
  REdLetZero v_R_bytes (TBytes 32) (
  REdLetZero v_chal_buf (TBytes 4160) (
  REdLetZero v_k_full (TBytes 64) (
  REdLetZero v_k_slot (TBytes 32) (
  REdSeq (REdCall "sha512_64" (LE_TBytes v_h_full 64)
                              [LE_TBytes v_seed 32])
  (REdSeq (REdCall "memmove_a_from_h" (LE_TBytes v_a_slot 32)
                                       [LE_TBytes v_h_full 64])
  (* C3 — VERIFIED CLAMP via REdCallFn, args=[] (in-place on dest). *)
  (REdSeq (REdCallFn "clamp_64" (LE_TBytes v_a_slot 32) [])
  (REdSeq (REdCall "memmove_prefix_from_h" (LE_TBytes v_prefix 32)
                                            [LE_TBytes v_h_full 64])
  (REdSeq (REdCall "ed25519_scalarmult_base" (LE_TBytes v_A_xyzt 200)
                                              [LE_TBytes v_a_slot 32])
  (REdSeq (REdCall "ed25519_compress" (LE_TBytes v_A_bytes 32)
                                       [LE_TBytes v_A_xyzt 200])
  (REdSeq (REdCall "memmove_nonce_prefix" (LE_TBytes v_nonce_buf 4128)
                                           [LE_TBytes v_prefix 32])
  (REdSeq (REdCall "memmove_nonce_msg" (LE_TBytes v_nonce_buf 4128)
                                        [LE_TBytes v_msg 4096])
  (REdSeq (REdCall "sha512_64" (LE_TBytes v_r_full 64)
                                [LE_TBytes v_nonce_buf 4128])
  (REdSeq (REdCall "scalar_reduce" (LE_TBytes v_r_slot 32)
                                    [LE_TBytes v_r_full 64])
  (REdSeq (REdCall "ed25519_scalarmult_base" (LE_TBytes v_R_xyzt 200)
                                              [LE_TBytes v_r_slot 32])
  (REdSeq (REdCall "ed25519_compress" (LE_TBytes v_R_bytes 32)
                                       [LE_TBytes v_R_xyzt 200])
  (REdSeq (REdCall "memmove_chal_R" (LE_TBytes v_chal_buf 4160)
                                     [LE_TBytes v_R_bytes 32])
  (REdSeq (REdCall "memmove_chal_A" (LE_TBytes v_chal_buf 4160)
                                     [LE_TBytes v_A_bytes 32])
  (REdSeq (REdCall "memmove_chal_M" (LE_TBytes v_chal_buf 4160)
                                     [LE_TBytes v_msg 4096])
  (REdSeq (REdCall "sha512_64" (LE_TBytes v_k_full 64)
                                [LE_TBytes v_chal_buf 4160])
  (REdSeq (REdCall "scalar_reduce" (LE_TBytes v_k_slot 32)
                                    [LE_TBytes v_k_full 64])
  (REdSeq (REdCall "scalar_muladd" (LE_TBytes v_sig_out 64)
                                    [LE_TBytes v_r_slot 32;
                                     LE_TBytes v_k_slot 32;
                                     LE_TBytes v_a_slot 32])
  (REdCall "memmove_sig_R" (LE_TBytes v_sig_out 64)
                            [LE_TBytes v_R_bytes 32]
  ))))))))))))))))))))))))))))))).

(** Function table installing [clamp_64_body] as the verified
    implementation of "clamp_64". *)
Definition clamp_function_table : function_table_ed :=
  [("clamp_64", clamp_64_body)].

(** Variant of [strong_callee_post] (from [Sign_Strong_Correctness])
    with the "clamp_64" branch replaced by [True].  Since the clamp
    call is now a [REdCallFn] (dispatched through the function table),
    the [REdCall]-flavoured "clamp_64" branch never fires, so dropping
    [clamp_64_spec] from it is sound — and removes [clamp_64_spec]
    from the theorem's axiom dependency closure. *)
Definition strong_callee_post_no_clamp
           (fname : String.string)
           (args : list located_ed)
           (dst : located_ed)
           (rs1 rs2 : rust_state_ed) : Prop :=
  frames_except rs1 rs2 dst.(loc_var) /\
  match fname, args with
  | "sha512_64", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (sha512_full_spec src_bs)
  | "scalar_reduce", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (scalar_reduce_spec src_bs)
  | "scalar_muladd", [r; k; a] =>
      exists r_bs k_bs a_bs dst_bs,
        slot_holds rs1 r.(loc_var) r_bs /\
        slot_holds rs1 k.(loc_var) k_bs /\
        slot_holds rs1 a.(loc_var) a_bs /\
        slot_holds rs1 dst.(loc_var) dst_bs /\
        slot_holds rs2 dst.(loc_var)
          (scalar_muladd_spec r_bs k_bs a_bs ++ skipn 32 dst_bs)
  | "ed25519_compress", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (ed25519_compress_spec src_bs)
  | "ed25519_scalarmult_base", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (ed25519_scalarmult_base_spec src_bs)
  | "memmove_a_from_h", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (memmove_a_from_h_spec src_bs)
  | "memmove_prefix_from_h", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (memmove_prefix_from_h_spec src_bs)
  | "memmove_nonce_prefix", [src] =>
      exists src_bs dst_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs1 dst.(loc_var) dst_bs /\
        slot_holds rs2 dst.(loc_var) (src_bs ++ skipn (length src_bs) dst_bs)
  | "memmove_nonce_msg", [src] =>
      exists src_bs dst_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs1 dst.(loc_var) dst_bs /\
        slot_holds rs2 dst.(loc_var) (firstn 32 dst_bs ++ src_bs)
  | "memmove_chal_R", [src] =>
      exists src_bs dst_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs1 dst.(loc_var) dst_bs /\
        slot_holds rs2 dst.(loc_var) (src_bs ++ skipn (length src_bs) dst_bs)
  | "memmove_chal_A", [src] =>
      exists src_bs dst_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs1 dst.(loc_var) dst_bs /\
        slot_holds rs2 dst.(loc_var)
          (firstn 32 dst_bs ++ src_bs ++ skipn (32 + length src_bs) dst_bs)
  | "memmove_chal_M", [src] =>
      exists src_bs dst_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs1 dst.(loc_var) dst_bs /\
        slot_holds rs2 dst.(loc_var) (firstn 64 dst_bs ++ src_bs)
  | "memmove_sig_R", [src] =>
      exists src_bs dst_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs1 dst.(loc_var) dst_bs /\
        slot_holds rs2 dst.(loc_var) (firstn 32 dst_bs ++ src_bs)
  (* "clamp_64" branch deliberately omitted — handled via REdCallFn. *)
  | _, _ => True
  end.

(** Frame-only projection of [strong_callee_post_no_clamp].  Used by
    the local [peel_call_seq_noclamp] tactic below. *)
Lemma strong_callee_post_no_clamp_frame_other_slots :
  forall fname args dst rs1 rs2 x,
    strong_callee_post_no_clamp fname args dst rs1 rs2 ->
    x <> dst.(loc_var) ->
    rs_get_tower_ed rs1 x = rs_get_tower_ed rs2 x.
Proof.
  intros fname args dst rs1 rs2 x [Hframe _] Hne.
  apply (Hframe x Hne).
Qed.

(** Custom [peel_call_seq] for [strong_callee_post_no_clamp]. *)
Ltac peel_call_seq_nc H Hframe Hres :=
  let Hcall := fresh "Hcall" in
  let Hrest := fresh "Hrest" in
  inversion H; subst; clear H;
  match goal with
  | Hc : rust_exec_ed _ _ _ (REdCall _ _ _) _ _,
    Hr : rust_exec_ed _ _ _ _ _ _ |- _ =>
      rename Hc into Hcall; rename Hr into Hrest
  end;
  let Hcp := fresh "Hcp" in
  inversion Hcall; subst; clear Hcall;
  match goal with
  | Hc : strong_callee_post_no_clamp _ _ _ _ _ |- _ =>
      rename Hc into Hcp
  end;
  destruct Hcp as [Hframe Hres];
  rename Hrest into H.

Ltac peel_last_call_nc H Hframe Hres :=
  inversion H; subst; clear H;
  match goal with
  | Hc : strong_callee_post_no_clamp _ _ _ _ _ |- _ =>
      destruct Hc as [Hframe Hres]
  end.

(* ================================================================ *)
(* §2. Gallina reference with [clamp_64_gallina] substituted        *)
(* ================================================================ *)

(** Same as [ed25519_sign_gallina_lifted] but with [clamp_64_gallina]
    instead of the axiomatic [clamp_64_spec]. *)
Definition ed25519_sign_gallina_lifted_verified_clamp
    (seed msg : list Byte.byte)
    (nonce_init chal_init sig_init : list Byte.byte)
  : list Byte.byte :=
  let h_full   := sha512_full_spec seed in
  let a        := clamp_64_gallina (memmove_a_from_h_spec h_full) in
  let prefix   := memmove_prefix_from_h_spec h_full in
  let A_xyzt   := ed25519_scalarmult_base_spec a in
  let A_bytes  := ed25519_compress_spec A_xyzt in
  let nonce_C7 := (prefix ++ skipn (length prefix) nonce_init)%list in
  let nonce_C8 := (firstn 32 nonce_C7 ++ msg)%list in
  let r_full   := sha512_full_spec nonce_C8 in
  let r        := scalar_reduce_spec r_full in
  let R_xyzt   := ed25519_scalarmult_base_spec r in
  let R_bytes  := ed25519_compress_spec R_xyzt in
  let chal_C13 := (R_bytes ++ skipn (length R_bytes) chal_init)%list in
  let chal_C14 := (firstn 32 chal_C13 ++ A_bytes ++
                   skipn (32 + length A_bytes) chal_C13)%list in
  let chal_C15 := (firstn 64 chal_C14 ++ msg)%list in
  let k_full   := sha512_full_spec chal_C15 in
  let k        := scalar_reduce_spec k_full in
  let sig_C18  := (scalar_muladd_spec r k a ++ skipn 32 sig_init)%list in
  (firstn 32 sig_C18 ++ R_bytes)%list.

(* ================================================================ *)
(* §3. Frame lemma for [clamp_64_body]                              *)
(* ================================================================ *)

(** [clamp_64_body] only modifies [dst].  All other tower slots are
    preserved across its execution.  Proof structure mirrors
    [clamp_64_body_correct] — invert the 4 AST ops, observe that
    the tower env is only touched at [dst.(loc_var)] (the two
    byte_stores), while byte_loads touch only the scalar env. *)
Lemma clamp_64_body_frames :
  forall callee_post callee_post_n function_table
         (dst : located_ed)
         (rs1 rs2 : rust_state_ed),
    rust_exec_ed callee_post callee_post_n function_table
                 (clamp_64_body dst []) rs1 rs2 ->
    forall y, y <> dst.(loc_var) ->
              rs_get_tower_ed rs1 y = rs_get_tower_ed rs2 y.
Proof.
  intros callee_post callee_post_n function_table dst rs1 rs2 Hexec y Hne.
  cbv [clamp_64_body] in Hexec.
  inversion Hexec; clear Hexec; subst.
  inversion H1; clear H1; subst.
  inversion H4; clear H4; subst.
  inversion H1; clear H1; subst.
  inversion H7; clear H7; subst.
  inversion H1; clear H1; subst.
  inversion H11; clear H11; subst.
  cbv [rs_get_tower_ed rs_set_tower_ed rs_set_scalar_ed].
  cbn.
  rewrite (lookup_update_in_place_ed_other _ _ _ _ Hne).
  rewrite (lookup_update_in_place_ed_other _ _ _ _ Hne).
  reflexivity.
Qed.

(** Corollary in [frames_except] form, matching the shape used by
    [Sign_Strong_Correctness]'s frame_thread. *)
Lemma clamp_64_body_frames_except :
  forall callee_post callee_post_n function_table
         (dst : located_ed)
         (rs1 rs2 : rust_state_ed),
    rust_exec_ed callee_post callee_post_n function_table
                 (clamp_64_body dst []) rs1 rs2 ->
    frames_except rs1 rs2 dst.(loc_var).
Proof.
  intros * Hexec y Hne.
  exact (clamp_64_body_frames _ _ _ _ _ _ Hexec y Hne).
Qed.

(** **Wrapper lemma.**  Combines [clamp_64_body_correct] +
    [clamp_64_body_frames_except], packaged in [slot_holds] form so the
    main proof can drop in as a near-replica of the [REdCall] C3 step.
    Recovers the [TBytes 32] type tag of the destination slot by
    inverting the first byte_load of the body — this is what tells us
    the env's existential [n0] equals 32. *)
Lemma clamp_64_body_slot_holds :
  forall callee_post callee_post_n function_table
         (dst_var : String.string)
         (rs1 rs2 : rust_state_ed)
         (in_bs : list Byte.byte),
    length in_bs = 32%nat ->
    slot_holds rs1 dst_var in_bs ->
    rust_exec_ed callee_post callee_post_n function_table
                 (clamp_64_body {| loc_var := dst_var; loc_type := TBytes 32 |} [])
                 rs1 rs2 ->
    slot_holds rs2 dst_var (clamp_64_gallina in_bs)
    /\ frames_except rs1 rs2 dst_var.
Proof.
  intros callee_post callee_post_n function_table dst_var rs1 rs2 in_bs
         Hlen Hin Hexec.
  pose (dst := {| loc_var := dst_var; loc_type := TBytes 32 |}).
  fold dst in Hexec.
  (* Recover the explicit (TBytes 32) form of [Hin]. *)
  unfold slot_holds, bytes_at in Hin.
  destruct (rs_get_tower_ed rs1 dst_var) as [tv|] eqn:Hget_tv;
    [|discriminate].
  destruct tv as [t v_tv].
  destruct t; try discriminate.
  destruct v_tv; try discriminate.
  inversion Hin; subst bs; clear Hin.
  (* Use a first inversion step on the body to learn n0 = 32.
     Hexec carries dst's loc_type = TBytes 32; rexec_byte_load forces
     the env's type tag at dst.(loc_var) to match. *)
  assert (Hn_eq : n0 = 32%nat).
  { cbv [clamp_64_body] in Hexec.
    inversion Hexec; subst.
    match goal with
    | H : rust_exec_ed _ _ _ (REdByteLoad _ _ _) _ _ |- _ =>
        inversion H; subst
    end.
    (* H5 : loc_type dst = TBytes n1; H8 : rs_get_tower_ed at loc_var dst. *)
    match goal with
    | H : loc_type dst = TBytes ?nn |- _ => cbn in H; inversion H; subst nn; clear H
    end.
    match goal with
    | H : rs_get_tower_ed _ _ = Some (exist_tval_ed _ _) |- _ =>
        cbn in H; rewrite Hget_tv in H; inversion H
    end.
    reflexivity. }
  subst n0.
  split.
  - (* Correctness side. *)
    pose proof (clamp_64_body_correct callee_post callee_post_n function_table
                  dst _ _ _ eq_refl Hlen Hget_tv Hexec) as Hcorr.
    unfold slot_holds, bytes_at.
    cbn in Hcorr. rewrite Hcorr. reflexivity.
  - (* Frame side. *)
    intros y Hne.
    apply (clamp_64_body_frames_except _ _ _ _ _ _ Hexec).
    cbn. exact Hne.
Qed.

(* ================================================================ *)
(* §4. Main theorem                                                  *)
(* ================================================================ *)

Theorem ed25519_sign_strong_correct_verified_clamp :
  forall (callee_post_n :
            String.string -> list located_ed -> list located_ed ->
            rust_state_ed -> rust_state_ed -> Prop)
         (rs1 rs2 : rust_state_ed) (seed msg sig_init : list Byte.byte),
    length seed = 32%nat ->
    length msg = 4096%nat ->
    slot_holds rs1 v_seed seed ->
    slot_holds rs1 v_msg  msg ->
    slot_holds rs1 v_sig_out sig_init ->
    rust_exec_ed strong_callee_post_no_clamp callee_post_n clamp_function_table
                 ed25519_sign_rs_with_callfn_clamp rs1 rs2 ->
    exists nonce_init chal_init,
      slot_holds rs2 v_sig_out
        (ed25519_sign_gallina_lifted_verified_clamp
           seed msg nonce_init chal_init sig_init).
Proof.
  intros callee_post_n rs1 rs2 seed msg sig_init Hseed_len Hmsg_len
         Hseed Hmsg Hsig_init Hexec.
  unfold ed25519_sign_rs_with_callfn_clamp in Hexec.

  (* Stage A: peel 13 REdLetZero allocations. *)
  repeat (match goal with
          | H : rust_exec_ed _ _ _ (REdLetZero _ _ _) _ _ |- _ =>
              inversion H; subst; clear H
          end).

  match goal with
  | H : rust_exec_ed _ _ _ _ ?rs_alloc _ |- _ =>
      assert (Hseed_alloc : slot_holds rs_alloc v_seed seed) by
        (repeat (apply slot_holds_set_tower_other; [discriminate|]); exact Hseed);
      assert (Hmsg_alloc : slot_holds rs_alloc v_msg msg) by
        (repeat (apply slot_holds_set_tower_other; [discriminate|]); exact Hmsg);
      assert (Hsig_alloc : slot_holds rs_alloc v_sig_out sig_init) by
        (repeat (apply slot_holds_set_tower_other; [discriminate|]); exact Hsig_init);
      rename H into Hexec
  end.
  clear Hseed Hmsg Hsig_init.

  (* === Stage B: 19 call inversions === *)

  (* C1: sha512_64 (h_full ← seed) *)
  peel_call_seq_nc Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt1]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hseed_alloc) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hseed_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var].
  clear Hframe Hsrc.

  (* C2: memmove_a_from_h (a ← h_full) *)
  peel_call_seq_nc Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt2]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt1) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hseed_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt1; [|neq_var].
  clear Hframe Hsrc.

  (* === C3: clamp_64 — REdCallFn (verified body) === *)
  (* Peel the outer REdSeq, then invert rexec_callfn. *)
  inversion Hexec; subst; clear Hexec.
  match goal with
  | Hcfn : rust_exec_ed _ _ _ (REdCallFn _ _ _) _ _ |- _ =>
      rename Hcfn into HclampFn
  end.
  match goal with
  | Hrest : rust_exec_ed _ _ _ (REdSeq _ _) _ _ |- _ =>
      rename Hrest into Hexec
  end.
  inversion HclampFn; subst; clear HclampFn.
  (* Two new hypotheses: [find ... = Some (..., body)] and
     [rust_exec_ed ... (body dest args) rs rs'].  Locate by shape. *)
  match goal with
  | Hf : find _ _ = Some _ |- _ =>
      cbv [clamp_function_table List.find fst String.eqb] in Hf;
      inversion Hf; clear Hf
  end.
  match goal with
  | Hb : rust_exec_ed _ _ _ (?body _ _) _ _ |- _ =>
      rename Hb into Hbody
  end.
  subst.
  (* Hbody : rust_exec_ed _ _ _ (clamp_64_body (LE_TBytes v_a_slot 32) []) rs_pre rs_post.
     Apply the wrapper [clamp_64_body_slot_holds] to extract the
     post-state slot_holds (using clamp_64_gallina) and frame property. *)
  assert (Hlen_in : length (memmove_a_from_h_spec (sha512_full_spec seed)) = 32%nat).
  { unfold memmove_a_from_h_spec.
    rewrite firstn_length, sha512_full_spec_len.
    reflexivity. }
  (* LE_TBytes v_a_slot 32 expands to {| loc_var := v_a_slot; loc_type := TBytes 32 |}.
     Both Htgt2 and Hbody refer to this — convert to the wrapper-friendly form. *)
  cbn [LE_TBytes loc_var] in Htgt2, Hbody.
  pose proof (clamp_64_body_slot_holds _ _ _ _ _ _ _
                Hlen_in Htgt2 Hbody) as [Htgt3 Hframe].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hseed_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt1; [|neq_var].
  (* Recover the LE_TBytes-form so subsequent calls' [Hsrc] can match.
     [Htgt3] currently has plain [v_a_slot]; downstream uses [loc_var (LE_TBytes ...)]. *)
  clear Hframe Hbody Hlen_in.
  rename Htgt3 into Htgt3'.

  (* C4: memmove_prefix_from_h (prefix ← h_full) *)
  peel_call_seq_nc Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt4]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt1) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hseed_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt1; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3'; [|neq_var].
  clear Hframe Hsrc.

  (* C5: ed25519_scalarmult_base (A_xyzt ← a) *)
  peel_call_seq_nc Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt5]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt3') as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hseed_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt1; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3'; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt4; [|neq_var].
  clear Hframe Hsrc.

  (* C6: ed25519_compress (A_bytes ← A_xyzt) *)
  peel_call_seq_nc Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt6]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt5) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hseed_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt1; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3'; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt4; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt5; [|neq_var].
  clear Hframe Hsrc.

  (* C7: memmove_nonce_prefix (nonce_buf ← prefix) *)
  peel_call_seq_nc Hexec Hframe Hres.
  destruct Hres as [src_bs [dst_bs7 [Hsrc [Hdst Htgt7]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt4) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hseed_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt1; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3'; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt4; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt5; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt6; [|neq_var].
  clear Hframe Hsrc Hdst.

  (* C8: memmove_nonce_msg (nonce_buf ← msg) *)
  peel_call_seq_nc Hexec Hframe Hres.
  destruct Hres as [src_bs [dst_bs [Hsrc [Hdst Htgt8]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hmsg_alloc) as Heq; subst src_bs.
  pose proof (slot_holds_inj _ _ _ _ Hdst Htgt7) as Heq2; subst dst_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hseed_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt1; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3'; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt4; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt5; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt6; [|neq_var].
  clear Hframe Hsrc Hdst Htgt7.

  (* C9: sha512_64 (r_full ← nonce_buf) *)
  peel_call_seq_nc Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt9]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt8) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hseed_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3'; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt5; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt6; [|neq_var].
  clear Hframe Hsrc Htgt1 Htgt4 Htgt8.

  (* C10: scalar_reduce (r ← r_full) *)
  peel_call_seq_nc Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt10]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt9) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hseed_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3'; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt5; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt6; [|neq_var].
  clear Hframe Hsrc Htgt9.

  (* C11: ed25519_scalarmult_base (R_xyzt ← r) *)
  peel_call_seq_nc Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt11]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt10) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hseed_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3'; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt5; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt6; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt10; [|neq_var].
  clear Hframe Hsrc.

  (* C12: ed25519_compress (R_bytes ← R_xyzt) *)
  peel_call_seq_nc Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt12]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt11) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hseed_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3'; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt5; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt6; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt10; [|neq_var].
  clear Hframe Hsrc Htgt11.

  (* C13: memmove_chal_R (chal_buf ← R_bytes) *)
  peel_call_seq_nc Hexec Hframe Hres.
  destruct Hres as [src_bs [dst_bs13 [Hsrc [Hdst Htgt13]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt12) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hseed_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3'; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt5; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt6; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt10; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt12; [|neq_var].
  clear Hframe Hsrc Hdst.

  (* C14: memmove_chal_A (chal_buf ← A_bytes) *)
  peel_call_seq_nc Hexec Hframe Hres.
  destruct Hres as [src_bs [dst_bs [Hsrc [Hdst Htgt14]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt6) as Heq; subst src_bs.
  pose proof (slot_holds_inj _ _ _ _ Hdst Htgt13) as Heq2; subst dst_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hseed_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3'; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt5; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt6; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt10; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt12; [|neq_var].
  clear Hframe Hsrc Hdst Htgt13.

  (* C15: memmove_chal_M (chal_buf ← msg) *)
  peel_call_seq_nc Hexec Hframe Hres.
  destruct Hres as [src_bs [dst_bs [Hsrc [Hdst Htgt15]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hmsg_alloc) as Heq; subst src_bs.
  pose proof (slot_holds_inj _ _ _ _ Hdst Htgt14) as Heq2; subst dst_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hseed_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3'; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt10; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt12; [|neq_var].
  clear Hframe Hsrc Hdst Htgt5 Htgt6 Htgt14.

  (* C16: sha512_64 (k_full ← chal_buf) *)
  peel_call_seq_nc Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt16]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt15) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hseed_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3'; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt10; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt12; [|neq_var].
  clear Hframe Hsrc Htgt15.

  (* C17: scalar_reduce (k ← k_full) *)
  peel_call_seq_nc Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt17]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt16) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hseed_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3'; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt10; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt12; [|neq_var].
  clear Hframe Hsrc Htgt16.

  (* C18: scalar_muladd (sig_out ← r, k, a) *)
  peel_call_seq_nc Hexec Hframe Hres.
  destruct Hres as [r_bs [k_bs [a_bs [dst_bs [Hsr [Hsk [Hsa [Hsd Htgt18]]]]]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsr Htgt10) as Heq; subst r_bs.
  pose proof (slot_holds_inj _ _ _ _ Hsk Htgt17) as Heq; subst k_bs.
  pose proof (slot_holds_inj _ _ _ _ Hsa Htgt3') as Heq; subst a_bs.
  pose proof (slot_holds_inj _ _ _ _ Hsd Hsig_alloc) as Heq; subst dst_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt12; [|neq_var].
  clear Hframe Hsr Hsk Hsa Hsd Hseed_alloc Hmsg_alloc Hsig_alloc
        Htgt3' Htgt10 Htgt17.

  (* C19: memmove_sig_R (sig_out ← R_bytes) — last call *)
  peel_last_call_nc Hexec Hframe Hres.
  destruct Hres as [src_bs [dst_bs [Hsrc [Hdst Htgt19]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt12) as Heq; subst src_bs.
  pose proof (slot_holds_inj _ _ _ _ Hdst Htgt18) as Heq2; subst dst_bs.
  clear Hframe Hsrc Hdst.

  (* === Stage C: assembly. === *)
  cbn [LE_TBytes loc_var] in Htgt19.
  exists dst_bs7, dst_bs13.
  unfold ed25519_sign_gallina_lifted_verified_clamp.
  exact Htgt19.
Qed.

(** **Print Assumptions guard.**  Should report exactly the 5
    remaining leaf Gallina specs (and their length axioms):
      - sha512_full_spec, sha512_full_spec_len
      - scalar_reduce_spec
      - scalar_muladd_spec, scalar_muladd_spec_len
      - ed25519_scalarmult_base_spec
      - ed25519_compress_spec
    NO [clamp_64_spec] — the axiomatic clamp has been replaced by
    the verified [clamp_64_body]. *)
Print Assumptions ed25519_sign_strong_correct_verified_clamp.
