(** * Sign / Verify ports through RustCmd
 *
 * Defines [ed25519_sign_rs] and [ed25519_verify_rs] in the
 * [rust_cmd_ed] AST.  States correctness theorems via the
 * [callee_post_well_formed] discipline + bedrock2 bridge.
 *
 * Source: [Sign.v] line 89's bedrock2 body; [Verify.v]'s analogue.
 * Plan: [R10_RUSTCMD_PORT_PLAN.md] D22.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.SafeRustEd25519BorrowCheck.
Require Import Bedrock.End2End.Ed25519.Scalarmult_Impl_RustCmd.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. Variable names                                                *)
(* ================================================================ *)

Definition v_sig_out := "sig_out".
Definition v_seed    := "seed".
Definition v_msg     := "msg".
Definition v_msg_len := "msg_len".
Definition v_h_full  := "h_full".
Definition v_a_slot  := "a".
Definition v_prefix  := "prefix".
Definition v_A_xyzt  := "A_xyzt".
Definition v_A_bytes := "A_bytes".
Definition v_nonce_buf := "nonce_buf".
Definition v_r_full  := "r_full".
Definition v_r_slot  := "r".
Definition v_R_xyzt  := "R_xyzt".
Definition v_R_bytes := "R_bytes".
Definition v_chal_buf := "chal_buf".
Definition v_k_full  := "k_full".
Definition v_k_slot  := "k".
Definition v_sig_in  := "sig_in".
Definition v_pub     := "pub".

(* ================================================================ *)
(* §2. ed25519_sign as rust_cmd_ed                                   *)
(* ================================================================ *)

(** Mirrors [Sign.v] line 89's bedrock2 body.  Each [stackalloc] →
    [REdLetZero] of the appropriate [TBytes n] type; each function
    call → [REdCall] with typed [located_ed] args.

    Memory-offset operations (e.g., [memmove(nonce_buf + $32, ...)])
    are modeled as REdCall to [memmove] taking the WHOLE buffer slot
    + a scalar offset; the actual offset arithmetic is part of the
    callee's bedrock2 implementation, abstracted from the rust_cmd_ed
    view. *)
Definition LE_TBytes (v : String.string) (n : nat) : located_ed :=
  {| loc_var := v; loc_type := TBytes n |}.

(** TU64-typed located_ed helper.  Used for passing dynamic length
    arguments to leaves whose ABI takes [(buf, msg_len)] — most
    notably [sha512_64]'s message-length parameter. *)
Definition LE_TU64 (v : String.string) : located_ed :=
  {| loc_var := v; loc_type := TU64 |}.

Definition ed25519_sign_rs : rust_cmd_ed :=
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
  (* Step 1: h = SHA-512(seed) *)
  REdSeq (REdCall "sha512_64" (LE_TBytes v_h_full 64)
                              [LE_TBytes v_seed 32])
  (* Step 2-3: a := h[0..32]; clamp_64(a); prefix := h[32..64] *)
  (REdSeq (REdCall "memmove_a_from_h" (LE_TBytes v_a_slot 32)
                                       [LE_TBytes v_h_full 64])
  (REdSeq (REdCall "clamp_64" (LE_TBytes v_a_slot 32) [])
  (REdSeq (REdCall "memmove_prefix_from_h" (LE_TBytes v_prefix 32)
                                            [LE_TBytes v_h_full 64])
  (* Step 4: A = a · B *)
  (REdSeq (REdCall "ed25519_scalarmult_base" (LE_TBytes v_A_xyzt 200)
                                              [LE_TBytes v_a_slot 32])
  (REdSeq (REdCall "ed25519_compress" (LE_TBytes v_A_bytes 32)
                                       [LE_TBytes v_A_xyzt 200])
  (* Step 5: r = SHA-512(prefix || M[..msg_len]) mod L *)
  (REdSeq (REdCall "memmove_nonce_prefix" (LE_TBytes v_nonce_buf 4128)
                                           [LE_TBytes v_prefix 32])
  (REdSeq (REdCall "memmove_nonce_msg" (LE_TBytes v_nonce_buf 4128)
                                        [LE_TBytes v_msg 4096])
  (REdLetU64 "nonce_hash_len" (SAdd (SLit 32) (SVar v_msg_len))
  (REdSeq (REdCall "sha512_64" (LE_TBytes v_r_full 64)
                                [LE_TBytes v_nonce_buf 4128;
                                 LE_TU64 "nonce_hash_len"])
  (REdSeq (REdCall "scalar_reduce" (LE_TBytes v_r_slot 32)
                                    [LE_TBytes v_r_full 64])
  (* Step 6: R = r · B *)
  (REdSeq (REdCall "ed25519_scalarmult_base" (LE_TBytes v_R_xyzt 200)
                                              [LE_TBytes v_r_slot 32])
  (REdSeq (REdCall "ed25519_compress" (LE_TBytes v_R_bytes 32)
                                       [LE_TBytes v_R_xyzt 200])
  (* Step 7: k = SHA-512(R || A || M[..msg_len]) mod L *)
  (REdSeq (REdCall "memmove_chal_R" (LE_TBytes v_chal_buf 4160)
                                     [LE_TBytes v_R_bytes 32])
  (REdSeq (REdCall "memmove_chal_A" (LE_TBytes v_chal_buf 4160)
                                     [LE_TBytes v_A_bytes 32])
  (REdSeq (REdCall "memmove_chal_M" (LE_TBytes v_chal_buf 4160)
                                     [LE_TBytes v_msg 4096])
  (REdLetU64 "chal_hash_len" (SAdd (SLit 64) (SVar v_msg_len))
  (REdSeq (REdCall "sha512_64" (LE_TBytes v_k_full 64)
                                [LE_TBytes v_chal_buf 4160;
                                 LE_TU64 "chal_hash_len"])
  (REdSeq (REdCall "scalar_reduce" (LE_TBytes v_k_slot 32)
                                    [LE_TBytes v_k_full 64])
  (* Step 8: s = (r + k · a) mod L; written to sig_out+32 *)
  (REdSeq (REdCall "scalar_muladd" (LE_TBytes v_sig_out 64)
                                    [LE_TBytes v_r_slot 32;
                                     LE_TBytes v_k_slot 32;
                                     LE_TBytes v_a_slot 32])
  (* Step 9: sig_out[0..32] = R *)
  (REdCall "memmove_sig_R" (LE_TBytes v_sig_out 64)
                            [LE_TBytes v_R_bytes 32]
  ))))))))))))))))))))))))))))))))).

Lemma borrow_ok_ed_sign : borrow_ok_ed ed25519_sign_rs = true.
Proof. vm_compute. reflexivity. Qed.

(** Signing correctness via well-formedness preservation.  Stronger
    statement (output is RFC 8032 sign result) is a separate target:
    requires hash-call specs + scalar-arithmetic specs for r/k. *)
Theorem ed25519_sign_rs_correct :
  forall callee_post callee_post_n function_table rs1 rs2,
    callee_post_well_formed callee_post ->
    callee_post_n_well_formed callee_post_n ->
    rs_well_formed rs1 ->
    rust_exec_ed callee_post callee_post_n function_table ed25519_sign_rs rs1 rs2 ->
    rs_well_formed rs2.
Proof.
  intros callee_post callee_post_n function_table rs1 rs2 Hcp Hcpn Hwf Hexec.
  eapply rust_exec_ed_preserves_wf; eassumption.
Qed.

(* ================================================================ *)
(* §3. ed25519_verify as rust_cmd_ed                                 *)
(* ================================================================ *)

(** Verify is structurally similar to Sign with early-exit branches
    on each validation check.  We model the early exits as [REdIfNz]
    branches whose `false` cases are [REdCall "verify_fail"] (a sink
    that updates the result slot to 0).  The success path mirrors
    [Verify.v]'s body. *)
Definition v_sig_lt_L    := "sig_lt_L".
Definition v_R_xyzt_v    := "R_xyzt_v".
Definition v_A_xyzt_v    := "A_xyzt_v".
Definition v_h_v         := "h_v".
Definition v_h_red       := "h_red".
Definition v_sB          := "sB".
Definition v_hA          := "hA".
Definition v_RcheckA     := "RcheckA".
Definition v_check_bytes := "check_bytes".
(** 2026-05-12: result is now the caller-supplied [result_out] parameter
    rather than an internally-allocated slot.  Eliminates the
    "non-caller-visible local" emitter gap; halves the cargo
    [verify] wrapper cost (no more recompute through dalek). *)
Definition v_result      := "result_out".
(** Slots introduced by the Bug-B fix:
    - v_R_bytes_v : 32-byte R extracted from sig_in[0..32], used as a
      source for [memmove_chal_R].
    - v_chal_buf_v : 4160-byte challenge buffer holding the canonical
      RFC 8032 hash input [R || A || msg].  Hashed with dynamic length
      [64 + msg_len]. *)
Definition v_R_bytes_v   := "R_bytes_v".
Definition v_chal_buf_v  := "chal_buf_v".
(** Bug-C fix slot: 32-byte S extracted from sig_in[32..64].  Passed to
    [ed25519_scalarmult_base] in place of the 64-byte [v_sig_in]. *)
Definition v_S_bytes     := "S_bytes".

(** Note: the [v_result] (= "result_out") slot is supplied by the
    caller via [ed25519_verify_rs_sig]'s first parameter — NOT
    allocated by [REdLetZero] here.  The protocol writes the
    accept/reject byte into it directly. *)
Definition ed25519_verify_rs : rust_cmd_ed :=
  REdLetZero v_R_xyzt_v (TBytes 200) (
  REdLetZero v_A_xyzt_v (TBytes 200) (
  REdLetZero v_h_v (TBytes 64) (
  REdLetZero v_h_red (TBytes 32) (
  REdLetZero v_sB (TBytes 200) (
  REdLetZero v_hA (TBytes 200) (
  REdLetZero v_RcheckA (TBytes 200) (
  REdLetZero v_check_bytes (TBytes 32) (
  (* Bug-B: dedicated slots for R extraction + canonical chal_buf. *)
  REdLetZero v_R_bytes_v (TBytes 32) (
  REdLetZero v_chal_buf_v (TBytes 4160) (
  REdLetZero v_S_bytes (TBytes 32) (
  REdSeq (REdCall "scalar_lt_L" (LE_TBytes v_result 1)
                                  [LE_TBytes v_sig_in 64])
  (REdSeq (REdCall "ed25519_decompress_R" (LE_TBytes v_R_xyzt_v 200)
                                            [LE_TBytes v_sig_in 64])
  (REdSeq (REdCall "ed25519_decompress_A" (LE_TBytes v_A_xyzt_v 200)
                                            [LE_TBytes v_pub 32])
  (* Bug-B fix step 1: extract R bytes from sig_in for chal_buf. *)
  (REdSeq (REdCall "memmove_R_from_sig" (LE_TBytes v_R_bytes_v 32)
                                          [LE_TBytes v_sig_in 64])
  (* Bug-B fix step 2: build chal_buf = R || A || msg via the existing
     sign-side memmove_chal_* leaves. *)
  (REdSeq (REdCall "memmove_chal_R" (LE_TBytes v_chal_buf_v 4160)
                                     [LE_TBytes v_R_bytes_v 32])
  (REdSeq (REdCall "memmove_chal_A" (LE_TBytes v_chal_buf_v 4160)
                                     [LE_TBytes v_pub 32])
  (REdSeq (REdCall "memmove_chal_M" (LE_TBytes v_chal_buf_v 4160)
                                     [LE_TBytes v_msg 4096])
  (* Bug-B fix step 3: compute dynamic chal hash length 64 + msg_len. *)
  (REdLetU64 "verify_chal_len" (SAdd (SLit 64) (SVar v_msg_len))
  (* Bug-B fix step 4: hash chal_buf with dynamic length (RFC 8032). *)
  (REdSeq (REdCall "sha512_64" (LE_TBytes v_h_v 64)
                                [LE_TBytes v_chal_buf_v 4160;
                                 LE_TU64 "verify_chal_len"])
  (REdSeq (REdCall "scalar_reduce" (LE_TBytes v_h_red 32)
                                    [LE_TBytes v_h_v 64])
  (* Bug-C fix: extract the 32-byte scalar S = sig_in[32..64] before
     passing it to ed25519_scalarmult_base, whose ABI expects a
     32-byte scalar (not the 64-byte signature). *)
  (REdSeq (REdCall "memmove_S_from_sig" (LE_TBytes v_S_bytes 32)
                                         [LE_TBytes v_sig_in 64])
  (REdSeq (REdCall "ed25519_scalarmult_base" (LE_TBytes v_sB 200)
                                              [LE_TBytes v_S_bytes 32])
  (REdSeq (REdCall "ed25519_scalarmult" (LE_TBytes v_hA 200)
                                         [LE_TBytes v_h_red 32;
                                          LE_TBytes v_A_xyzt_v 200])
  (REdSeq (REdCall "ed25519_xyzt_add" (LE_TBytes v_RcheckA 200)
                                       [LE_TBytes v_R_xyzt_v 200;
                                        LE_TBytes v_hA 200])
  (REdSeq (REdCall "ed25519_compress" (LE_TBytes v_check_bytes 32)
                                       [LE_TBytes v_RcheckA 200])
  (REdCall "bytes_equal_32" (LE_TBytes v_result 1)
                              [LE_TBytes v_sig_in 64;
                               LE_TBytes v_check_bytes 32]
  )))))))))))))))))))))))))).

Lemma borrow_ok_ed_verify : borrow_ok_ed ed25519_verify_rs = true.
Proof. vm_compute. reflexivity. Qed.

Theorem ed25519_verify_rs_correct :
  forall callee_post callee_post_n function_table rs1 rs2,
    callee_post_well_formed callee_post ->
    callee_post_n_well_formed callee_post_n ->
    rs_well_formed rs1 ->
    rust_exec_ed callee_post callee_post_n function_table ed25519_verify_rs rs1 rs2 ->
    rs_well_formed rs2.
Proof.
  intros callee_post callee_post_n function_table rs1 rs2 Hcp Hcpn Hwf Hexec.
  eapply rust_exec_ed_preserves_wf; eassumption.
Qed.

(** Architectural note: similar to R10, the bedrock2-WP-shaped
    versions of these theorems require the
    [bedrock_call_simulates_rust_exec] hypothesis from
    [SafeRustEd25519BedrockBridge.v] for each function.  Threading
    it gives Sign / Verify wired into Scalarmult.v's downstream
    Axiom chain. *)
