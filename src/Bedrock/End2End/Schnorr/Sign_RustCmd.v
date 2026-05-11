(** * Schnorr Sign as rust_cmd_ed
 *
 * Plain Schnorr signature scheme over the Ed25519 group.  Differs from
 * Ed25519 only in nonce derivation: Schnorr uses fresh randomness
 * [r_rand], whereas Ed25519 derives the nonce deterministically from
 * SHA-512(prefix || msg).  Everything else (point ops, challenge hash,
 * scalar arithmetic, serialisation) is identical.
 *
 * Protocol:
 *   R     = r_rand · B                            -- nonce commitment
 *   PK    = sk · B                                -- public key (typically precomputed)
 *   c     = SHA-512(R || PK || msg) mod L         -- challenge
 *   s     = (r_rand + c · sk) mod L               -- response
 *   sig   = R || s                                -- 64-byte signature
 *
 * Fifth user of the [rust_cmd_ed] framework after Ed25519 sign+verify,
 * XEdDSA sign, and Lizard inject+extract.  Reuses every Ed25519 leaf —
 * no new callees are introduced.  Mirrors [Sign_Verify_RustCmd.v]
 * step-for-step but skips the seed-hash + clamp + prefix-extract block
 * (Ed25519's steps 1–4).
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.SafeRustEd25519BorrowCheck.
Require Import Bedrock.End2End.Ed25519.Sign_Verify_RustCmd.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. Variable names                                                *)
(* ================================================================ *)

(** Entry-point arguments. *)
Definition v_sn_sk      := "sn_sk".       (* 32B private key   *)
Definition v_sn_msg     := "sn_msg".      (* 4096B message     *)
Definition v_sn_msg_len := "sn_msg_len".  (* dynamic length    *)
Definition v_sn_r_rand  := "sn_r_rand".   (* 32B random scalar *)
Definition v_sn_sig_out := "sn_sig_out".  (* 64B signature out *)

(** Internal slots (allocated via REdLetZero). *)
Definition v_sn_R_xyzt  := "sn_R_xyzt".   (* 200B intermediate R = r·B   *)
Definition v_sn_R_bytes := "sn_R_bytes".  (* 32B compressed R            *)
Definition v_sn_PK_xyzt := "sn_PK_xyzt".  (* 200B intermediate PK = sk·B *)
Definition v_sn_PK_bytes:= "sn_PK_bytes". (* 32B compressed PK           *)
Definition v_sn_chal_buf:= "sn_chal_buf". (* 4160B challenge buffer (R||PK||msg) *)
Definition v_sn_chal_full:= "sn_chal_full". (* 64B SHA-512 output       *)
Definition v_sn_c       := "sn_c".        (* 32B reduced challenge       *)

(** Buffer widths used by the protocol. *)
Definition sn_chal_width : nat := 4160. (* 32 + 32 + 4096 *)
Definition sn_msg_width  : nat := 4096.

(* ================================================================ *)
(* §2. schnorr_sign_rs as rust_cmd_ed                                *)
(* ================================================================ *)

(** Mirrors [ed25519_sign_rs]'s second half (the point-scalar arithmetic
    chain), substituting [v_sn_r_rand] for the SHA-512-derived nonce and
    [v_sn_sk] for the clamped Edwards scalar.  Reuses Ed25519 leaves:
    [ed25519_scalarmult_base], [ed25519_compress], [memmove_chal_R],
    [memmove_chal_A], [memmove_chal_M], [sha512_64], [scalar_reduce],
    [scalar_muladd], [memmove_sig_R]. *)
Definition schnorr_sign_rs : rust_cmd_ed :=
  REdLetZero v_sn_R_xyzt   (TBytes 200) (
  REdLetZero v_sn_R_bytes  (TBytes 32) (
  REdLetZero v_sn_PK_xyzt  (TBytes 200) (
  REdLetZero v_sn_PK_bytes (TBytes 32) (
  REdLetZero v_sn_chal_buf (TBytes sn_chal_width) (
  REdLetZero v_sn_chal_full(TBytes 64) (
  REdLetZero v_sn_c        (TBytes 32) (
  (* Step 1: R = r_rand · B *)
  REdSeq (REdCall "ed25519_scalarmult_base"
            (LE_TBytes v_sn_R_xyzt 200)
            [LE_TBytes v_sn_r_rand 32])
  (* Step 2: R_bytes = compress(R) *)
  (REdSeq (REdCall "ed25519_compress"
            (LE_TBytes v_sn_R_bytes 32)
            [LE_TBytes v_sn_R_xyzt 200])
  (* Step 3: PK = sk · B *)
  (REdSeq (REdCall "ed25519_scalarmult_base"
            (LE_TBytes v_sn_PK_xyzt 200)
            [LE_TBytes v_sn_sk 32])
  (* Step 4: PK_bytes = compress(PK) *)
  (REdSeq (REdCall "ed25519_compress"
            (LE_TBytes v_sn_PK_bytes 32)
            [LE_TBytes v_sn_PK_xyzt 200])
  (* Step 5a: chal_buf[0..32] = R_bytes *)
  (REdSeq (REdCall "memmove_chal_R"
            (LE_TBytes v_sn_chal_buf sn_chal_width)
            [LE_TBytes v_sn_R_bytes 32])
  (* Step 5b: chal_buf[32..64] = PK_bytes *)
  (REdSeq (REdCall "memmove_chal_A"
            (LE_TBytes v_sn_chal_buf sn_chal_width)
            [LE_TBytes v_sn_PK_bytes 32])
  (* Step 5c: chal_buf[64..64+msg_len] = msg *)
  (REdSeq (REdCall "memmove_chal_M"
            (LE_TBytes v_sn_chal_buf sn_chal_width)
            [LE_TBytes v_sn_msg sn_msg_width])
  (* Step 6: dynamic chal-hash length = 64 + msg_len *)
  (REdLetU64 "sn_chal_hash_len"
             (SAdd (SLit 64) (SVar v_sn_msg_len))
  (* Step 7: chal_full = SHA-512(chal_buf[0..chal_hash_len]) *)
  (REdSeq (REdCall "sha512_64"
            (LE_TBytes v_sn_chal_full 64)
            [LE_TBytes v_sn_chal_buf sn_chal_width;
             LE_TU64 "sn_chal_hash_len"])
  (* Step 8: c = reduce(chal_full) *)
  (REdSeq (REdCall "scalar_reduce"
            (LE_TBytes v_sn_c 32)
            [LE_TBytes v_sn_chal_full 64])
  (* Step 9: s = (r_rand + c·sk) mod L → writes first 32B of sig_out *)
  (REdSeq (REdCall "scalar_muladd"
            (LE_TBytes v_sn_sig_out 64)
            [LE_TBytes v_sn_r_rand 32;
             LE_TBytes v_sn_c 32;
             LE_TBytes v_sn_sk 32])
  (* Step 10: sig_out[0..32] = R_bytes (final R prefix placement) *)
  (REdCall "memmove_sig_R"
            (LE_TBytes v_sn_sig_out 64)
            [LE_TBytes v_sn_R_bytes 32]
  )))))))))))))))))).

Lemma borrow_ok_schnorr_sign : borrow_ok_ed schnorr_sign_rs = true.
Proof. vm_compute. reflexivity. Qed.

(** Well-formedness preservation theorem — framework baseline.  Parallel
    to [ed25519_sign_rs_correct] / [xeddsa_sign_rs_correct]. *)
Theorem schnorr_sign_rs_correct :
  forall callee_post callee_post_n function_table rs1 rs2,
    callee_post_well_formed callee_post ->
    callee_post_n_well_formed callee_post_n ->
    rs_well_formed rs1 ->
    rust_exec_ed callee_post callee_post_n function_table schnorr_sign_rs rs1 rs2 ->
    rs_well_formed rs2.
Proof.
  intros callee_post callee_post_n function_table rs1 rs2 Hcp Hcpn Hwf Hexec.
  eapply rust_exec_ed_preserves_wf; eassumption.
Qed.
