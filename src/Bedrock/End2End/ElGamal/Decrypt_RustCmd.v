(** * ElGamal Decrypt as rust_cmd_ed
 *
 * Inverse of [elgamal_encrypt_rs]: given a 32-byte secret key [sk] and a
 * 64-byte ciphertext [ct = C1 || C2], recover the original 32-byte
 * Ristretto message point.
 *
 *   shared := sk · C1       (Diffie-Hellman shared point)
 *   msg    := C2 - shared   (subtract the blinding)
 *
 * Subtraction is implemented as [C2 + negate(shared)] via the new leaf
 * [ed25519_xyzt_negate].
 *
 * Protocol body (9 leaf calls):
 *
 *   1. memmove_R_from_sig       — C1_bytes     ← ct[0..32]         (32B)
 *   2. memmove_S_from_sig       — C2_bytes     ← ct[32..64]        (32B)
 *   3. ristretto_decode_or_fail — C1_xyzt      ← decode(C1_bytes)  (200B)
 *   4. ed25519_scalarmult       — shared_xyzt  ← sk · C1_xyzt      (200B)
 *   5. ed25519_xyzt_negate      — neg_shared   ← -shared_xyzt      (200B)
 *   6. ristretto_decode_or_fail — C2_xyzt      ← decode(C2_bytes)  (200B)
 *   7. ed25519_xyzt_add         — msg_xyzt     ← C2_xyzt + neg     (200B)
 *   8. ristretto_encode         — msg_out      ← compress(msg_xyzt)(32B)
 *
 * Mirrors [Encrypt_RustCmd.v] structurally: 7 [REdLetZero] intermediates,
 * Schnorr-style memmove split of the 64-byte input ciphertext into two
 * 32-byte halves, then the decode → scalarmult → negate → add → encode
 * chain.
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

(** Input/output slots (entry-point arguments). *)
Definition v_sk         := "sk".            (* 32B scalar secret key *)
Definition v_ct         := "ct".            (* 64B ciphertext input  *)
Definition v_msg_out    := "msg_out".       (* 32B recovered Ristretto *)

(** Internal slots (allocated via REdLetZero). *)
Definition v_C1_bytes_d := "C1_bytes_d".    (* 32B C1 extracted from ct *)
Definition v_C2_bytes_d := "C2_bytes_d".    (* 32B C2 extracted from ct *)
Definition v_C1_xyzt_d  := "C1_xyzt_d".     (* 200B decompressed C1     *)
Definition v_shared_d   := "shared_d".      (* 200B sk · C1             *)
Definition v_neg_shared := "neg_shared".    (* 200B -shared             *)
Definition v_C2_xyzt_d  := "C2_xyzt_d".     (* 200B decompressed C2     *)
Definition v_msg_xyzt_d := "msg_xyzt_d".    (* 200B C2 + (-shared)      *)

(* ================================================================ *)
(* §2. elgamal_decrypt as rust_cmd_ed                                *)
(* ================================================================ *)

Definition elgamal_decrypt_rs : rust_cmd_ed :=
  REdLetZero v_C1_bytes_d (TBytes 32) (
  REdLetZero v_C2_bytes_d (TBytes 32) (
  REdLetZero v_C1_xyzt_d  (TBytes 200) (
  REdLetZero v_shared_d   (TBytes 200) (
  REdLetZero v_neg_shared (TBytes 200) (
  REdLetZero v_C2_xyzt_d  (TBytes 200) (
  REdLetZero v_msg_xyzt_d (TBytes 200) (
  (* Step 1: C1_bytes = ct[0..32] *)
  REdSeq (REdCall "memmove_R_from_sig"
            (LE_TBytes v_C1_bytes_d 32)
            [LE_TBytes v_ct 64])
  (* Step 2: C2_bytes = ct[32..64] *)
  (REdSeq (REdCall "memmove_S_from_sig"
            (LE_TBytes v_C2_bytes_d 32)
            [LE_TBytes v_ct 64])
  (* Step 3: C1_xyzt = decode(C1_bytes) *)
  (REdSeq (REdCall "ristretto_decode_or_fail"
            (LE_TBytes v_C1_xyzt_d 200)
            [LE_TBytes v_C1_bytes_d 32])
  (* Step 4: shared = sk · C1_xyzt *)
  (REdSeq (REdCall "ed25519_scalarmult"
            (LE_TBytes v_shared_d 200)
            [LE_TBytes v_sk 32; LE_TBytes v_C1_xyzt_d 200])
  (* Step 5: neg_shared = -shared *)
  (REdSeq (REdCall "ed25519_xyzt_negate"
            (LE_TBytes v_neg_shared 200)
            [LE_TBytes v_shared_d 200])
  (* Step 6: C2_xyzt = decode(C2_bytes) *)
  (REdSeq (REdCall "ristretto_decode_or_fail"
            (LE_TBytes v_C2_xyzt_d 200)
            [LE_TBytes v_C2_bytes_d 32])
  (* Step 7: msg_xyzt = C2_xyzt + neg_shared *)
  (REdSeq (REdCall "ed25519_xyzt_add"
            (LE_TBytes v_msg_xyzt_d 200)
            [LE_TBytes v_C2_xyzt_d 200; LE_TBytes v_neg_shared 200])
  (* Step 8: msg_out = compress(msg_xyzt) *)
   (REdCall "ristretto_encode"
            (LE_TBytes v_msg_out 32)
            [LE_TBytes v_msg_xyzt_d 200])))))))))))))).

Lemma borrow_ok_elgamal_decrypt : borrow_ok_ed elgamal_decrypt_rs = true.
Proof. vm_compute. reflexivity. Qed.

(** Well-formedness preservation theorem — framework baseline. *)
Theorem elgamal_decrypt_rs_correct :
  forall callee_post callee_post_n function_table rs1 rs2,
    callee_post_well_formed callee_post ->
    callee_post_n_well_formed callee_post_n ->
    rs_well_formed rs1 ->
    rust_exec_ed callee_post callee_post_n function_table
                 elgamal_decrypt_rs rs1 rs2 ->
    rs_well_formed rs2.
Proof.
  intros callee_post callee_post_n function_table rs1 rs2 Hcp Hcpn Hwf Hexec.
  eapply rust_exec_ed_preserves_wf; eassumption.
Qed.
