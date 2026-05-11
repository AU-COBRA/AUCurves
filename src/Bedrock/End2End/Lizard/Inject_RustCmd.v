(** * Lizard Inject as rust_cmd_ed
 *
 * Signal's Lizard scheme injects 16 bytes of plaintext into a
 * Ristretto255 group element.  Used in Signal's prekey distribution
 * and sealed-sender.
 *
 * Canonical Lizard inject (16B plaintext → 32B Ristretto encoding):
 *
 *   1. lizard_pack: build a 32-byte buffer with the 16-byte plaintext
 *      in the middle (buf[0..8] || pt[0..16] || buf[24..32], where
 *      the padding bytes are derived from a hash of the plaintext).
 *   2. elligator2_to_edwards: apply the Elligator2 map to the 32B
 *      buffer, producing a Curve25519 point in Montgomery form, then
 *      convert to Edwards (xyzt) representation (200 bytes).
 *   3. ristretto_encode: serialise the Edwards point to 32B Ristretto.
 *
 * Mirrors the XEdDSA [Sign_RustCmd.v] structure: each [stackalloc]
 * becomes a [REdLetZero], each call becomes [REdCall] with typed
 * [located_ed] arguments.  The protocol body is a 3-call sequence
 * with 2 intermediate stack-allocated buffers.
 *
 * Third framework user after Ed25519 (sign/verify) and XEdDSA
 * (sign).  Demonstrates handling of Ristretto-based protocols
 * beyond standard Edwards curves.
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
Definition v_pt   := "pt".          (* 16B plaintext input *)
Definition v_out  := "out".         (* 32B Ristretto output *)

(** Internal slots (allocated via REdLetZero). *)
Definition v_buf32 := "buf32".      (* 32B intermediate (padded plaintext) *)
Definition v_xyzt  := "xyzt".       (* 200B Edwards point (xyzt encoding) *)

(* ================================================================ *)
(* §2. lizard_inject as rust_cmd_ed                                  *)
(* ================================================================ *)

(** Three-call protocol body.

    Step 1: pack the 16B plaintext into a 32B buffer with derived padding
            via the [lizard_pack] leaf (typically a hash-based padding
            scheme that makes the Elligator2 input look random).
    Step 2: apply Elligator2 to obtain a Curve25519 (Montgomery) point,
            converted to Edwards (xyzt) form, via [elligator2_to_edwards].
    Step 3: serialise the Edwards point with [ristretto_encode] to obtain
            the final 32-byte Ristretto encoding. *)
Definition lizard_inject_rs : rust_cmd_ed :=
  REdLetZero v_buf32 (TBytes 32) (
  REdLetZero v_xyzt  (TBytes 200) (
  REdSeq (REdCall "lizard_pack"
            (LE_TBytes v_buf32 32) [LE_TBytes v_pt 16])
  (REdSeq (REdCall "elligator2_to_edwards"
            (LE_TBytes v_xyzt 200) [LE_TBytes v_buf32 32])
   (REdCall "ristretto_encode"
            (LE_TBytes v_out 32) [LE_TBytes v_xyzt 200])))).

Lemma borrow_ok_lizard_inject : borrow_ok_ed lizard_inject_rs = true.
Proof. vm_compute. reflexivity. Qed.

(** Well-formedness preservation theorem — the framework's baseline
    correctness statement, parallel to [ed25519_sign_rs_correct] /
    [xeddsa_sign_rs_correct]. *)
Theorem lizard_inject_rs_correct :
  forall callee_post callee_post_n function_table rs1 rs2,
    callee_post_well_formed callee_post ->
    callee_post_n_well_formed callee_post_n ->
    rs_well_formed rs1 ->
    rust_exec_ed callee_post callee_post_n function_table lizard_inject_rs rs1 rs2 ->
    rs_well_formed rs2.
Proof.
  intros callee_post callee_post_n function_table rs1 rs2 Hcp Hcpn Hwf Hexec.
  eapply rust_exec_ed_preserves_wf; eassumption.
Qed.
