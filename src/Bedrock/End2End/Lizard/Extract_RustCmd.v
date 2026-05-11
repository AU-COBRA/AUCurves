(** * Lizard Extract as rust_cmd_ed
 *
 * Inverse of [lizard_inject_rs]: given a 32B Ristretto encoding, recover
 * the 16B plaintext that was injected.  Used in Signal's prekey
 * distribution / sealed-sender unwrap.
 *
 * Canonical Lizard extract (32B Ristretto → 16B plaintext):
 *
 *   1. ristretto_decode_or_fail: deserialise the 32B Ristretto bytes
 *      into an Edwards (xyzt) point (200 bytes).  On invalid input
 *      the leaf is modelled as identity-with-sentinel (the recovered
 *      "point" is a recognisable failure marker — downstream callers
 *      handle the option type at the FFI boundary; this matches how
 *      Signal's reference implementation handles invalid encodings).
 *   2. edwards_to_elligator2: convert the Edwards point back to a
 *      Curve25519 (Montgomery) point and apply the Elligator2 inverse,
 *      recovering the 32B field element representation.
 *   3. lizard_unpack: extract the middle 16 bytes (the plaintext) from
 *      the 32B buffer.
 *
 * Mirrors [Inject_RustCmd.v] structurally — same 3-call shape with 2
 * intermediate stack-allocated buffers, walked in reverse order
 * (xyzt → buf32 → pt_out).
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
Definition v_rist   := "rist".      (* 32B Ristretto input *)
Definition v_pt_out := "pt_out".    (* 16B plaintext output *)

(** Internal slots (allocated via REdLetZero). *)
Definition v_xyzt_ex  := "xyzt_ex".   (* 200B Edwards point (xyzt encoding) *)
Definition v_buf32_ex := "buf32_ex".  (* 32B intermediate (padded plaintext) *)

(* ================================================================ *)
(* §2. lizard_extract as rust_cmd_ed                                 *)
(* ================================================================ *)

(** Three-call protocol body.

    Step 1: deserialise the 32B Ristretto encoding into an Edwards
            (xyzt) point via [ristretto_decode_or_fail].
    Step 2: invert Elligator2 to obtain the 32B padded buffer via
            [edwards_to_elligator2].
    Step 3: extract the middle 16 bytes (plaintext) via [lizard_unpack]. *)
Definition lizard_extract_rs : rust_cmd_ed :=
  REdLetZero v_xyzt_ex  (TBytes 200) (
  REdLetZero v_buf32_ex (TBytes 32) (
  REdSeq (REdCall "ristretto_decode_or_fail"
            (LE_TBytes v_xyzt_ex 200) [LE_TBytes v_rist 32])
  (REdSeq (REdCall "edwards_to_elligator2"
            (LE_TBytes v_buf32_ex 32) [LE_TBytes v_xyzt_ex 200])
   (REdCall "lizard_unpack"
            (LE_TBytes v_pt_out 16) [LE_TBytes v_buf32_ex 32])))).

Lemma borrow_ok_lizard_extract : borrow_ok_ed lizard_extract_rs = true.
Proof. vm_compute. reflexivity. Qed.

(** Well-formedness preservation theorem — framework baseline. *)
Theorem lizard_extract_rs_correct :
  forall callee_post callee_post_n function_table rs1 rs2,
    callee_post_well_formed callee_post ->
    callee_post_n_well_formed callee_post_n ->
    rs_well_formed rs1 ->
    rust_exec_ed callee_post callee_post_n function_table lizard_extract_rs rs1 rs2 ->
    rs_well_formed rs2.
Proof.
  intros callee_post callee_post_n function_table rs1 rs2 Hcp Hcpn Hwf Hexec.
  eapply rust_exec_ed_preserves_wf; eassumption.
Qed.
