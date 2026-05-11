(** * Pedersen Open as rust_cmd_ed
 *
 * Pedersen opening (verification of a commitment) over the Ristretto255
 * prime-order group:
 *
 *   open(c, m, r) := bytes_equal(c, m·G + r·H)
 *
 * where c is a 32-byte candidate Ristretto commitment, (m, r) are
 * 32-byte scalars, G, H are the public Pedersen generators.  The output
 * is a 1-byte boolean (1 = open succeeded, 0 = mismatch).
 *
 * Protocol body (5 leaf calls):
 *
 *   1. ed25519_scalarmult_base     — mG ← m·G  (200B Edwards point)
 *   2. ristretto_h_scalarmult      — rH ← r·H  (200B Edwards point)
 *   3. ed25519_xyzt_add            — sum ← mG + rH  (200B Edwards point)
 *   4. ristretto_encode            — c_check ← sum  (32B Ristretto encoding)
 *   5. bytes_equal_32              — result ← bytes_equal(c, c_check)  (1B)
 *
 * Mirrors [Commit_RustCmd.v] structurally — same 4-call commit prefix,
 * plus one terminating constant-time comparison against the candidate.
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
Definition v_c_open  := "c_open".       (* 32B candidate commitment input *)
Definition v_m_open  := "m_open".       (* 32B scalar (message) *)
Definition v_r_open  := "r_open".       (* 32B scalar (blinding) *)
Definition v_result_open := "result_open". (* 1B boolean output *)

(** Internal slots (allocated via REdLetZero). *)
Definition v_mG_o    := "mG_o".         (* 200B Edwards point m·G *)
Definition v_rH_o    := "rH_o".         (* 200B Edwards point r·H *)
Definition v_sum_o   := "sum_o".        (* 200B Edwards point sum *)
Definition v_c_check := "c_check".      (* 32B Ristretto re-encoding *)

(* ================================================================ *)
(* §2. pedersen_open as rust_cmd_ed                                  *)
(* ================================================================ *)

(** Five-call protocol body.

    Step 1: m·G via [ed25519_scalarmult_base].
    Step 2: r·H via [ristretto_h_scalarmult].
    Step 3: sum = m·G + r·H via [ed25519_xyzt_add].
    Step 4: 32B Ristretto re-encoding via [ristretto_encode].
    Step 5: constant-time comparison against the candidate
            commitment via [bytes_equal_32].  Result lands in the 1B
            output slot. *)
Definition pedersen_open_rs : rust_cmd_ed :=
  REdLetZero v_mG_o    (TBytes 200) (
  REdLetZero v_rH_o    (TBytes 200) (
  REdLetZero v_sum_o   (TBytes 200) (
  REdLetZero v_c_check (TBytes 32) (
  REdSeq (REdCall "ed25519_scalarmult_base"
            (LE_TBytes v_mG_o 200) [LE_TBytes v_m_open 32])
  (REdSeq (REdCall "ristretto_h_scalarmult"
            (LE_TBytes v_rH_o 200) [LE_TBytes v_r_open 32])
  (REdSeq (REdCall "ed25519_xyzt_add"
            (LE_TBytes v_sum_o 200)
            [LE_TBytes v_mG_o 200; LE_TBytes v_rH_o 200])
  (REdSeq (REdCall "ristretto_encode"
            (LE_TBytes v_c_check 32) [LE_TBytes v_sum_o 200])
   (REdCall "bytes_equal_32"
            (LE_TBytes v_result_open 1)
            [LE_TBytes v_c_open 32; LE_TBytes v_c_check 32])))))))).

Lemma borrow_ok_pedersen_open : borrow_ok_ed pedersen_open_rs = true.
Proof. vm_compute. reflexivity. Qed.

(** Well-formedness preservation theorem — framework baseline. *)
Theorem pedersen_open_rs_correct :
  forall callee_post callee_post_n function_table rs1 rs2,
    callee_post_well_formed callee_post ->
    callee_post_n_well_formed callee_post_n ->
    rs_well_formed rs1 ->
    rust_exec_ed callee_post callee_post_n function_table pedersen_open_rs rs1 rs2 ->
    rs_well_formed rs2.
Proof.
  intros callee_post callee_post_n function_table rs1 rs2 Hcp Hcpn Hwf Hexec.
  eapply rust_exec_ed_preserves_wf; eassumption.
Qed.
