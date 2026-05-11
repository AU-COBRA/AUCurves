(** * Pedersen Commit as rust_cmd_ed
 *
 * Pedersen commitment over the Ristretto255 prime-order group:
 *
 *   commit(m, r) := m·G + r·H
 *
 * where G, H ∈ Ristretto255 are public generators and (m, r) are
 * 32-byte scalars (message and blinding factor).  The output is a
 * 32-byte Ristretto encoding.
 *
 * Protocol body (4 leaf calls):
 *
 *   1. ed25519_scalarmult_base     — mG ← m·G  (200B Edwards point)
 *   2. ristretto_h_scalarmult      — rH ← r·H  (200B Edwards point)
 *   3. ed25519_xyzt_add            — sum ← mG + rH  (200B Edwards point)
 *   4. ristretto_encode            — out ← sum  (32B Ristretto encoding)
 *
 * Fourth framework user after Ed25519 (sign / verify) and Lizard
 * (inject / extract).  Demonstrates that the rust_cmd_ed framework
 * is composable: every leaf except [ristretto_h_scalarmult] is
 * reused verbatim from Ed25519 / Lizard, leaving exactly one new
 * Parameter to introduce here.
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
Definition v_m   := "m".            (* 32B scalar (message) *)
Definition v_r   := "r".            (* 32B scalar (blinding) *)
Definition v_out := "out".          (* 32B Ristretto commitment *)

(** Internal slots (allocated via REdLetZero). *)
Definition v_mG  := "mG".           (* 200B Edwards point m·G *)
Definition v_rH  := "rH".           (* 200B Edwards point r·H *)
Definition v_sum := "sum".          (* 200B Edwards point sum *)

(* ================================================================ *)
(* §2. pedersen_commit as rust_cmd_ed                                *)
(* ================================================================ *)

(** Four-call protocol body.

    Step 1: m·G via [ed25519_scalarmult_base].
    Step 2: r·H via [ristretto_h_scalarmult] (the only new leaf —
            structurally identical to scalarmult_base but uses the H
            generator instead of the standard G).
    Step 3: sum the two Edwards points via [ed25519_xyzt_add].
    Step 4: encode the sum as 32B Ristretto via [ristretto_encode]. *)
Definition pedersen_commit_rs : rust_cmd_ed :=
  REdLetZero v_mG  (TBytes 200) (
  REdLetZero v_rH  (TBytes 200) (
  REdLetZero v_sum (TBytes 200) (
  REdSeq (REdCall "ed25519_scalarmult_base"
            (LE_TBytes v_mG 200) [LE_TBytes v_m 32])
  (REdSeq (REdCall "ristretto_h_scalarmult"
            (LE_TBytes v_rH 200) [LE_TBytes v_r 32])
  (REdSeq (REdCall "ed25519_xyzt_add"
            (LE_TBytes v_sum 200)
            [LE_TBytes v_mG 200; LE_TBytes v_rH 200])
   (REdCall "ristretto_encode"
            (LE_TBytes v_out 32) [LE_TBytes v_sum 200])))))).

Lemma borrow_ok_pedersen_commit : borrow_ok_ed pedersen_commit_rs = true.
Proof. vm_compute. reflexivity. Qed.

(** Well-formedness preservation theorem — the framework's baseline
    correctness statement, parallel to [ed25519_sign_rs_correct] /
    [lizard_inject_rs_correct]. *)
Theorem pedersen_commit_rs_correct :
  forall callee_post callee_post_n function_table rs1 rs2,
    callee_post_well_formed callee_post ->
    callee_post_n_well_formed callee_post_n ->
    rs_well_formed rs1 ->
    rust_exec_ed callee_post callee_post_n function_table pedersen_commit_rs rs1 rs2 ->
    rs_well_formed rs2.
Proof.
  intros callee_post callee_post_n function_table rs1 rs2 Hcp Hcpn Hwf Hexec.
  eapply rust_exec_ed_preserves_wf; eassumption.
Qed.
