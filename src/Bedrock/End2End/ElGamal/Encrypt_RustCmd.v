(** * ElGamal Encrypt as rust_cmd_ed
 *
 * ElGamal public-key encryption over the Ristretto255 prime-order group
 * with generator G.  Encrypt(pk, msg, r_random) returns the 64-byte
 * ciphertext C = C1 || C2 where:
 *
 *   C1 := r_random · G                     (ephemeral 32B Ristretto)
 *   shared := r_random · pk                (200B Edwards point)
 *   C2 := msg + shared                     (Edwards addition;
 *                                            msg is lifted to a
 *                                            Ristretto-encoded point)
 *
 * Protocol body (9 leaf calls):
 *
 *   1. ed25519_scalarmult_base   — C1_xyzt   ← r_random · G       (200B)
 *   2. ristretto_encode          — C1        ← compress(C1_xyzt)  (32B)
 *   3. ristretto_decode_or_fail  — pk_xyzt   ← decode(pk)         (200B)
 *   4. ed25519_scalarmult        — shared_xyzt ← r_random · pk_xyzt(200B)
 *   5. ristretto_decode_or_fail  — msg_xyzt  ← decode(msg)        (200B)
 *   6. ed25519_xyzt_add          — C2_xyzt   ← msg_xyzt + shared  (200B)
 *   7. ristretto_encode          — C2        ← compress(C2_xyzt)  (32B)
 *   8. memmove_first_32          — out[0..32]  ← C1
 *   9. memmove_second_32         — out[32..64] ← C2
 *
 * Sixth framework user after Ed25519 (sign / verify), XEdDSA, Lizard,
 * Pedersen, Schnorr.  First *encryption* protocol — different shape from
 * signing/commitments: it composes a decode/encode pair and packs the
 * 64-byte ciphertext from two 32-byte halves via [memmove_first_32] /
 * [memmove_second_32] (parallel to Schnorr verify's
 * [memmove_R_from_sig] / [memmove_S_from_sig]).
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
Definition v_pk     := "pk".         (* 32B Ristretto public key  *)
Definition v_msg    := "msg".        (* 32B Ristretto message point *)
Definition v_r_rand := "r_rand".     (* 32B random scalar         *)
Definition v_out    := "out".        (* 64B ciphertext output     *)

(** Internal slots (allocated via REdLetZero). *)
Definition v_C1_xyzt     := "C1_xyzt".      (* 200B r · G                *)
Definition v_C1          := "C1".           (* 32B compressed C1         *)
Definition v_pk_xyzt     := "pk_xyzt".      (* 200B decompressed pk      *)
Definition v_shared_xyzt := "shared_xyzt".  (* 200B r · pk               *)
Definition v_msg_xyzt    := "msg_xyzt".     (* 200B decompressed msg     *)
Definition v_C2_xyzt     := "C2_xyzt".      (* 200B msg + shared         *)
Definition v_C2          := "C2".           (* 32B compressed C2         *)

(* ================================================================ *)
(* §2. elgamal_encrypt as rust_cmd_ed                                *)
(* ================================================================ *)

Definition elgamal_encrypt_rs : rust_cmd_ed :=
  REdLetZero v_C1_xyzt     (TBytes 200) (
  REdLetZero v_C1          (TBytes 32) (
  REdLetZero v_pk_xyzt     (TBytes 200) (
  REdLetZero v_shared_xyzt (TBytes 200) (
  REdLetZero v_msg_xyzt    (TBytes 200) (
  REdLetZero v_C2_xyzt     (TBytes 200) (
  REdLetZero v_C2          (TBytes 32) (
  (* Step 1: C1_xyzt = r · G *)
  REdSeq (REdCall "ed25519_scalarmult_base"
            (LE_TBytes v_C1_xyzt 200)
            [LE_TBytes v_r_rand 32])
  (* Step 2: C1 = compress(C1_xyzt) *)
  (REdSeq (REdCall "ristretto_encode"
            (LE_TBytes v_C1 32)
            [LE_TBytes v_C1_xyzt 200])
  (* Step 3: pk_xyzt = decode(pk) *)
  (REdSeq (REdCall "ristretto_decode_or_fail"
            (LE_TBytes v_pk_xyzt 200)
            [LE_TBytes v_pk 32])
  (* Step 4: shared_xyzt = r · pk_xyzt *)
  (REdSeq (REdCall "ed25519_scalarmult"
            (LE_TBytes v_shared_xyzt 200)
            [LE_TBytes v_r_rand 32; LE_TBytes v_pk_xyzt 200])
  (* Step 5: msg_xyzt = decode(msg) *)
  (REdSeq (REdCall "ristretto_decode_or_fail"
            (LE_TBytes v_msg_xyzt 200)
            [LE_TBytes v_msg 32])
  (* Step 6: C2_xyzt = msg_xyzt + shared_xyzt *)
  (REdSeq (REdCall "ed25519_xyzt_add"
            (LE_TBytes v_C2_xyzt 200)
            [LE_TBytes v_msg_xyzt 200; LE_TBytes v_shared_xyzt 200])
  (* Step 7: C2 = compress(C2_xyzt) *)
  (REdSeq (REdCall "ristretto_encode"
            (LE_TBytes v_C2 32)
            [LE_TBytes v_C2_xyzt 200])
  (* Step 8: out[0..32] = C1 *)
  (REdSeq (REdCall "memmove_first_32"
            (LE_TBytes v_out 64)
            [LE_TBytes v_C1 32])
  (* Step 9: out[32..64] = C2 *)
   (REdCall "memmove_second_32"
            (LE_TBytes v_out 64)
            [LE_TBytes v_C2 32]))))))))))))))).

Lemma borrow_ok_elgamal_encrypt : borrow_ok_ed elgamal_encrypt_rs = true.
Proof. vm_compute. reflexivity. Qed.

(** Well-formedness preservation theorem — framework baseline,
    parallel to [pedersen_commit_rs_correct]. *)
Theorem elgamal_encrypt_rs_correct :
  forall callee_post callee_post_n function_table rs1 rs2,
    callee_post_well_formed callee_post ->
    callee_post_n_well_formed callee_post_n ->
    rs_well_formed rs1 ->
    rust_exec_ed callee_post callee_post_n function_table
                 elgamal_encrypt_rs rs1 rs2 ->
    rs_well_formed rs2.
Proof.
  intros callee_post callee_post_n function_table rs1 rs2 Hcp Hcpn Hwf Hexec.
  eapply rust_exec_ed_preserves_wf; eassumption.
Qed.
