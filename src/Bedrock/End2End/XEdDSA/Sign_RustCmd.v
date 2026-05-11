(** * XEdDSA Sign as rust_cmd_ed
 *
 * Signal's XEdDSA: sign an Ed25519-style signature using an X25519
 * (Montgomery) private key.  Reuses most Ed25519 leaves (scalar_reduce,
 * ed25519_scalarmult_base, scalar_muladd, ed25519_compress) plus two
 * new XEdDSA-specific leaves:
 *
 *   - [calculate_key_pair] : converts X25519 priv k to Edwards
 *     scalar [a] + compressed public [A] with sign-bit fixup.
 *   - [xed_hash_1]         : SHA-512 with XEdDSA's domain-separation
 *     prefix [0xFE || 0xFF^31].  The prefix is added internally by the
 *     leaf; the caller passes only the protocol payload [a || M || Z].
 *
 * Protocol:
 *   (a, A) = calculate_key_pair(k)              -- 32-byte a, 32-byte A
 *   r_full = xed_hash_1(a || M || Z)            -- domain-separated H1
 *   r      = scalar_reduce(r_full)
 *   R_xyzt = ed25519_scalarmult_base(r)
 *   R      = ed25519_compress(R_xyzt)
 *   k_full = sha512(R || A || M)
 *   k      = scalar_reduce(k_full)
 *   s      = scalar_muladd(r, k, a)
 *   sig    = R || s
 *
 * Mirrors the Ed25519 [Sign_Verify_RustCmd.v] structure: each
 * stackalloc becomes a [REdLetZero], each call becomes [REdCall] with
 * typed [located_ed] arguments, dynamic message-length values become
 * [REdLetU64] steps.
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
Definition v_xed_sig_out := "xed_sig_out".  (* 64-byte signature output *)
Definition v_xed_k       := "xed_k".        (* 32-byte X25519 private key *)
Definition v_xed_msg     := "xed_msg".      (* msg slot (≤4096 bytes) *)
Definition v_xed_msg_len := "xed_msg_len".  (* dynamic message length (TU64) *)
Definition v_xed_Z       := "xed_Z".        (* 64-byte randomness *)

(** Internal slots (allocated via REdLetZero). *)
Definition v_xed_a       := "xed_a".        (* 32-byte Edwards scalar (after sign-fix) *)
Definition v_xed_A       := "xed_A".        (* 32-byte compressed public key *)
Definition v_xed_nonce   := "xed_nonce".    (* a (32) || M (≤4096) || Z (64) *)
Definition v_xed_r_full  := "xed_r_full".   (* 64-byte nonce hash *)
Definition v_xed_r       := "xed_r".        (* 32-byte reduced r *)
Definition v_xed_R_xyzt  := "xed_R_xyzt".   (* 200-byte point R = rB *)
Definition v_xed_R_bytes := "xed_R_bytes".  (* 32-byte compressed R *)
Definition v_xed_chal    := "xed_chal".     (* R (32) || A (32) || M (≤4096) *)
Definition v_xed_k_full  := "xed_k_full".   (* 64-byte challenge hash *)
Definition v_xed_k_red   := "xed_k_red".    (* 32-byte reduced challenge *)

(** Slot widths.  Use the same upper bound for [msg] as Ed25519 (4096)
    so the nonce_buf width is [32 + 4096 + 64 = 4192] and chal_buf is
    [32 + 32 + 4096 = 4160], reusing the latter exactly from Ed25519. *)
Definition xed_nonce_width : nat := 4192.  (* 32 + 4096 + 64 *)
Definition xed_chal_width  : nat := 4160.  (* 32 + 32 + 4096 *)
Definition xed_msg_width   : nat := 4096.

(* ================================================================ *)
(* §2. xeddsa_sign as rust_cmd_ed                                    *)
(* ================================================================ *)

(** Structurally analogous to [ed25519_sign_rs], but:
    - Replaces steps 1–4 (sha512 seed → memmove_a → clamp → memmove_prefix)
      with a single [calculate_key_pair] leaf producing (a, A) directly.
      Since each [REdCall] writes one destination, we use TWO calls:
      [calculate_key_pair_a] writing [v_xed_a] and [calculate_key_pair_A]
      writing [v_xed_A] (both read [v_xed_k]).  This pattern mirrors how
      Ed25519 already does [memmove_a_from_h] + [memmove_prefix_from_h]
      against the same source.
    - Uses [xed_hash_1] (domain-separated) instead of [sha512_64] for
      the nonce step.  The leaf consumes [a || M || Z] and internally
      prepends [0xFE || 0xFF^31].
    - The nonce input includes 64 bytes of randomness [Z] (replacing
      Ed25519's [prefix]). *)
Definition xeddsa_sign_rs : rust_cmd_ed :=
  REdLetZero v_xed_a       (TBytes 32) (
  REdLetZero v_xed_A       (TBytes 32) (
  REdLetZero v_xed_nonce   (TBytes xed_nonce_width) (
  REdLetZero v_xed_r_full  (TBytes 64) (
  REdLetZero v_xed_r       (TBytes 32) (
  REdLetZero v_xed_R_xyzt  (TBytes 200) (
  REdLetZero v_xed_R_bytes (TBytes 32) (
  REdLetZero v_xed_chal    (TBytes xed_chal_width) (
  REdLetZero v_xed_k_full  (TBytes 64) (
  REdLetZero v_xed_k_red   (TBytes 32) (
  (* Step 1a: a = calculate_key_pair_a(k) — derived scalar with sign fixup *)
  REdSeq (REdCall "calculate_key_pair_a"
            (LE_TBytes v_xed_a 32)
            [LE_TBytes v_xed_k 32])
  (* Step 1b: A = calculate_key_pair_A(k) — compressed Edwards public *)
  (REdSeq (REdCall "calculate_key_pair_A"
            (LE_TBytes v_xed_A 32)
            [LE_TBytes v_xed_k 32])
  (* Step 2a: nonce_buf[0..32] = a *)
  (REdSeq (REdCall "memmove_xed_nonce_a"
            (LE_TBytes v_xed_nonce xed_nonce_width)
            [LE_TBytes v_xed_a 32])
  (* Step 2b: nonce_buf[32..32+msg_len] = msg *)
  (REdSeq (REdCall "memmove_xed_nonce_msg"
            (LE_TBytes v_xed_nonce xed_nonce_width)
            [LE_TBytes v_xed_msg xed_msg_width])
  (* Step 2c: nonce_buf[32+msg_len..96+msg_len] = Z *)
  (REdSeq (REdCall "memmove_xed_nonce_Z"
            (LE_TBytes v_xed_nonce xed_nonce_width)
            [LE_TBytes v_xed_Z 64])
  (* Step 3: dynamic nonce hash length = 32 + msg_len + 64 *)
  (REdLetU64 "xed_nonce_hash_len"
             (SAdd (SLit 96) (SVar v_xed_msg_len))
  (* Step 4: r_full = xed_hash_1(nonce_buf, nonce_hash_len)
     — leaf adds [0xFE || 0xFF^31] internally *)
  (REdSeq (REdCall "xed_hash_1"
            (LE_TBytes v_xed_r_full 64)
            [LE_TBytes v_xed_nonce xed_nonce_width;
             LE_TU64 "xed_nonce_hash_len"])
  (* Step 5: r = scalar_reduce(r_full) *)
  (REdSeq (REdCall "scalar_reduce"
            (LE_TBytes v_xed_r 32)
            [LE_TBytes v_xed_r_full 64])
  (* Step 6: R = r · B *)
  (REdSeq (REdCall "ed25519_scalarmult_base"
            (LE_TBytes v_xed_R_xyzt 200)
            [LE_TBytes v_xed_r 32])
  (REdSeq (REdCall "ed25519_compress"
            (LE_TBytes v_xed_R_bytes 32)
            [LE_TBytes v_xed_R_xyzt 200])
  (* Step 7a: chal_buf[0..32] = R *)
  (REdSeq (REdCall "memmove_xed_chal_R"
            (LE_TBytes v_xed_chal xed_chal_width)
            [LE_TBytes v_xed_R_bytes 32])
  (* Step 7b: chal_buf[32..64] = A *)
  (REdSeq (REdCall "memmove_xed_chal_A"
            (LE_TBytes v_xed_chal xed_chal_width)
            [LE_TBytes v_xed_A 32])
  (* Step 7c: chal_buf[64..64+msg_len] = msg *)
  (REdSeq (REdCall "memmove_xed_chal_M"
            (LE_TBytes v_xed_chal xed_chal_width)
            [LE_TBytes v_xed_msg xed_msg_width])
  (* Step 8: dynamic chal-hash length = 64 + msg_len *)
  (REdLetU64 "xed_chal_hash_len"
             (SAdd (SLit 64) (SVar v_xed_msg_len))
  (* Step 9: k_full = sha512(chal_buf, chal_hash_len) *)
  (REdSeq (REdCall "sha512_64"
            (LE_TBytes v_xed_k_full 64)
            [LE_TBytes v_xed_chal xed_chal_width;
             LE_TU64 "xed_chal_hash_len"])
  (* Step 10: k = scalar_reduce(k_full) *)
  (REdSeq (REdCall "scalar_reduce"
            (LE_TBytes v_xed_k_red 32)
            [LE_TBytes v_xed_k_full 64])
  (* Step 11: s = scalar_muladd(r, k, a) — writes first 32 bytes of sig_out *)
  (REdSeq (REdCall "scalar_muladd"
            (LE_TBytes v_xed_sig_out 64)
            [LE_TBytes v_xed_r 32;
             LE_TBytes v_xed_k_red 32;
             LE_TBytes v_xed_a 32])
  (* Step 12: sig_out[0..32] = R_bytes — final placement of R prefix *)
  (REdCall "memmove_xed_sig_R"
            (LE_TBytes v_xed_sig_out 64)
            [LE_TBytes v_xed_R_bytes 32]
  ))))))))))))))))))))))))))).

Lemma borrow_ok_xed_sign : borrow_ok_ed xeddsa_sign_rs = true.
Proof. vm_compute. reflexivity. Qed.

(** Well-formedness preservation theorem — the framework's baseline
    correctness statement, parallel to [ed25519_sign_rs_correct]. *)
Theorem xeddsa_sign_rs_correct :
  forall callee_post callee_post_n function_table rs1 rs2,
    callee_post_well_formed callee_post ->
    callee_post_n_well_formed callee_post_n ->
    rs_well_formed rs1 ->
    rust_exec_ed callee_post callee_post_n function_table xeddsa_sign_rs rs1 rs2 ->
    rs_well_formed rs2.
Proof.
  intros callee_post callee_post_n function_table rs1 rs2 Hcp Hcpn Hwf Hexec.
  eapply rust_exec_ed_preserves_wf; eassumption.
Qed.
