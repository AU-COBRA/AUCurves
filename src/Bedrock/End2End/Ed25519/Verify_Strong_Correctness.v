(** * Verify_Strong_Correctness — Gap-#3 strong correctness for ed25519_verify_rs.
 *
 * Mirrors [Sign_Strong_Correctness.v] for the verify protocol.
 *
 * Under [strong_callee_post_verify] (each leaf returns its Gallina
 * spec AND frames all other slots), the v_result slot after execution
 * equals [ed25519_verify_gallina sig_in pub msg], a 1-byte accept/reject
 * indicator computed from the leaf specs.
 *
 * Structure:
 *   §1  Imports + reuse of slot_holds / frames_except infrastructure
 *       from [Sign_Strong_Correctness.v].
 *   §2  Additional leaf Gallina specs for verify-only leaves
 *       (decompress_R/A, scalarmult, xyzt_add, scalar_lt_L,
 *        bytes_equal_32, memmove_R_from_sig).  sha512_full_spec,
 *        scalar_reduce_spec, ed25519_scalarmult_base_spec,
 *        ed25519_compress_spec, memmove_chal_* are reused from
 *        [Sign_Strong_Correctness] / [RemainingBridges].
 *   §3  [ed25519_verify_gallina]: top-level reference (1-byte result).
 *   §4  [strong_callee_post_verify]: per-call obligation.
 *   §5  Strong correctness theorem.  Qed.
 *
 * Status: §1-§5 closed.  ed25519_verify_strong_correct is Qed-clean.
 *
 * Verify's body in [Sign_Verify_RustCmd.v] is straight-line (no
 * [REdIfNz] branches); the protocol writes the canonical-S check
 * to v_result, then unconditionally overwrites it with the
 * bytes_equal_32 result of compress(R + h·A) against R-from-sig_in.
 * The functional postcondition therefore matches bytes_equal_32 only.
 *
 * Bug-B fix (2026-05-11): the [sha512_64] call now hashes the
 * canonical RFC 8032 input [R || A || msg] from a fresh [chal_buf_v]
 * slot, not [sig_in].  Body adds three [memmove_chal_*] callees
 * (reused from sign) + a [memmove_R_from_sig] that extracts R bytes
 * from [sig_in].  The Gallina reference [ed25519_verify_gallina]
 * matches accordingly.  Strong-callee-post mirrors Bug-A's 2-arg
 * [sha512_64] arm + adds memmove arms.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import Strings.Byte.
From Stdlib Require Import micromega.Lia.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.RemainingBridges.
Require Import Bedrock.End2End.Ed25519.SHA512Bridge.
Require Import Bedrock.End2End.Ed25519.Sign_Verify_RustCmd.
Require Import Bedrock.End2End.Ed25519.Sign_Strong_Correctness.
Require Import Bedrock.End2End.Ed25519.XyztAddVerified.
Require Import Bedrock.End2End.Ed25519.ScalarmultVerified.
Require Import Bedrock.End2End.Ed25519.DecompressVerified.
Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* §2. Additional Gallina specs for verify-only leaves              *)
(* ================================================================ *)

(** [ed25519_decompress_R_spec sig_in] : 200-byte xyzt representation
    of the decompressed R-point parsed from the first 32 bytes of [sig_in].
    Output is always 200 bytes; an invalid R is modeled as a designated
    "bad" point in the xyzt encoding (the protocol does not branch). *)
(** [ed25519_decompress_R_spec], [ed25519_decompress_A_spec],
    [ed25519_scalarmult_spec], [ed25519_xyzt_add_spec] are now
    Definitions (no longer Parameters), imported from
    [DecompressVerified.v], [ScalarmultVerified.v], and
    [XyztAddVerified.v].  Length lemmas are imported under the same
    names from those files. *)

(** [scalar_lt_L_spec sig_in] : 1-byte canonical-S check (1 = ok, 0 = bad).
    The protocol writes this to v_result, then *overwrites* it with the
    bytes_equal_32 result.  Hence this spec function is never observed in
    the final postcondition — declared only for completeness.

    Concrete Definition (NOT an axiom): tests whether the little-endian
    decoding of the byte list is strictly less than [L_curve_order].
    Reduces by [vm_compute] on any concrete input. *)
Definition scalar_lt_L_spec (bs : list Byte.byte) : list Byte.byte :=
  if (LittleEndianList.le_combine bs <? L_curve_order)%Z
  then [Byte.x01] else [Byte.x00].

Lemma scalar_lt_L_spec_len :
  forall sig_in, length (scalar_lt_L_spec sig_in) = 1%nat.
Proof.
  intros sig_in. cbv [scalar_lt_L_spec].
  destruct (LittleEndianList.le_combine sig_in <? L_curve_order)%Z; reflexivity.
Qed.

(** [bytes_equal_32_spec a b] : 1-byte equality result.
    Models comparison of two byte lists (1 = equal, 0 = unequal).
    Concrete Definition (NOT an axiom) via [list_eq_dec byte_eq_dec].
    The Gallina spec is not required to be constant-time; only the
    eventual rust_cmd_ed body emitted to Rust needs CT. *)
Definition bytes_equal_32_spec (a b : list Byte.byte) : list Byte.byte :=
  if List.list_eq_dec byte_eq_dec a b
  then [Byte.x01] else [Byte.x00].

Lemma bytes_equal_32_spec_len :
  forall a b, length (bytes_equal_32_spec a b) = 1%nat.
Proof.
  intros a b. cbv [bytes_equal_32_spec].
  destruct (List.list_eq_dec byte_eq_dec a b); reflexivity.
Qed.

(** [memmove_R_from_sig_spec sig_in] : extracts the first 32 bytes of
    a 64-byte signature (the R component) into a fresh 32-byte slot.
    Models the Rust leaf [memmove_R_from_sig(R: *mut u8, sig: *const u8)]
    declared in [RustCmdToRust.rs_prelude]. *)
Definition memmove_R_from_sig_spec (sig_in : list Byte.byte) : list Byte.byte :=
  firstn 32 sig_in.

(** [memmove_S_from_sig_spec sig_in] : extracts bytes 32..64 of a
    64-byte signature (the S scalar component) into a fresh 32-byte slot.
    Models the Rust leaf [memmove_S_from_sig(S: *mut u8, sig: *const u8)]
    declared in [RustCmdToRust.rs_prelude].  Bug-C fix: passed as the
    32-byte scalar argument to [ed25519_scalarmult_base]. *)
Definition memmove_S_from_sig_spec (sig_in : list Byte.byte) : list Byte.byte :=
  skipn 32 sig_in.

(* ================================================================ *)
(* §3. Gallina reference                                              *)
(* ================================================================ *)

(** Top-level verify result: 1 byte.  Computed by the leaf-spec
    composition that mirrors the protocol's straight-line flow.

    Note: the protocol's scalar_lt_L write to v_result is shadowed by
    the final bytes_equal_32 write, so the result depends only on the
    bytes_equal_32 of compress(R + h·A) against the R portion of sig_in.

    Bug-B fix: the sha512_64 input is the canonical RFC 8032
    challenge buffer [R || A || firstn msg_len msg], built by the
    [memmove_chal_*] leaves (reused from sign).  Like
    [ed25519_sign_gallina_lifted], we parameterize on the buffer
    initial bytes [chal_init] and the dynamic hash length to keep the
    proof body precise — the clean form follows under the standard
    buffer lengths.

    The "lifted" form mirrors the protocol's intermediate firstn /
    skipn fragments introduced by the memmove leaves' specs (where
    each memmove writes a prefix of a larger buffer). *)
Definition ed25519_verify_gallina_lifted
    (sig_in pub msg : list Byte.byte)
    (chal_hash_len : nat)
    (chal_init : list Byte.byte)
  : list Byte.byte :=
  let R_xyzt    := ed25519_decompress_R_spec sig_in in
  let A_xyzt    := ed25519_decompress_A_spec pub in
  let R_bytes   := memmove_R_from_sig_spec sig_in in
  let chal_C5   := (R_bytes ++ skipn (length R_bytes) chal_init)%list in
  let chal_C6   := (firstn 32 chal_C5 ++ pub ++
                    skipn (32 + length pub) chal_C5)%list in
  let chal_C7   := (firstn 64 chal_C6 ++ msg)%list in
  let h_full    := sha512_full_spec (firstn chal_hash_len chal_C7) in
  let h         := scalar_reduce_spec h_full in
  let sB        := ed25519_scalarmult_base_spec (memmove_S_from_sig_spec sig_in) in
  let hA        := ed25519_scalarmult_spec h A_xyzt in
  let RcheckA   := ed25519_xyzt_add_spec R_xyzt hA in
  let check_b   := ed25519_compress_spec RcheckA in
  bytes_equal_32_spec sig_in check_b.

(** Clean reference: under conventional buffer lengths
    (chal_init: 4160 bytes, chal_hash_len = 64 + msg_len), the lifted
    gallina collapses to a direct [R || A || firstn msg_len msg] hash.
    Stated as a separate lemma; the strong correctness theorem
    returns the lifted form (existentially quantified over
    chal_init / chal_hash_len) to keep the proof straight-line. *)
Definition ed25519_verify_gallina
    (sig_in pub msg : list Byte.byte) : list Byte.byte :=
  let R_xyzt    := ed25519_decompress_R_spec sig_in in
  let A_xyzt    := ed25519_decompress_A_spec pub in
  let R_bytes   := memmove_R_from_sig_spec sig_in in
  let chal      := (R_bytes ++ pub ++ msg)%list in
  let h_full    := sha512_full_spec chal in
  let h         := scalar_reduce_spec h_full in
  let sB        := ed25519_scalarmult_base_spec (memmove_S_from_sig_spec sig_in) in
  let hA        := ed25519_scalarmult_spec h A_xyzt in
  let RcheckA   := ed25519_xyzt_add_spec R_xyzt hA in
  let check_b   := ed25519_compress_spec RcheckA in
  bytes_equal_32_spec sig_in check_b.

(* Bug-C fix (2026-05-11): the protocol now extracts the 32-byte scalar
   S = sig_in[32..64] via [memmove_S_from_sig] before passing it to
   [ed25519_scalarmult_base].  The Gallina reference threads
   [memmove_S_from_sig_spec sig_in] into [ed25519_scalarmult_base_spec]. *)

(* ================================================================ *)
(* §4. Strong callee_post predicate for verify                       *)
(* ================================================================ *)

(** Scalar-side frame conjunct: [v_msg_len] is read by the
    [REdLetU64 "verify_chal_len" ...] step that computes the dynamic
    chal hash length; no callee in verify mutates it.  The conjunct
    asserts [rs_get_scalar_ed rs1 v_msg_len = rs_get_scalar_ed rs2
    v_msg_len] per call so the proof can thread the precondition
    [rs_get_scalar_ed rs1 v_msg_len = Some msg_len] across all
    pre-LetU64 call sites. *)
Definition strong_callee_post_verify
           (fname : String.string)
           (args : list located_ed)
           (dst : located_ed)
           (rs1 rs2 : rust_state_ed) : Prop :=
  frames_except rs1 rs2 dst.(loc_var) /\
  (rs_get_scalar_ed rs1 v_msg_len = rs_get_scalar_ed rs2 v_msg_len) /\
  match fname, args with
  | "sha512_64", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (sha512_full_spec src_bs)
  | "sha512_64", [src; len_arg] =>
      (* Bug-B fix: dynamic-length sha512_64.  The leaf hashes
         [firstn len src_bs] where [len] is the value of the scalar
         slot [len_arg.(loc_var)]. *)
      exists src_bs len,
        slot_holds rs1 src.(loc_var) src_bs /\
        rs_get_scalar_ed rs1 len_arg.(loc_var) = Some len /\
        slot_holds rs2 dst.(loc_var)
          (sha512_full_spec (firstn (Z.to_nat len) src_bs))
  | "scalar_reduce", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (scalar_reduce_spec src_bs)
  | "ed25519_scalarmult_base", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (ed25519_scalarmult_base_spec src_bs)
  | "ed25519_compress", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (ed25519_compress_spec src_bs)
  | "ed25519_decompress_R", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (ed25519_decompress_R_spec src_bs)
  | "ed25519_decompress_A", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (ed25519_decompress_A_spec src_bs)
  | "ed25519_scalarmult", [h; A] =>
      exists h_bs A_bs,
        slot_holds rs1 h.(loc_var) h_bs /\
        slot_holds rs1 A.(loc_var) A_bs /\
        slot_holds rs2 dst.(loc_var) (ed25519_scalarmult_spec h_bs A_bs)
  | "ed25519_xyzt_add", [P; Q] =>
      exists P_bs Q_bs,
        slot_holds rs1 P.(loc_var) P_bs /\
        slot_holds rs1 Q.(loc_var) Q_bs /\
        slot_holds rs2 dst.(loc_var) (ed25519_xyzt_add_spec P_bs Q_bs)
  | "scalar_lt_L", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (scalar_lt_L_spec src_bs)
  | "bytes_equal_32", [a; b] =>
      exists a_bs b_bs,
        slot_holds rs1 a.(loc_var) a_bs /\
        slot_holds rs1 b.(loc_var) b_bs /\
        slot_holds rs2 dst.(loc_var) (bytes_equal_32_spec a_bs b_bs)
  (* Bug-B fix: extracts R from sig_in into a 32-byte slot.  Reuses
     the sign-side memmove_chal_* leaves for the rest of the chal
     buffer build, so those arms must agree with [Sign_Strong_Correctness]
     verbatim. *)
  | "memmove_R_from_sig", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (memmove_R_from_sig_spec src_bs)
  | "memmove_S_from_sig", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (memmove_S_from_sig_spec src_bs)
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
  | _, _ => True
  end.

(** Frame lemma — Qed.  [strong_callee_post_verify] preserves all slots
    except dest. *)
Lemma strong_callee_post_verify_frame_other_slots :
  forall fname args dst rs1 rs2 x,
    strong_callee_post_verify fname args dst rs1 rs2 ->
    x <> dst.(loc_var) ->
    rs_get_tower_ed rs1 x = rs_get_tower_ed rs2 x.
Proof.
  intros fname args dst rs1 rs2 x [Hframe _] Hne.
  apply (Hframe x Hne).
Qed.

(** Helpers reused by the strong-correctness proof: tower-set update of
    slot [x] preserves [slot_holds] for a different slot [y]; scalar
    lookups are unaffected by tower updates; scalar updates of slot [x]
    preserve scalar lookups for a different slot [y].  These are
    imported from [Sign_Strong_Correctness] via the [Require Import]
    line at the top of this file. *)

(* ================================================================ *)
(* §4b. Local tactics                                                *)
(* ================================================================ *)

(** [neq_var_v] proves [v_X <> v_Y] for the verify-side v_* names.
    Includes both sign-side names (so we can compose with imported
    helpers if needed) and verify-side names. *)
Ltac neq_var_v :=
  cbn [LE_TBytes loc_var];
  cbv [v_sig_in v_pub v_msg v_sig_out
       v_result v_R_xyzt_v v_A_xyzt_v v_h_v v_h_red
       v_sB v_hA v_RcheckA v_check_bytes
       v_R_bytes_v v_chal_buf_v v_S_bytes
       (* sign-side too, harmless *)
       v_h_full v_a_slot v_prefix v_A_xyzt v_A_bytes v_nonce_buf
       v_r_full v_r_slot v_R_xyzt v_R_bytes v_chal_buf
       v_k_full v_k_slot v_seed v_msg_len];
  discriminate.

Ltac peel_call_seq_v H Hframe Hres :=
  let Hcall := fresh "Hcall" in
  let Hrest := fresh "Hrest" in
  let Hsc := fresh "Hsc_msg" in
  inversion H; subst; clear H;
  match goal with
  | Hc : rust_exec_ed _ _ _ (REdCall _ _ _) _ _,
    Hr : rust_exec_ed _ _ _ _ _ _ |- _ =>
      rename Hc into Hcall; rename Hr into Hrest
  end;
  let Hcp := fresh "Hcp" in
  inversion Hcall; subst; clear Hcall;
  match goal with
  | Hc : strong_callee_post_verify _ _ _ _ _ |- _ =>
      rename Hc into Hcp
  end;
  destruct Hcp as [Hframe [Hsc Hres]];
  match goal with
  | Hh : rs_get_scalar_ed _ v_msg_len = Some _ |- _ =>
      rewrite Hsc in Hh; clear Hsc
  end;
  rename Hrest into H.

Ltac peel_last_call_v H Hframe Hres :=
  let Hsc := fresh "Hsc_msg" in
  inversion H; subst; clear H;
  match goal with
  | Hc : strong_callee_post_verify _ _ _ _ _ |- _ =>
      destruct Hc as [Hframe [Hsc Hres]]; clear Hsc
  end.

(* ================================================================ *)
(* §5. Strong correctness theorem                                    *)
(* ================================================================ *)

(** **Main theorem.**  Under [strong_callee_post_verify], the
    ed25519_verify_rs protocol produces a v_result slot equal to
    [ed25519_verify_gallina sig_in pub msg].

    Hypotheses:
    - lengths: |sig_in|=64, |pub|=32, |msg|=4096 (RFC 8032);
    - the sig_in/pub/msg/sig_out slots in rs1 are loaded with the
      named bytes (msg + sig_out are unused by verify; threaded for
      symmetry with sign);
    - rust_exec_ed terminates under strong_callee_post_verify.
*)
Theorem ed25519_verify_strong_correct :
  forall (callee_post_n :
            String.string -> list located_ed -> list located_ed ->
            rust_state_ed -> rust_state_ed -> Prop)
         (function_table : function_table_ed)
         (rs1 rs2 : rust_state_ed)
         (sig_in pub msg sig_out_init : list Byte.byte)
         (msg_len : Z),
    length sig_in = 64%nat ->
    length pub    = 32%nat ->
    length msg    = 4096%nat ->
    (0 <= msg_len <= 4096)%Z ->
    slot_holds rs1 v_sig_in  sig_in ->
    slot_holds rs1 v_pub     pub ->
    slot_holds rs1 v_msg     msg ->
    slot_holds rs1 v_sig_out sig_out_init ->
    rs_get_scalar_ed rs1 v_msg_len = Some msg_len ->
    rust_exec_ed strong_callee_post_verify callee_post_n function_table
                 ed25519_verify_rs rs1 rs2 ->
    exists chal_hash_len chal_init,
      slot_holds rs2 v_result
        (ed25519_verify_gallina_lifted sig_in pub msg
           chal_hash_len chal_init).
Proof.
  intros callee_post_n function_table rs1 rs2
         sig_in pub msg sig_out_init msg_len
         Hsig_len Hpub_len Hmsg_len Hmsg_len_bound
         Hsig_in Hpub Hmsg Hsig_out Hmsg_len_get Hexec.
  unfold ed25519_verify_rs in Hexec.

  (* Stage A: peel 11 REdLetZero allocations. *)
  repeat (match goal with
          | H : rust_exec_ed _ _ _ (REdLetZero _ _ _) _ _ |- _ =>
              inversion H; subst; clear H
          end).

  (* Propagate sig_in/pub/msg/sig_out/msg_len across the 11 fresh slot
     allocations.  Tower lookups via [slot_holds_set_tower_other];
     scalar lookup via [scalar_get_set_tower] (which holds
     unconditionally — tower and scalar envs are stored separately). *)
  match goal with
  | H : rust_exec_ed _ _ _ _ ?rs_alloc _ |- _ =>
      assert (Hsig_in_alloc : slot_holds rs_alloc v_sig_in sig_in) by
        (repeat (apply slot_holds_set_tower_other; [discriminate|]); exact Hsig_in);
      assert (Hpub_alloc : slot_holds rs_alloc v_pub pub) by
        (repeat (apply slot_holds_set_tower_other; [discriminate|]); exact Hpub);
      assert (Hmsg_alloc : slot_holds rs_alloc v_msg msg) by
        (repeat (apply slot_holds_set_tower_other; [discriminate|]); exact Hmsg);
      assert (Hsig_out_alloc : slot_holds rs_alloc v_sig_out sig_out_init) by
        (repeat (apply slot_holds_set_tower_other; [discriminate|]); exact Hsig_out);
      assert (Hmsg_len_alloc : rs_get_scalar_ed rs_alloc v_msg_len = Some msg_len) by
        (repeat rewrite scalar_get_set_tower; exact Hmsg_len_get);
      rename H into Hexec
  end.
  clear Hsig_in Hpub Hmsg Hsig_out Hmsg_len_get.

  (* === Stage B: 14 call inversions + 1 REdLetU64 === *)

  (* V1: scalar_lt_L (v_result ← sig_in) *)
  peel_call_seq_v Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt1]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hsig_in_alloc) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_v.
  clear Hframe Hsrc.

  (* V2: ed25519_decompress_R (R_xyzt_v ← sig_in) *)
  peel_call_seq_v Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt2]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hsig_in_alloc) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_v.
  clear Hframe Hsrc.

  (* V3: ed25519_decompress_A (A_xyzt_v ← pub) *)
  peel_call_seq_v Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt3]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hpub_alloc) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_v.
  clear Hframe Hsrc.

  (* V4 (Bug-B): memmove_R_from_sig (R_bytes_v ← sig_in) *)
  peel_call_seq_v Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt4]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hsig_in_alloc) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_v.
  clear Hframe Hsrc.

  (* V5 (Bug-B): memmove_chal_R (chal_buf_v ← R_bytes_v) *)
  peel_call_seq_v Hexec Hframe Hres.
  destruct Hres as [src_bs [dst_bs5 [Hsrc [Hdst Htgt5]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt4) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_v.
  clear Hframe Hsrc Hdst.

  (* V6 (Bug-B): memmove_chal_A (chal_buf_v ← pub) *)
  peel_call_seq_v Hexec Hframe Hres.
  destruct Hres as [src_bs [dst_bs [Hsrc [Hdst Htgt6]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hpub_alloc) as Heq; subst src_bs.
  pose proof (slot_holds_inj _ _ _ _ Hdst Htgt5) as Heq2; subst dst_bs.
  frame_through_call_with Hframe neq_var_v.
  clear Hframe Hsrc Hdst Htgt5.

  (* V7 (Bug-B): memmove_chal_M (chal_buf_v ← msg) *)
  peel_call_seq_v Hexec Hframe Hres.
  destruct Hres as [src_bs [dst_bs [Hsrc [Hdst Htgt7]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hmsg_alloc) as Heq; subst src_bs.
  pose proof (slot_holds_inj _ _ _ _ Hdst Htgt6) as Heq2; subst dst_bs.
  frame_through_call_with Hframe neq_var_v.
  clear Hframe Hsrc Hdst Htgt6.

  (* Bug-B fix: peel the [REdLetU64 "verify_chal_len" ...] step that
     computes the dynamic message-length argument [64 + msg_len]. *)
  inversion Hexec; subst; clear Hexec.
  match goal with
  | Hev : eval_sexpr_ed _ _ = Some _ |- _ =>
      rename Hev into Heval_cl
  end.
  match goal with
  | Hr : rust_exec_ed _ _ _ _ _ _ |- _ =>
      rename Hr into Hexec
  end.
  cbn [eval_sexpr_ed] in Heval_cl.
  rewrite Hmsg_len_alloc in Heval_cl.
  inversion Heval_cl as [Hv_cl].
  assert (Hmsg_len_set_cl : v_msg_len <> "verify_chal_len")
    by (cbv [v_msg_len]; intro Hcontra; discriminate Hcontra).
  match goal with
  | _ : context [rs_set_scalar_ed ?rs0 "verify_chal_len" ?v0] |- _ =>
      pose proof (slot_holds_scalar_set_other rs0 "verify_chal_len" v0 _ _
                    Hmsg_len_set_cl Hmsg_len_alloc) as Hmsg_len_alloc';
      clear Hmsg_len_alloc Hmsg_len_set_cl;
      rename Hmsg_len_alloc' into Hmsg_len_alloc
  end.

  (* V8 (Bug-B): sha512_64 (h_v ← chal_buf_v, verify_chal_len) — 2-arg arm.
     Post-LetU64: upgraded [frame_through_call_conv_with] bridges the
     [rs_set_scalar_ed] convertibility gap. *)
  peel_call_seq_v Hexec Hframe Hres.
  destruct Hres as [src_bs [len8 [Hsrc [Hlen8 Htgt8]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt7) as Heq; subst src_bs.
  cbn [LE_TU64 loc_var] in Hlen8.
  frame_through_call_conv_with Hframe neq_var_v.
  clear Hframe Hsrc Htgt7.

  (* V9: scalar_reduce (h_red ← h_v) *)
  peel_call_seq_v Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt9]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt8) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_v.
  clear Hframe Hsrc Htgt8.

  (* V10 (Bug-C): memmove_S_from_sig (S_bytes ← sig_in[32..64]) *)
  peel_call_seq_v Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt10a]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hsig_in_alloc) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_v.
  clear Hframe Hsrc.

  (* V10 (Bug-C): ed25519_scalarmult_base (sB ← S_bytes) *)
  peel_call_seq_v Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt10]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt10a) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_v.
  clear Hframe Hsrc Htgt10a.

  (* V11: ed25519_scalarmult (hA ← h_red, A_xyzt_v) *)
  peel_call_seq_v Hexec Hframe Hres.
  destruct Hres as [h_bs [A_bs [Hsh [HsA Htgt11]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsh Htgt9) as Heq; subst h_bs.
  pose proof (slot_holds_inj _ _ _ _ HsA Htgt3) as Heq; subst A_bs.
  frame_through_call_with Hframe neq_var_v.
  clear Hframe Hsh HsA Htgt10.

  (* V12: ed25519_xyzt_add (RcheckA ← R_xyzt_v, hA) *)
  peel_call_seq_v Hexec Hframe Hres.
  destruct Hres as [P_bs [Q_bs [HsP [HsQ Htgt12]]]].
  pose proof (slot_holds_inj _ _ _ _ HsP Htgt2) as Heq; subst P_bs.
  pose proof (slot_holds_inj _ _ _ _ HsQ Htgt11) as Heq; subst Q_bs.
  frame_through_call_with Hframe neq_var_v.
  clear Hframe HsP HsQ Htgt11.

  (* V13: ed25519_compress (check_bytes ← RcheckA) *)
  peel_call_seq_v Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt13]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt12) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_v.
  clear Hpub_alloc Hmsg_alloc Hsig_out_alloc Htgt1 Htgt2 Htgt3 Htgt4
        Htgt9 Htgt12.
  clear Hframe Hsrc.

  (* V14: bytes_equal_32 (v_result ← sig_in, check_bytes) — last call *)
  peel_last_call_v Hexec Hframe Hres.
  destruct Hres as [a_bs [b_bs [Hsa [Hsb Htgt14]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsa Hsig_in_alloc) as Heq; subst a_bs.
  pose proof (slot_holds_inj _ _ _ _ Hsb Htgt13) as Heq; subst b_bs.
  clear Hframe Hsa Hsb.

  (* === Stage C: assembly. ===
     Htgt14's body matches [ed25519_verify_gallina_lifted] with
     [chal_hash_len := Z.to_nat len8] and [chal_init := dst_bs5]. *)
  cbn [LE_TBytes loc_var] in Htgt14.
  exists (Z.to_nat len8), dst_bs5.
  unfold ed25519_verify_gallina_lifted.
  exact Htgt14.
Qed.

(** **Sanity print.**  [Print Assumptions ed25519_verify_strong_correct]
    reports only the paper-fixed leaf-spec Parameters (sha512_full_spec
    + scalar_reduce_spec + ed25519_compress_spec + ed25519_scalarmult_base_spec
    via Sign_Strong_Correctness) and the verify-only Parameters declared
    above (ed25519_decompress_R/A, ed25519_scalarmult, ed25519_xyzt_add,
    scalar_lt_L, bytes_equal_32).  [memmove_R_from_sig_spec] is a
    Definition, not a Parameter. *)
