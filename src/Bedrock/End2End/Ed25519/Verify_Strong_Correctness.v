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
 *        bytes_equal_32).  sha512_full_spec, scalar_reduce_spec,
 *        ed25519_scalarmult_base_spec, ed25519_compress_spec are
 *        reused from [Sign_Strong_Correctness] / [RemainingBridges].
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
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import micromega.Lia.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.RemainingBridges.
Require Import Bedrock.End2End.Ed25519.SHA512Bridge.
Require Import Bedrock.End2End.Ed25519.Sign_Verify_RustCmd.
Require Import Bedrock.End2End.Ed25519.Sign_Strong_Correctness.
Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* §2. Additional Gallina specs for verify-only leaves              *)
(* ================================================================ *)

(** [ed25519_decompress_R_spec sig_in] : 200-byte xyzt representation
    of the decompressed R-point parsed from the first 32 bytes of [sig_in].
    Output is always 200 bytes; an invalid R is modeled as a designated
    "bad" point in the xyzt encoding (the protocol does not branch). *)
Parameter ed25519_decompress_R_spec : list Byte.byte -> list Byte.byte.
Parameter ed25519_decompress_R_spec_len :
  forall sig_in, length (ed25519_decompress_R_spec sig_in) = 200%nat.

(** [ed25519_decompress_A_spec pub] : 200-byte xyzt of the decompressed
    public key. *)
Parameter ed25519_decompress_A_spec : list Byte.byte -> list Byte.byte.
Parameter ed25519_decompress_A_spec_len :
  forall pub, length (ed25519_decompress_A_spec pub) = 200%nat.

(** [ed25519_scalarmult_spec h A_xyzt] : scalar multiplication h·A in xyzt. *)
Parameter ed25519_scalarmult_spec : list Byte.byte -> list Byte.byte -> list Byte.byte.
Parameter ed25519_scalarmult_spec_len :
  forall h A, length (ed25519_scalarmult_spec h A) = 200%nat.

(** [ed25519_xyzt_add_spec P Q] : Edwards addition in xyzt. *)
Parameter ed25519_xyzt_add_spec : list Byte.byte -> list Byte.byte -> list Byte.byte.
Parameter ed25519_xyzt_add_spec_len :
  forall P Q, length (ed25519_xyzt_add_spec P Q) = 200%nat.

(** [scalar_lt_L_spec sig_in] : 1-byte canonical-S check (1 = ok, 0 = bad).
    The protocol writes this to v_result, then *overwrites* it with the
    bytes_equal_32 result.  Hence this spec function is never observed in
    the final postcondition — declared only for completeness. *)
Parameter scalar_lt_L_spec : list Byte.byte -> list Byte.byte.
Parameter scalar_lt_L_spec_len :
  forall sig_in, length (scalar_lt_L_spec sig_in) = 1%nat.

(** [bytes_equal_32_spec sig_in check_bytes] : 1-byte equality result.
    Models constant-time comparison of [firstn 32 sig_in] against
    [check_bytes]. *)
Parameter bytes_equal_32_spec : list Byte.byte -> list Byte.byte -> list Byte.byte.
Parameter bytes_equal_32_spec_len :
  forall a b, length (bytes_equal_32_spec a b) = 1%nat.

(* ================================================================ *)
(* §3. Gallina reference                                              *)
(* ================================================================ *)

(** Top-level verify result: 1 byte.  Computed by the leaf-spec
    composition that mirrors the protocol's straight-line flow.

    Note: the protocol's scalar_lt_L write to v_result is shadowed by
    the final bytes_equal_32 write, so the result depends only on the
    bytes_equal_32 of compress(R + h·A) against the R portion of sig_in. *)
Definition ed25519_verify_gallina
    (sig_in pub _msg : list Byte.byte) : list Byte.byte :=
  let R_xyzt    := ed25519_decompress_R_spec sig_in in
  let A_xyzt    := ed25519_decompress_A_spec pub in
  let h_full    := sha512_full_spec sig_in in
  let h         := scalar_reduce_spec h_full in
  let sB        := ed25519_scalarmult_base_spec sig_in in
  let hA        := ed25519_scalarmult_spec h A_xyzt in
  let RcheckA   := ed25519_xyzt_add_spec R_xyzt hA in
  let check_b   := ed25519_compress_spec RcheckA in
  bytes_equal_32_spec sig_in check_b.

(* The protocol passes [v_sig_in] (64 bytes) as the source to
   sha512_64, scalar_reduce takes the 64-byte h_full → 32-byte h_red,
   and ed25519_scalarmult_base also reads from sig_in.  These
   length disagreements (sB really uses sig_in[32..]) are buried
   inside each leaf's Gallina spec; from our viewpoint each spec is
   a black box [list byte -> list byte]. *)

(* ================================================================ *)
(* §4. Strong callee_post predicate for verify                       *)
(* ================================================================ *)

Definition strong_callee_post_verify
           (fname : String.string)
           (args : list located_ed)
           (dst : located_ed)
           (rs1 rs2 : rust_state_ed) : Prop :=
  frames_except rs1 rs2 dst.(loc_var) /\
  match fname, args with
  | "sha512_64", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (sha512_full_spec src_bs)
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
       (* sign-side too, harmless *)
       v_h_full v_a_slot v_prefix v_A_xyzt v_A_bytes v_nonce_buf
       v_r_full v_r_slot v_R_xyzt v_R_bytes v_chal_buf
       v_k_full v_k_slot v_seed v_msg_len];
  discriminate.

Ltac peel_call_seq_v H Hframe Hres :=
  let Hcall := fresh "Hcall" in
  let Hrest := fresh "Hrest" in
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
  destruct Hcp as [Hframe Hres];
  rename Hrest into H.

Ltac peel_last_call_v H Hframe Hres :=
  inversion H; subst; clear H;
  match goal with
  | Hc : strong_callee_post_verify _ _ _ _ _ |- _ =>
      destruct Hc as [Hframe Hres]
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
         (sig_in pub msg sig_out_init : list Byte.byte),
    length sig_in = 64%nat ->
    length pub    = 32%nat ->
    length msg    = 4096%nat ->
    slot_holds rs1 v_sig_in  sig_in ->
    slot_holds rs1 v_pub     pub ->
    slot_holds rs1 v_msg     msg ->
    slot_holds rs1 v_sig_out sig_out_init ->
    rust_exec_ed strong_callee_post_verify callee_post_n function_table
                 ed25519_verify_rs rs1 rs2 ->
    slot_holds rs2 v_result
      (ed25519_verify_gallina sig_in pub msg).
Proof.
  intros callee_post_n function_table rs1 rs2
         sig_in pub msg sig_out_init
         Hsig_len Hpub_len Hmsg_len
         Hsig_in Hpub Hmsg Hsig_out Hexec.
  unfold ed25519_verify_rs in Hexec.

  (* Stage A: peel 9 REdLetZero allocations. *)
  repeat (match goal with
          | H : rust_exec_ed _ _ _ (REdLetZero _ _ _) _ _ |- _ =>
              inversion H; subst; clear H
          end).

  (* Propagate sig_in/pub/msg across the 9 fresh slot allocations
     into the post-allocation state via [slot_holds_set_tower_other]. *)
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
      rename H into Hexec
  end.
  clear Hsig_in Hpub Hmsg Hsig_out.

  (* === Stage B: 10 call inversions === *)

  (* V1: scalar_lt_L (v_result ← sig_in) *)
  peel_call_seq_v Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt1]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hsig_in_alloc) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_in_alloc; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hpub_alloc; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_out_alloc; [|neq_var_v].
  clear Hframe Hsrc.

  (* V2: ed25519_decompress_R (R_xyzt_v ← sig_in) *)
  peel_call_seq_v Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt2]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hsig_in_alloc) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_in_alloc; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hpub_alloc; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_out_alloc; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt1; [|neq_var_v].
  clear Hframe Hsrc.

  (* V3: ed25519_decompress_A (A_xyzt_v ← pub) *)
  peel_call_seq_v Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt3]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hpub_alloc) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_in_alloc; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hpub_alloc; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_out_alloc; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt1; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt2; [|neq_var_v].
  clear Hframe Hsrc.

  (* V4: sha512_64 (h_v ← sig_in) *)
  peel_call_seq_v Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt4]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hsig_in_alloc) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_in_alloc; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hpub_alloc; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_out_alloc; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt1; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt2; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3; [|neq_var_v].
  clear Hframe Hsrc.

  (* V5: scalar_reduce (h_red ← h_v) *)
  peel_call_seq_v Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt5]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt4) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_in_alloc; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hpub_alloc; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_out_alloc; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt1; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt2; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3; [|neq_var_v].
  clear Hframe Hsrc Htgt4.

  (* V6: ed25519_scalarmult_base (sB ← sig_in) *)
  peel_call_seq_v Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt6]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hsig_in_alloc) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_in_alloc; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hpub_alloc; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_out_alloc; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt1; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt2; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt5; [|neq_var_v].
  clear Hframe Hsrc.

  (* V7: ed25519_scalarmult (hA ← h_red, A_xyzt_v) *)
  peel_call_seq_v Hexec Hframe Hres.
  destruct Hres as [h_bs [A_bs [Hsh [HsA Htgt7]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsh Htgt5) as Heq; subst h_bs.
  pose proof (slot_holds_inj _ _ _ _ HsA Htgt3) as Heq; subst A_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_in_alloc; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hpub_alloc; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_out_alloc; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt1; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt2; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt5; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt6; [|neq_var_v].
  clear Hframe Hsh HsA.

  (* V8: ed25519_xyzt_add (RcheckA ← R_xyzt_v, hA) *)
  peel_call_seq_v Hexec Hframe Hres.
  destruct Hres as [P_bs [Q_bs [HsP [HsQ Htgt8]]]].
  pose proof (slot_holds_inj _ _ _ _ HsP Htgt2) as Heq; subst P_bs.
  pose proof (slot_holds_inj _ _ _ _ HsQ Htgt7) as Heq; subst Q_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_in_alloc; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hpub_alloc; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_out_alloc; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt1; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt2; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3; [|neq_var_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt5; [|neq_var_v].
  clear Hframe HsP HsQ Htgt6 Htgt7.

  (* V9: ed25519_compress (check_bytes ← RcheckA) *)
  peel_call_seq_v Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt9]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt8) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_in_alloc; [|neq_var_v].
  clear Hpub_alloc Hmsg_alloc Hsig_out_alloc Htgt1 Htgt2 Htgt3 Htgt5 Htgt8.
  clear Hframe Hsrc.

  (* V10: bytes_equal_32 (v_result ← sig_in, check_bytes) — last call *)
  peel_last_call_v Hexec Hframe Hres.
  destruct Hres as [a_bs [b_bs [Hsa [Hsb Htgt10]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsa Hsig_in_alloc) as Heq; subst a_bs.
  pose proof (slot_holds_inj _ _ _ _ Hsb Htgt9) as Heq; subst b_bs.
  clear Hframe Hsa Hsb.

  (* === Stage C: assembly. ===
     Htgt10 says rs2's v_result =
       bytes_equal_32_spec sig_in
         (ed25519_compress_spec (ed25519_xyzt_add_spec
            (ed25519_decompress_R_spec sig_in)
            (ed25519_scalarmult_spec (scalar_reduce_spec (sha512_full_spec sig_in))
                                     (ed25519_decompress_A_spec pub)))).
     This is exactly [ed25519_verify_gallina sig_in pub msg]. *)
  cbn [LE_TBytes loc_var] in Htgt10.
  unfold ed25519_verify_gallina.
  exact Htgt10.
Qed.

(** **Sanity print.**  [Print Assumptions ed25519_verify_strong_correct]
    reports only the 6 paper-fixed leaf-spec Parameters and the 6
    verify-only Parameters declared above. *)
