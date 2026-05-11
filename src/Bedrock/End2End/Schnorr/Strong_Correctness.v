(** * Schnorr Strong_Correctness — strong correctness for
 *    [schnorr_sign_rs] and [schnorr_verify_rs].
 *
 * Functional postcondition: under [strong_callee_post_schnorr] (each
 * leaf returns its Gallina spec AND frames all other tower slots), the
 * sig_out / result slot equals the lifted Gallina reference applied to
 * the inputs.
 *
 * Mirrors [Bedrock.End2End.XEdDSA.Sign_Strong_Correctness] (dynamic
 * message length, REdLetU64 step for chal_hash_len, scalar-frame
 * conjunct in [strong_callee_post]).  Reuses every leaf Gallina spec
 * from Ed25519 / RemainingBridges — no new leaves.
 *
 * The proof uses the [frame_through_call_with] tactic from
 * [Bedrock.End2End.StrongCorrectnessTactics] (commit 780ed07) to
 * collapse the per-call frame-propagation block from ~10 lines to a
 * single line.  Both theorems are Qed-clean; [Print Assumptions]
 * reports only [sha512_full_spec] (inherited from Ed25519).
 *
 * Architecture:
 *   §1 Per-callee Gallina specs (all reused; no new leaves).
 *   §2 Gallina references [schnorr_sign_gallina] /
 *      [schnorr_verify_gallina_lifted].
 *   §3 [strong_callee_post_schnorr] + frame lemma (Qed).
 *   §4 [schnorr_sign_strong_correct]   (Qed).
 *   §5 [schnorr_verify_strong_correct] (Qed).
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
Require Import Bedrock.End2End.Ed25519.Verify_Strong_Correctness.
Require Import Bedrock.End2End.Ed25519.ScalarmultVerified.
Require Import Bedrock.End2End.Ed25519.XyztAddVerified.
Require Import Bedrock.End2End.Ed25519.DecompressVerified.
Require Import Bedrock.End2End.StrongCorrectnessTactics.
Require Import Bedrock.End2End.Schnorr.Sign_RustCmd.
Require Import Bedrock.End2End.Schnorr.Verify_RustCmd.
Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* §1. Memmove specs reused under the canonical Ed25519 layouts.      *)
(* ================================================================ *)

(** Schnorr's protocol body uses the same memmove leaves as Ed25519's
    sign/verify, so the per-callee Gallina specs are all reused.
    Specifically:
      memmove_chal_R  : (src ++ skipn |src| dst)
      memmove_chal_A  : (firstn 32 dst ++ src ++ skipn (32+|src|) dst)
      memmove_chal_M  : (firstn 64 dst ++ src)
      memmove_sig_R   : (firstn 32 dst ++ src)
      memmove_R_from_sig : firstn 32 sig
      memmove_S_from_sig : skipn 32 sig

    For convenience, we name them at the Schnorr level so the lifted
    reference reads cleanly. *)
Definition memmove_sn_chal_R_spec (src_bs dst_bs : list Byte.byte) : list Byte.byte :=
  (src_bs ++ skipn (length src_bs) dst_bs)%list.
Definition memmove_sn_chal_A_spec (src_bs dst_bs : list Byte.byte) : list Byte.byte :=
  (firstn 32 dst_bs ++ src_bs ++ skipn (32 + length src_bs) dst_bs)%list.
Definition memmove_sn_chal_M_spec (src_bs dst_bs : list Byte.byte) : list Byte.byte :=
  (firstn 64 dst_bs ++ src_bs)%list.
Definition memmove_sn_sig_R_spec (src_bs dst_bs : list Byte.byte) : list Byte.byte :=
  (firstn 32 dst_bs ++ src_bs)%list.

(* ================================================================ *)
(* §2. Gallina references                                             *)
(* ================================================================ *)

(** Clean Schnorr sign reference. *)
Definition schnorr_sign_gallina
    (sk msg r_rand : list Byte.byte) : list Byte.byte :=
  let R_xyzt   := ed25519_scalarmult_base_spec r_rand in
  let R_bytes  := ed25519_compress_spec R_xyzt in
  let PK_xyzt  := ed25519_scalarmult_base_spec sk in
  let PK_bytes := ed25519_compress_spec PK_xyzt in
  let chal     := (R_bytes ++ PK_bytes ++ msg)%list in
  let chal_full:= sha512_full_spec chal in
  let c        := scalar_reduce_spec chal_full in
  let s        := scalar_muladd_spec r_rand c sk in
  (s ++ R_bytes)%list.

(** Lifted Schnorr sign reference (matches protocol's intermediate
    state precisely; threads dynamic hash length + per-buffer init). *)
Definition schnorr_sign_gallina_lifted
    (sk msg r_rand : list Byte.byte)
    (chal_hash_len : nat)
    (chal_init sig_init : list Byte.byte)
  : list Byte.byte :=
  let R_xyzt   := ed25519_scalarmult_base_spec r_rand in
  let R_bytes  := ed25519_compress_spec R_xyzt in
  let PK_xyzt  := ed25519_scalarmult_base_spec sk in
  let PK_bytes := ed25519_compress_spec PK_xyzt in
  let chal_C5  := memmove_sn_chal_R_spec R_bytes chal_init in
  let chal_C6  := memmove_sn_chal_A_spec PK_bytes chal_C5 in
  let chal_C7  := memmove_sn_chal_M_spec msg chal_C6 in
  let chal_full:= sha512_full_spec (firstn chal_hash_len chal_C7) in
  let c        := scalar_reduce_spec chal_full in
  let sig_C9   := (scalar_muladd_spec r_rand c sk ++ skipn 32 sig_init)%list in
  (firstn 32 sig_C9 ++ R_bytes)%list.

(** Lifted Schnorr verify reference (1-byte result).

    The protocol writes the [bytes_equal_32] result to v_sn_result.
    Per Verify's pattern, the comparison is between [sig[0..32]] (the
    R-component of the signature) and [compress(R_xyzt + c·PK_xyzt)].

    The "lifted" form parameterises on the initial chal_buf bytes +
    dynamic hash length, matching the protocol's intermediate state.
    The clean form is recoverable under standard buffer widths. *)
Definition schnorr_verify_gallina_lifted
    (sig pk msg : list Byte.byte)
    (chal_hash_len : nat)
    (chal_init : list Byte.byte)
  : list Byte.byte :=
  let R_bytes   := memmove_R_from_sig_spec sig in
  let S_bytes   := memmove_S_from_sig_spec sig in
  let R_xyzt    := ed25519_decompress_R_spec sig in
  let PK_xyzt   := ed25519_decompress_A_spec pk in
  let chal_C5   := memmove_sn_chal_R_spec R_bytes chal_init in
  let chal_C6   := memmove_sn_chal_A_spec pk chal_C5 in
  let chal_C7   := memmove_sn_chal_M_spec msg chal_C6 in
  let chal_full := sha512_full_spec (firstn chal_hash_len chal_C7) in
  let c         := scalar_reduce_spec chal_full in
  let sB        := ed25519_scalarmult_base_spec S_bytes in
  let cPK       := ed25519_scalarmult_spec c PK_xyzt in
  let R_check   := ed25519_xyzt_add_spec R_xyzt cPK in
  let check_b   := ed25519_compress_spec R_check in
  bytes_equal_32_spec sig check_b.

(* ================================================================ *)
(* §3. Strong callee_post predicate                                   *)
(* ================================================================ *)

(** Per-call obligation: dest gets the leaf's Gallina spec, all other
    tower slots are framed, and both message-length scalars (sign-side
    [v_sn_msg_len] and verify-side [v_sn_v_msg_len]) are preserved.

    Threading two scalar slots is simpler than the Ed25519 verify
    pattern; the protocol consumes only one in each direction, but
    [strong_callee_post_schnorr] is shared between sign and verify
    proofs so we frame both unconditionally. *)
Definition strong_callee_post_schnorr
           (fname : String.string)
           (args : list located_ed)
           (dst : located_ed)
           (rs1 rs2 : rust_state_ed) : Prop :=
  frames_except rs1 rs2 dst.(loc_var) /\
  (rs_get_scalar_ed rs1 v_sn_msg_len = rs_get_scalar_ed rs2 v_sn_msg_len) /\
  (rs_get_scalar_ed rs1 v_sn_v_msg_len = rs_get_scalar_ed rs2 v_sn_v_msg_len) /\
  match fname, args with
  | "sha512_64", [src; len_arg] =>
      exists src_bs len,
        slot_holds rs1 src.(loc_var) src_bs /\
        rs_get_scalar_ed rs1 len_arg.(loc_var) = Some len /\
        slot_holds rs2 dst.(loc_var)
          (sha512_full_spec (firstn (Z.to_nat len) src_bs))
  | "scalar_reduce", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (scalar_reduce_spec src_bs)
  | "scalar_muladd", [r; k; a] =>
      exists r_bs k_bs a_bs dst_bs,
        slot_holds rs1 r.(loc_var) r_bs /\
        slot_holds rs1 k.(loc_var) k_bs /\
        slot_holds rs1 a.(loc_var) a_bs /\
        slot_holds rs1 dst.(loc_var) dst_bs /\
        slot_holds rs2 dst.(loc_var)
          (scalar_muladd_spec r_bs k_bs a_bs ++ skipn 32 dst_bs)
  | "ed25519_compress", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (ed25519_compress_spec src_bs)
  | "ed25519_scalarmult_base", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (ed25519_scalarmult_base_spec src_bs)
  | "ed25519_scalarmult", [sc; pt] =>
      exists sc_bs pt_bs,
        slot_holds rs1 sc.(loc_var) sc_bs /\
        slot_holds rs1 pt.(loc_var) pt_bs /\
        slot_holds rs2 dst.(loc_var) (ed25519_scalarmult_spec sc_bs pt_bs)
  | "ed25519_xyzt_add", [p; q] =>
      exists p_bs q_bs,
        slot_holds rs1 p.(loc_var) p_bs /\
        slot_holds rs1 q.(loc_var) q_bs /\
        slot_holds rs2 dst.(loc_var) (ed25519_xyzt_add_spec p_bs q_bs)
  | "ed25519_decompress_R", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (ed25519_decompress_R_spec src_bs)
  | "ed25519_decompress_A", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (ed25519_decompress_A_spec src_bs)
  | "memmove_chal_R", [src] =>
      exists src_bs dst_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs1 dst.(loc_var) dst_bs /\
        slot_holds rs2 dst.(loc_var) (memmove_sn_chal_R_spec src_bs dst_bs)
  | "memmove_chal_A", [src] =>
      exists src_bs dst_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs1 dst.(loc_var) dst_bs /\
        slot_holds rs2 dst.(loc_var) (memmove_sn_chal_A_spec src_bs dst_bs)
  | "memmove_chal_M", [src] =>
      exists src_bs dst_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs1 dst.(loc_var) dst_bs /\
        slot_holds rs2 dst.(loc_var) (memmove_sn_chal_M_spec src_bs dst_bs)
  | "memmove_sig_R", [src] =>
      exists src_bs dst_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs1 dst.(loc_var) dst_bs /\
        slot_holds rs2 dst.(loc_var) (memmove_sn_sig_R_spec src_bs dst_bs)
  | "memmove_R_from_sig", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (memmove_R_from_sig_spec src_bs)
  | "memmove_S_from_sig", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (memmove_S_from_sig_spec src_bs)
  | "bytes_equal_32", [a; b] =>
      exists a_bs b_bs,
        slot_holds rs1 a.(loc_var) a_bs /\
        slot_holds rs1 b.(loc_var) b_bs /\
        slot_holds rs2 dst.(loc_var) (bytes_equal_32_spec a_bs b_bs)
  | _, _ => True
  end.

(* ================================================================ *)
(* §3a. Frame lemma — Qed                                             *)
(* ================================================================ *)

Lemma strong_callee_post_schnorr_frame_other_slots :
  forall fname args dst rs1 rs2 x,
    strong_callee_post_schnorr fname args dst rs1 rs2 ->
    x <> dst.(loc_var) ->
    rs_get_tower_ed rs1 x = rs_get_tower_ed rs2 x.
Proof.
  intros fname args dst rs1 rs2 x [Hframe _] Hne.
  apply (Hframe x Hne).
Qed.

(* ================================================================ *)
(* §4. Strong correctness — sign                                      *)
(* ================================================================ *)

(** Disequality tactic for Schnorr sign slot names. *)
Ltac neq_var_sn :=
  cbn [LE_TBytes LE_TU64 loc_var];
  cbv [v_sn_sk v_sn_msg v_sn_msg_len v_sn_r_rand v_sn_sig_out
       v_sn_R_xyzt v_sn_R_bytes v_sn_PK_xyzt v_sn_PK_bytes
       v_sn_chal_buf v_sn_chal_full v_sn_c];
  discriminate.

(** Peel one call: pulls [strong_callee_post_schnorr] from the
    inverted call hypothesis, destructures into frame + two scalar
    frames + result, threads the two scalar slot equalities. *)
Ltac peel_call_seq_sn H Hframe Hres :=
  let Hcall := fresh "Hcall" in
  let Hrest := fresh "Hrest" in
  let Hsc1 := fresh "Hsc_sn_msg" in
  let Hsc2 := fresh "Hsc_sn_v_msg" in
  inversion H; subst; clear H;
  match goal with
  | Hc : rust_exec_ed _ _ _ (REdCall _ _ _) _ _,
    Hr : rust_exec_ed _ _ _ _ _ _ |- _ =>
      rename Hc into Hcall; rename Hr into Hrest
  end;
  inversion Hcall; subst; clear Hcall;
  match goal with
  | Hc : strong_callee_post_schnorr _ _ _ _ _ |- _ =>
      destruct Hc as [Hframe [Hsc1 [Hsc2 Hres]]]
  end;
  (* Rewrite scalar-frame equalities into [Hmsg_len_alloc] if present. *)
  (try match goal with
   | Hh : rs_get_scalar_ed _ v_sn_msg_len = Some _ |- _ =>
       rewrite Hsc1 in Hh
   end);
  (try match goal with
   | Hh : rs_get_scalar_ed _ v_sn_v_msg_len = Some _ |- _ =>
       rewrite Hsc2 in Hh
   end);
  clear Hsc1 Hsc2;
  rename Hrest into H.

Ltac peel_last_call_sn H Hframe Hres :=
  let Hsc1 := fresh "Hsc_sn_msg" in
  let Hsc2 := fresh "Hsc_sn_v_msg" in
  inversion H; subst; clear H;
  match goal with
  | Hc : strong_callee_post_schnorr _ _ _ _ _ |- _ =>
      destruct Hc as [Hframe [Hsc1 [Hsc2 Hres]]]; clear Hsc1 Hsc2
  end.

Theorem schnorr_sign_strong_correct :
  forall (callee_post_n :
            String.string -> list located_ed -> list located_ed ->
            rust_state_ed -> rust_state_ed -> Prop)
         (function_table : function_table_ed)
         (rs1 rs2 : rust_state_ed)
         (sk msg r_rand sig_init : list Byte.byte)
         (msg_len : Z),
    length sk = 32%nat ->
    length msg = 4096%nat ->
    length r_rand = 32%nat ->
    (0 <= msg_len <= 4096)%Z ->
    slot_holds rs1 v_sn_sk sk ->
    slot_holds rs1 v_sn_msg msg ->
    slot_holds rs1 v_sn_r_rand r_rand ->
    slot_holds rs1 v_sn_sig_out sig_init ->
    rs_get_scalar_ed rs1 v_sn_msg_len = Some msg_len ->
    rust_exec_ed strong_callee_post_schnorr callee_post_n function_table
                 schnorr_sign_rs rs1 rs2 ->
    exists chal_hash_len chal_init,
      slot_holds rs2 v_sn_sig_out
        (schnorr_sign_gallina_lifted sk msg r_rand
           chal_hash_len chal_init sig_init).
Proof.
  intros callee_post_n function_table rs1 rs2 sk msg r_rand sig_init msg_len
         Hsk_len Hmsg_len Hr_rand_len Hmsg_len_bound
         Hsk Hmsg Hr_rand Hsig_init Hmsg_len_get Hexec.
  unfold schnorr_sign_rs in Hexec.

  (* Stage A: peel 7 REdLetZero allocations. *)
  peel_all_let_zero.

  (* Propagate input slots through 7 fresh allocations. *)
  match goal with
  | H : rust_exec_ed _ _ _ _ ?rs_alloc _ |- _ =>
      assert (Hsk_alloc : slot_holds rs_alloc v_sn_sk sk) by
        (slot_holds_set_tower_other_repeat Hsk);
      assert (Hmsg_alloc : slot_holds rs_alloc v_sn_msg msg) by
        (slot_holds_set_tower_other_repeat Hmsg);
      assert (Hr_rand_alloc : slot_holds rs_alloc v_sn_r_rand r_rand) by
        (slot_holds_set_tower_other_repeat Hr_rand);
      assert (Hsig_alloc : slot_holds rs_alloc v_sn_sig_out sig_init) by
        (slot_holds_set_tower_other_repeat Hsig_init);
      assert (Hmsg_len_alloc : rs_get_scalar_ed rs_alloc v_sn_msg_len = Some msg_len) by
        (repeat rewrite scalar_get_set_tower; exact Hmsg_len_get);
      rename H into Hexec
  end.
  clear Hsk Hmsg Hr_rand Hsig_init Hmsg_len_get.

  (* === Stage B: 10 call inversions === *)

  (* C1: ed25519_scalarmult_base (R_xyzt ← r_rand) *)
  peel_call_seq_sn Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt1]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hr_rand_alloc) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_sn.
  clear Hframe Hsrc.

  (* C2: ed25519_compress (R_bytes ← R_xyzt) *)
  peel_call_seq_sn Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt2]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt1) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_sn.
  clear Hframe Hsrc Htgt1.

  (* C3: ed25519_scalarmult_base (PK_xyzt ← sk) *)
  peel_call_seq_sn Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt3]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hsk_alloc) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_sn.
  clear Hframe Hsrc.

  (* C4: ed25519_compress (PK_bytes ← PK_xyzt) *)
  peel_call_seq_sn Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt4]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt3) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_sn.
  clear Hframe Hsrc Htgt3.

  (* C5: memmove_chal_R (chal_buf ← R_bytes) *)
  peel_call_seq_sn Hexec Hframe Hres.
  destruct Hres as [src_bs [dst_bs5 [Hsrc [Hdst Htgt5]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt2) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_sn.
  clear Hframe Hsrc Hdst.

  (* C6: memmove_chal_A (chal_buf ← PK_bytes) *)
  peel_call_seq_sn Hexec Hframe Hres.
  destruct Hres as [src_bs [dst_bs [Hsrc [Hdst Htgt6]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt4) as Heq; subst src_bs.
  pose proof (slot_holds_inj _ _ _ _ Hdst Htgt5) as Heq2; subst dst_bs.
  frame_through_call_with Hframe neq_var_sn.
  clear Hframe Hsrc Hdst Htgt5.

  (* C7: memmove_chal_M (chal_buf ← msg) *)
  peel_call_seq_sn Hexec Hframe Hres.
  destruct Hres as [src_bs [dst_bs [Hsrc [Hdst Htgt7]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hmsg_alloc) as Heq; subst src_bs.
  pose proof (slot_holds_inj _ _ _ _ Hdst Htgt6) as Heq2; subst dst_bs.
  frame_through_call_with Hframe neq_var_sn.
  clear Hframe Hsrc Hdst Htgt4 Htgt6.

  (* Peel REdLetU64 "sn_chal_hash_len" *)
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
  assert (Hmsg_set_cl : v_sn_msg_len <> "sn_chal_hash_len")
    by (cbv [v_sn_msg_len]; intro Hcontra; discriminate Hcontra).
  match goal with
  | _ : context [rs_set_scalar_ed ?rs0 "sn_chal_hash_len" ?v0] |- _ =>
      pose proof (slot_holds_scalar_set_other rs0 "sn_chal_hash_len" v0 _ _
                    Hmsg_set_cl Hmsg_len_alloc) as Hmsg_len_alloc';
      clear Hmsg_len_alloc Hmsg_set_cl;
      rename Hmsg_len_alloc' into Hmsg_len_alloc
  end.

  (* C8: sha512_64 (chal_full ← chal_buf, chal_hash_len)
     Post-LetU64: Hframe's LHS is [rs_set_scalar_ed rs ...] which doesn't
     syntactically unify with the tower-slot states [rs9].  We fall back to
     manual [apply slot_holds_frame _ _ _ _ _ Hframe in H], which uses
     [apply]'s built-in conversion to bridge the eta-reduction gap. *)
  peel_call_seq_sn Hexec Hframe Hres.
  destruct Hres as [src_bs [len8 [Hsrc [Hlen8 Htgt8]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt7) as Heq; subst src_bs.
  cbn [LE_TU64 loc_var] in Hlen8.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsk_alloc; [|neq_var_sn].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var_sn].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hr_rand_alloc; [|neq_var_sn].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var_sn].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt2; [|neq_var_sn].
  clear Hframe Hsrc Htgt7.

  (* C9: scalar_reduce (c ← chal_full) *)
  peel_call_seq_sn Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt9]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt8) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsk_alloc; [|neq_var_sn].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var_sn].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hr_rand_alloc; [|neq_var_sn].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var_sn].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt2; [|neq_var_sn].
  clear Hframe Hsrc Htgt8.

  (* C10: scalar_muladd (sig_out ← r_rand, c, sk) *)
  peel_call_seq_sn Hexec Hframe Hres.
  destruct Hres as [r_bs [k_bs [a_bs [dst_bs [Hsr [Hsk_get [Hsa [Hsd Htgt10]]]]]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsr Hr_rand_alloc) as Heq; subst r_bs.
  pose proof (slot_holds_inj _ _ _ _ Hsk_get Htgt9) as Heq; subst k_bs.
  pose proof (slot_holds_inj _ _ _ _ Hsa Hsk_alloc) as Heq; subst a_bs.
  pose proof (slot_holds_inj _ _ _ _ Hsd Hsig_alloc) as Heq; subst dst_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt2; [|neq_var_sn].
  clear Hframe Hsr Hsk_get Hsa Hsd Hsk_alloc Hr_rand_alloc Hsig_alloc Htgt9.

  (* C11: memmove_sig_R (sig_out ← R_bytes) — last call *)
  peel_last_call_sn Hexec Hframe Hres.
  destruct Hres as [src_bs [dst_bs [Hsrc [Hdst Htgt11]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt2) as Heq; subst src_bs.
  pose proof (slot_holds_inj _ _ _ _ Hdst Htgt10) as Heq2; subst dst_bs.
  clear Hframe Hsrc Hdst.

  (* Stage C: assembly. *)
  cbn [LE_TBytes loc_var] in Htgt11.
  exists (Z.to_nat len8), dst_bs5.
  unfold schnorr_sign_gallina_lifted, memmove_sn_sig_R_spec.
  exact Htgt11.
Qed.

(* ================================================================ *)
(* §5. Strong correctness — verify                                    *)
(* ================================================================ *)

Ltac neq_var_sn_v :=
  cbn [LE_TBytes LE_TU64 loc_var];
  cbv [v_sn_sig v_sn_pk v_sn_v_msg v_sn_v_msg_len v_sn_result
       v_sn_R_bytes_v v_sn_S_bytes_v v_sn_R_xyzt_v v_sn_PK_xyzt_v
       v_sn_chal_buf_v v_sn_chal_full_v v_sn_c_v v_sn_sB v_sn_cPK
       v_sn_R_check v_sn_check_bytes];
  discriminate.

Ltac peel_call_seq_sn_v H Hframe Hres :=
  let Hcall := fresh "Hcall" in
  let Hrest := fresh "Hrest" in
  let Hsc1 := fresh "Hsc_sn_msg" in
  let Hsc2 := fresh "Hsc_sn_v_msg" in
  inversion H; subst; clear H;
  match goal with
  | Hc : rust_exec_ed _ _ _ (REdCall _ _ _) _ _,
    Hr : rust_exec_ed _ _ _ _ _ _ |- _ =>
      rename Hc into Hcall; rename Hr into Hrest
  end;
  inversion Hcall; subst; clear Hcall;
  match goal with
  | Hc : strong_callee_post_schnorr _ _ _ _ _ |- _ =>
      destruct Hc as [Hframe [Hsc1 [Hsc2 Hres]]]
  end;
  (try match goal with
   | Hh : rs_get_scalar_ed _ v_sn_msg_len = Some _ |- _ =>
       rewrite Hsc1 in Hh
   end);
  (try match goal with
   | Hh : rs_get_scalar_ed _ v_sn_v_msg_len = Some _ |- _ =>
       rewrite Hsc2 in Hh
   end);
  clear Hsc1 Hsc2;
  rename Hrest into H.

Ltac peel_last_call_sn_v H Hframe Hres :=
  let Hsc1 := fresh "Hsc_sn_msg" in
  let Hsc2 := fresh "Hsc_sn_v_msg" in
  inversion H; subst; clear H;
  match goal with
  | Hc : strong_callee_post_schnorr _ _ _ _ _ |- _ =>
      destruct Hc as [Hframe [Hsc1 [Hsc2 Hres]]]; clear Hsc1 Hsc2
  end.

Theorem schnorr_verify_strong_correct :
  forall (callee_post_n :
            String.string -> list located_ed -> list located_ed ->
            rust_state_ed -> rust_state_ed -> Prop)
         (function_table : function_table_ed)
         (rs1 rs2 : rust_state_ed)
         (sig pk msg : list Byte.byte)
         (msg_len : Z),
    length sig = 64%nat ->
    length pk  = 32%nat ->
    length msg = 4096%nat ->
    (0 <= msg_len <= 4096)%Z ->
    slot_holds rs1 v_sn_sig sig ->
    slot_holds rs1 v_sn_pk pk ->
    slot_holds rs1 v_sn_v_msg msg ->
    rs_get_scalar_ed rs1 v_sn_v_msg_len = Some msg_len ->
    rust_exec_ed strong_callee_post_schnorr callee_post_n function_table
                 schnorr_verify_rs rs1 rs2 ->
    exists chal_hash_len chal_init,
      slot_holds rs2 v_sn_result
        (schnorr_verify_gallina_lifted sig pk msg chal_hash_len chal_init).
Proof.
  intros callee_post_n function_table rs1 rs2 sig pk msg msg_len
         Hsig_len Hpk_len Hmsg_len Hmsg_len_bound
         Hsig Hpk Hmsg Hmsg_len_get Hexec.
  unfold schnorr_verify_rs in Hexec.

  (* Stage A: peel 12 REdLetZero allocations. *)
  peel_all_let_zero.

  (* Propagate input slots through 12 fresh allocations.
     [v_sn_result] is allocated by REdLetZero (gets tt_zero), not threaded
     from rs1; the verify protocol writes to it via the final
     bytes_equal_32 leaf. *)
  match goal with
  | H : rust_exec_ed _ _ _ _ ?rs_alloc _ |- _ =>
      assert (Hsig_alloc : slot_holds rs_alloc v_sn_sig sig) by
        (slot_holds_set_tower_other_repeat Hsig);
      assert (Hpk_alloc : slot_holds rs_alloc v_sn_pk pk) by
        (slot_holds_set_tower_other_repeat Hpk);
      assert (Hmsg_alloc : slot_holds rs_alloc v_sn_v_msg msg) by
        (slot_holds_set_tower_other_repeat Hmsg);
      assert (Hmsg_len_alloc : rs_get_scalar_ed rs_alloc v_sn_v_msg_len = Some msg_len) by
        (repeat rewrite scalar_get_set_tower; exact Hmsg_len_get);
      rename H into Hexec
  end.
  clear Hsig Hpk Hmsg Hmsg_len_get.

  (* === Stage B: 13 call inversions === *)

  (* C1: memmove_R_from_sig (R_bytes_v ← sig) *)
  peel_call_seq_sn_v Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt1]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hsig_alloc) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_sn_v.
  clear Hframe Hsrc.

  (* C2: memmove_S_from_sig (S_bytes_v ← sig) *)
  peel_call_seq_sn_v Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt2]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hsig_alloc) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_sn_v.
  clear Hframe Hsrc.

  (* C3: ed25519_decompress_R (R_xyzt_v ← sig) *)
  peel_call_seq_sn_v Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt3]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hsig_alloc) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_sn_v.
  clear Hframe Hsrc.

  (* C4: ed25519_decompress_A (PK_xyzt_v ← pk) *)
  peel_call_seq_sn_v Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt4]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hpk_alloc) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_sn_v.
  clear Hframe Hsrc.

  (* C5: memmove_chal_R (chal_buf_v ← R_bytes_v) *)
  peel_call_seq_sn_v Hexec Hframe Hres.
  destruct Hres as [src_bs [dst_bs5 [Hsrc [Hdst Htgt5]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt1) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_sn_v.
  clear Hframe Hsrc Hdst.

  (* C6: memmove_chal_A (chal_buf_v ← pk) *)
  peel_call_seq_sn_v Hexec Hframe Hres.
  destruct Hres as [src_bs [dst_bs [Hsrc [Hdst Htgt6]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hpk_alloc) as Heq; subst src_bs.
  pose proof (slot_holds_inj _ _ _ _ Hdst Htgt5) as Heq2; subst dst_bs.
  frame_through_call_with Hframe neq_var_sn_v.
  clear Hframe Hsrc Hdst Htgt5.

  (* C7: memmove_chal_M (chal_buf_v ← msg) *)
  peel_call_seq_sn_v Hexec Hframe Hres.
  destruct Hres as [src_bs [dst_bs [Hsrc [Hdst Htgt7]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hmsg_alloc) as Heq; subst src_bs.
  pose proof (slot_holds_inj _ _ _ _ Hdst Htgt6) as Heq2; subst dst_bs.
  frame_through_call_with Hframe neq_var_sn_v.
  clear Hframe Hsrc Hdst Htgt6.

  (* Peel REdLetU64 "sn_verify_chal_len" *)
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
  assert (Hmsg_set_cl : v_sn_v_msg_len <> "sn_verify_chal_len")
    by (cbv [v_sn_v_msg_len]; intro Hcontra; discriminate Hcontra).
  match goal with
  | _ : context [rs_set_scalar_ed ?rs0 "sn_verify_chal_len" ?v0] |- _ =>
      pose proof (slot_holds_scalar_set_other rs0 "sn_verify_chal_len" v0 _ _
                    Hmsg_set_cl Hmsg_len_alloc) as Hmsg_len_alloc';
      clear Hmsg_len_alloc Hmsg_set_cl;
      rename Hmsg_len_alloc' into Hmsg_len_alloc
  end.

  (* C8: sha512_64 (chal_full_v ← chal_buf_v, verify_chal_len)
     Post-LetU64: use manual [apply slot_holds_frame] to bridge the
     [rs_set_scalar_ed] vs [rs9] convertibility gap (same as sign's C8). *)
  peel_call_seq_sn_v Hexec Hframe Hres.
  destruct Hres as [src_bs [len8 [Hsrc [Hlen8 Htgt8]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt7) as Heq; subst src_bs.
  cbn [LE_TU64 loc_var] in Hlen8.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var_sn_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hpk_alloc; [|neq_var_sn_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var_sn_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt2; [|neq_var_sn_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3; [|neq_var_sn_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt4; [|neq_var_sn_v].
  clear Hframe Hsrc Htgt7.

  (* C9: scalar_reduce (c_v ← chal_full_v) *)
  peel_call_seq_sn_v Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt9]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt8) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var_sn_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hpk_alloc; [|neq_var_sn_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var_sn_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt2; [|neq_var_sn_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3; [|neq_var_sn_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt4; [|neq_var_sn_v].
  clear Hframe Hsrc Htgt8.

  (* C10: ed25519_scalarmult_base (sB ← S_bytes_v) *)
  peel_call_seq_sn_v Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt10]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt2) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var_sn_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hpk_alloc; [|neq_var_sn_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var_sn_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3; [|neq_var_sn_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt4; [|neq_var_sn_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt9; [|neq_var_sn_v].
  clear Hframe Hsrc Htgt2.

  (* C11: ed25519_scalarmult (cPK ← c_v, PK_xyzt_v) *)
  peel_call_seq_sn_v Hexec Hframe Hres.
  destruct Hres as [sc_bs [pt_bs [Hsc [Hpt Htgt11]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsc Htgt9) as Heq; subst sc_bs.
  pose proof (slot_holds_inj _ _ _ _ Hpt Htgt4) as Heq; subst pt_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var_sn_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hpk_alloc; [|neq_var_sn_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var_sn_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3; [|neq_var_sn_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt10; [|neq_var_sn_v].
  clear Hframe Hsc Hpt Htgt9 Htgt4.

  (* C12: ed25519_xyzt_add (R_check ← R_xyzt_v, cPK) *)
  peel_call_seq_sn_v Hexec Hframe Hres.
  destruct Hres as [p_bs [q_bs [Hp [Hq Htgt12]]]].
  pose proof (slot_holds_inj _ _ _ _ Hp Htgt3) as Heq; subst p_bs.
  pose proof (slot_holds_inj _ _ _ _ Hq Htgt11) as Heq; subst q_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var_sn_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hpk_alloc; [|neq_var_sn_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var_sn_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt10; [|neq_var_sn_v].
  clear Hframe Hp Hq Htgt3 Htgt11.

  (* C13: ed25519_compress (check_bytes ← R_check) *)
  peel_call_seq_sn_v Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt13]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt12) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var_sn_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hpk_alloc; [|neq_var_sn_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var_sn_v].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt10; [|neq_var_sn_v].
  clear Hframe Hsrc Htgt12.

  (* C14: bytes_equal_32 (result ← sig, check_bytes) — last call *)
  peel_last_call_sn_v Hexec Hframe Hres.
  destruct Hres as [a_bs [b_bs [Ha [Hb Htgt14]]]].
  pose proof (slot_holds_inj _ _ _ _ Ha Hsig_alloc) as Heq; subst a_bs.
  pose proof (slot_holds_inj _ _ _ _ Hb Htgt13) as Heq; subst b_bs.
  clear Hframe Ha Hb.

  (* Stage C: assembly. *)
  cbn [LE_TBytes loc_var] in Htgt14.
  exists (Z.to_nat len8), dst_bs5.
  unfold schnorr_verify_gallina_lifted.
  exact Htgt14.
Qed.
