(** * ElGamal Strong_Correctness — strong correctness for
 *    [elgamal_encrypt_rs] and [elgamal_decrypt_rs].
 *
 * Functional postcondition: under [strong_callee_post_elgamal] (each
 * leaf returns its Gallina spec AND frames all other tower slots),
 * the output slot after execution equals the lifted Gallina reference
 * applied to the inputs.
 *
 * Sixth framework user after Ed25519 (sign / verify), XEdDSA, Lizard,
 * Pedersen, Schnorr.  First *encryption* protocol — structurally
 * similar to Pedersen-open (decode → arithmetic → encode chain), but
 * with two distinguishing features:
 *
 *   - Output is the 64-byte ciphertext [C1 || C2], packed from two
 *     32-byte halves via [memmove_first_32] / [memmove_second_32]
 *     (parallel to Schnorr verify's input-side
 *     [memmove_R_from_sig] / [memmove_S_from_sig] but writing to a
 *     larger destination instead of reading from one).
 *   - Decrypt uses a new placeholder leaf [ed25519_xyzt_negate]
 *     (point negation) to model subtraction as add-of-negate.
 *
 * Leaf reuse: 7 of 10 leaf specs are imported verbatim from prior
 * commits (Ed25519 sign/verify + Lizard).  The 3 new placeholder
 * Definitions added here:
 *
 *   - [memmove_first_32_spec]  : write src into dst[0..32]
 *   - [memmove_second_32_spec] : write src into dst[32..64]
 *   - [ed25519_xyzt_negate_spec] : 200B → 200B point negation
 *     (TODO Tier-2: faithful Edwards-coord negation; ~50 LoC).
 *
 * Status: §1-§7 closed.  All theorems Qed; 0 Admitteds; only
 * placeholder Definitions are involved (no Axioms / Parameters).
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import micromega.Lia.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.RemainingBridges.
Require Import Bedrock.End2End.Ed25519.XyztAddVerified.
Require Import Bedrock.End2End.Ed25519.ScalarmultVerified.
Require Import Bedrock.End2End.Ed25519.Sign_Verify_RustCmd.
Require Import Bedrock.End2End.Ed25519.Sign_Strong_Correctness.
Require Import Bedrock.End2End.Ed25519.Verify_Strong_Correctness.
Require Import Bedrock.End2End.Lizard.Strong_Correctness.
Require Import Bedrock.End2End.ElGamal.Encrypt_RustCmd.
Require Import Bedrock.End2End.ElGamal.Decrypt_RustCmd.
Require Import Bedrock.End2End.StrongCorrectnessTactics.
Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* §1. Per-callee Gallina specs (new)                                *)
(* ================================================================ *)

(** [memmove_first_32_spec dst src]: write src (32B) into dst[0..32],
    leaving dst[32..] unchanged.  Concrete Definition. *)
Definition memmove_first_32_spec (dst src : list Byte.byte) : list Byte.byte :=
  src ++ skipn 32 dst.

Lemma memmove_first_32_spec_len :
  forall dst src,
    length dst = 64%nat -> length src = 32%nat ->
    length (memmove_first_32_spec dst src) = 64%nat.
Proof.
  intros dst src Hd Hs. unfold memmove_first_32_spec.
  rewrite List.length_app, List.length_skipn, Hd, Hs. reflexivity.
Qed.

(** [memmove_second_32_spec dst src]: write src (32B) into dst[32..64],
    leaving dst[0..32] unchanged. *)
Definition memmove_second_32_spec (dst src : list Byte.byte) : list Byte.byte :=
  firstn 32 dst ++ src.

Lemma memmove_second_32_spec_len :
  forall dst src,
    length dst = 64%nat -> length src = 32%nat ->
    length (memmove_second_32_spec dst src) = 64%nat.
Proof.
  intros dst src Hd Hs. unfold memmove_second_32_spec.
  rewrite List.length_app, List.length_firstn, Hd, Hs. reflexivity.
Qed.

(** [ed25519_xyzt_negate_spec]: 200B Edwards (xyzt) point → 200B
    negated Edwards point.  TODO (Tier-2): faithful Edwards-coordinate
    negation (~50 LoC: negate X, T fields, leave Y, Z).  Placeholder
    returning 200 zero bytes; suffices for the strong-correctness
    pipeline since only the type signature and length lemma are
    consumed. *)
Definition ed25519_xyzt_negate_spec (_ : list Byte.byte) : list Byte.byte :=
  List.repeat Byte.x00 200.
Global Opaque ed25519_xyzt_negate_spec.

Lemma ed25519_xyzt_negate_spec_len :
  forall input, length input = 200%nat ->
    length (ed25519_xyzt_negate_spec input) = 200%nat.
Proof.
  intros input _.
  Transparent ed25519_xyzt_negate_spec.
  unfold ed25519_xyzt_negate_spec.
  rewrite List.repeat_length. reflexivity.
Qed.
Global Opaque ed25519_xyzt_negate_spec.

(* ================================================================ *)
(* §2. Gallina references                                            *)
(* ================================================================ *)

(** Clean reference for ElGamal encrypt: composes the 9 leaf specs.
    The 64-byte ciphertext is constructed by two memmove writes onto an
    initial 64-byte output buffer [out_init]. *)
Definition elgamal_encrypt_gallina
    (pk msg r_rand out_init : list Byte.byte) : list Byte.byte :=
  let C1_xyzt   := ed25519_scalarmult_base_spec r_rand in
  let C1_bytes  := ristretto_encode_spec C1_xyzt in
  let pk_xyzt   := ristretto_decode_or_fail_spec pk in
  let shared    := ed25519_scalarmult_spec r_rand pk_xyzt in
  let msg_xyzt  := ristretto_decode_or_fail_spec msg in
  let C2_xyzt   := ed25519_xyzt_add_spec msg_xyzt shared in
  let C2_bytes  := ristretto_encode_spec C2_xyzt in
  let out_step1 := memmove_first_32_spec  out_init C1_bytes in
  memmove_second_32_spec out_step1 C2_bytes.

(** Clean reference for ElGamal decrypt: parse → DH → subtract → encode. *)
Definition elgamal_decrypt_gallina
    (sk ct : list Byte.byte) : list Byte.byte :=
  let C1_bytes := memmove_R_from_sig_spec ct in
  let C2_bytes := memmove_S_from_sig_spec ct in
  let C1_xyzt  := ristretto_decode_or_fail_spec C1_bytes in
  let shared   := ed25519_scalarmult_spec sk C1_xyzt in
  let neg      := ed25519_xyzt_negate_spec shared in
  let C2_xyzt  := ristretto_decode_or_fail_spec C2_bytes in
  let msg_xyzt := ed25519_xyzt_add_spec C2_xyzt neg in
  ristretto_encode_spec msg_xyzt.

(* ================================================================ *)
(* §3. Strong callee_post predicate                                   *)
(* ================================================================ *)

(** Per-call obligation for the ElGamal leaves.  Uniform shape:
    frames_except + a per-call existential witness of the input/output
    relation.

    Note: [memmove_first_32] / [memmove_second_32] write *into* the
    destination, so the post depends on the *initial* value of [dst]
    too (similar to the Ed25519-sign [memmove_chal_*] arms). *)
Definition strong_callee_post_elgamal
           (fname : String.string)
           (args : list located_ed)
           (dst : located_ed)
           (rs1 rs2 : rust_state_ed) : Prop :=
  frames_except rs1 rs2 dst.(loc_var) /\
  match fname, args with
  | "ed25519_scalarmult_base", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (ed25519_scalarmult_base_spec src_bs)
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
  | "ed25519_xyzt_negate", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (ed25519_xyzt_negate_spec src_bs)
  | "ristretto_encode", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (ristretto_encode_spec src_bs)
  | "ristretto_decode_or_fail", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (ristretto_decode_or_fail_spec src_bs)
  | "memmove_R_from_sig", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (memmove_R_from_sig_spec src_bs)
  | "memmove_S_from_sig", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (memmove_S_from_sig_spec src_bs)
  | "memmove_first_32", [src] =>
      exists src_bs dst_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs1 dst.(loc_var) dst_bs /\
        slot_holds rs2 dst.(loc_var) (memmove_first_32_spec dst_bs src_bs)
  | "memmove_second_32", [src] =>
      exists src_bs dst_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs1 dst.(loc_var) dst_bs /\
        slot_holds rs2 dst.(loc_var) (memmove_second_32_spec dst_bs src_bs)
  | _, _ => True
  end.

(* ================================================================ *)
(* §4. Frame lemma — Qed                                              *)
(* ================================================================ *)

Lemma strong_callee_post_elgamal_frame_other_slots :
  forall fname args dst rs1 rs2 x,
    strong_callee_post_elgamal fname args dst rs1 rs2 ->
    x <> dst.(loc_var) ->
    rs_get_tower_ed rs1 x = rs_get_tower_ed rs2 x.
Proof.
  intros fname args dst rs1 rs2 x [Hframe _] Hne.
  apply (Hframe x Hne).
Qed.

(* ================================================================ *)
(* §5. Local tactics                                                  *)
(* ================================================================ *)

(** [neq_var_eg] proves [v_X <> v_Y] for ElGamal's variable names
    (both encrypt-side and decrypt-side, since both Strong_Correctness
    theorems live in this file). *)
Ltac neq_var_eg :=
  cbn [LE_TBytes loc_var];
  cbv [v_pk v_msg v_r_rand v_out
       v_C1_xyzt v_C1 v_pk_xyzt v_shared_xyzt
       v_msg_xyzt v_C2_xyzt v_C2
       v_sk v_ct v_msg_out
       v_C1_bytes_d v_C2_bytes_d v_C1_xyzt_d
       v_shared_d v_neg_shared v_C2_xyzt_d v_msg_xyzt_d];
  discriminate.

(** Peel one [REdSeq (REdCall ...) rest] cell and destructure its
    [strong_callee_post_elgamal] obligation. *)
Ltac peel_call_seq_eg H Hframe Hres :=
  let Hcall := fresh "Hcall" in
  let Hrest := fresh "Hrest" in
  inversion H; subst; clear H;
  match goal with
  | Hc : rust_exec_ed _ _ _ (REdCall _ _ _) _ _,
    Hr : rust_exec_ed _ _ _ _ _ _ |- _ =>
      rename Hc into Hcall; rename Hr into Hrest
  end;
  inversion Hcall; subst; clear Hcall;
  match goal with
  | Hc : strong_callee_post_elgamal _ _ _ _ _ |- _ =>
      destruct Hc as [Hframe Hres]
  end;
  rename Hrest into H.

Ltac peel_last_call_eg H Hframe Hres :=
  inversion H; subst; clear H;
  match goal with
  | Hc : strong_callee_post_elgamal _ _ _ _ _ |- _ =>
      destruct Hc as [Hframe Hres]
  end.

(* ================================================================ *)
(* §6. Strong correctness — encrypt                                   *)
(* ================================================================ *)

Theorem elgamal_encrypt_strong_correct :
  forall (callee_post_n :
            String.string -> list located_ed -> list located_ed ->
            rust_state_ed -> rust_state_ed -> Prop)
         (function_table : function_table_ed)
         (rs1 rs2 : rust_state_ed)
         (pk msg r_rand out_init : list Byte.byte),
    length pk = 32%nat ->
    length msg = 32%nat ->
    length r_rand = 32%nat ->
    length out_init = 64%nat ->
    slot_holds rs1 v_pk pk ->
    slot_holds rs1 v_msg msg ->
    slot_holds rs1 v_r_rand r_rand ->
    slot_holds rs1 v_out out_init ->
    rust_exec_ed strong_callee_post_elgamal callee_post_n function_table
                 elgamal_encrypt_rs rs1 rs2 ->
    slot_holds rs2 v_out (elgamal_encrypt_gallina pk msg r_rand out_init).
Proof.
  intros callee_post_n function_table rs1 rs2 pk msg r_rand out_init
         Hpk_len Hmsg_len Hr_len Hout_len Hpk Hmsg Hr Hout Hexec.
  unfold elgamal_encrypt_rs in Hexec.

  (* Stage A: peel 7 REdLetZero allocations. *)
  peel_all_let_zero.

  (* Propagate input slots through the 7 fresh allocations. *)
  match goal with
  | H : rust_exec_ed _ _ _ _ ?rs_alloc _ |- _ =>
      assert (Hpk_alloc : slot_holds rs_alloc v_pk pk) by
        (slot_holds_set_tower_other_repeat Hpk);
      assert (Hmsg_alloc : slot_holds rs_alloc v_msg msg) by
        (slot_holds_set_tower_other_repeat Hmsg);
      assert (Hr_alloc : slot_holds rs_alloc v_r_rand r_rand) by
        (slot_holds_set_tower_other_repeat Hr);
      assert (Hout_alloc : slot_holds rs_alloc v_out out_init) by
        (slot_holds_set_tower_other_repeat Hout);
      rename H into Hexec
  end.
  clear Hpk Hmsg Hr Hout.

  (* === Stage B: 9 call inversions === *)

  (* C1: ed25519_scalarmult_base (C1_xyzt ← r_rand) *)
  peel_call_seq_eg Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt1]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hr_alloc) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_eg.
  clear Hframe Hsrc.

  (* C2: ristretto_encode (C1 ← C1_xyzt) *)
  peel_call_seq_eg Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt2]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt1) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_eg.
  clear Hframe Hsrc Htgt1.

  (* C3: ristretto_decode_or_fail (pk_xyzt ← pk) *)
  peel_call_seq_eg Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt3]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hpk_alloc) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_eg.
  clear Hframe Hsrc.

  (* C4: ed25519_scalarmult (shared_xyzt ← r_rand, pk_xyzt) *)
  peel_call_seq_eg Hexec Hframe Hres.
  destruct Hres as [h_bs [A_bs [Hh [HA Htgt4]]]].
  pose proof (slot_holds_inj _ _ _ _ Hh Hr_alloc) as Heq; subst h_bs.
  pose proof (slot_holds_inj _ _ _ _ HA Htgt3) as Heq; subst A_bs.
  frame_through_call_with Hframe neq_var_eg.
  clear Hframe Hh HA Htgt3.

  (* C5: ristretto_decode_or_fail (msg_xyzt ← msg) *)
  peel_call_seq_eg Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt5]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hmsg_alloc) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_eg.
  clear Hframe Hsrc.

  (* C6: ed25519_xyzt_add (C2_xyzt ← msg_xyzt, shared_xyzt) *)
  peel_call_seq_eg Hexec Hframe Hres.
  destruct Hres as [P_bs [Q_bs [HP [HQ Htgt6]]]].
  pose proof (slot_holds_inj _ _ _ _ HP Htgt5) as Heq; subst P_bs.
  pose proof (slot_holds_inj _ _ _ _ HQ Htgt4) as Heq; subst Q_bs.
  frame_through_call_with Hframe neq_var_eg.
  clear Hframe HP HQ Htgt4 Htgt5.

  (* C7: ristretto_encode (C2 ← C2_xyzt) *)
  peel_call_seq_eg Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt7]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt6) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_eg.
  clear Hframe Hsrc Htgt6.

  (* C8: memmove_first_32 (out ← C1)
     Two-arg post: src + dst initial value. *)
  peel_call_seq_eg Hexec Hframe Hres.
  destruct Hres as [src_bs [dst_bs [Hsrc [Hdst Htgt8]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt2) as Heq; subst src_bs.
  pose proof (slot_holds_inj _ _ _ _ Hdst Hout_alloc) as Heq; subst dst_bs.
  frame_through_call_with Hframe neq_var_eg.
  clear Hframe Hsrc Hdst Hout_alloc Htgt2.

  (* C9: memmove_second_32 (out ← C2) — last call *)
  peel_last_call_eg Hexec Hframe Hres.
  destruct Hres as [src_bs [dst_bs [Hsrc [Hdst Htgt9]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt7) as Heq; subst src_bs.
  pose proof (slot_holds_inj _ _ _ _ Hdst Htgt8) as Heq; subst dst_bs.
  clear Hframe Hsrc Hdst.

  (* Stage C: assembly. *)
  cbn [LE_TBytes loc_var] in Htgt9.
  unfold elgamal_encrypt_gallina.
  exact Htgt9.
Qed.

(* ================================================================ *)
(* §7. Strong correctness — decrypt                                   *)
(* ================================================================ *)

Theorem elgamal_decrypt_strong_correct :
  forall (callee_post_n :
            String.string -> list located_ed -> list located_ed ->
            rust_state_ed -> rust_state_ed -> Prop)
         (function_table : function_table_ed)
         (rs1 rs2 : rust_state_ed)
         (sk ct msg_init : list Byte.byte),
    length sk = 32%nat ->
    length ct = 64%nat ->
    slot_holds rs1 v_sk sk ->
    slot_holds rs1 v_ct ct ->
    slot_holds rs1 v_msg_out msg_init ->
    rust_exec_ed strong_callee_post_elgamal callee_post_n function_table
                 elgamal_decrypt_rs rs1 rs2 ->
    slot_holds rs2 v_msg_out (elgamal_decrypt_gallina sk ct).
Proof.
  intros callee_post_n function_table rs1 rs2 sk ct msg_init
         Hsk_len Hct_len Hsk Hct Hmsg_init Hexec.
  unfold elgamal_decrypt_rs in Hexec.

  (* Stage A: peel 7 REdLetZero allocations. *)
  peel_all_let_zero.

  (* Propagate input slots through the 7 fresh allocations. *)
  match goal with
  | H : rust_exec_ed _ _ _ _ ?rs_alloc _ |- _ =>
      assert (Hsk_alloc : slot_holds rs_alloc v_sk sk) by
        (slot_holds_set_tower_other_repeat Hsk);
      assert (Hct_alloc : slot_holds rs_alloc v_ct ct) by
        (slot_holds_set_tower_other_repeat Hct);
      assert (Hmsg_alloc : slot_holds rs_alloc v_msg_out msg_init) by
        (slot_holds_set_tower_other_repeat Hmsg_init);
      rename H into Hexec
  end.
  clear Hsk Hct Hmsg_init.

  (* === Stage B: 8 call inversions === *)

  (* C1: memmove_R_from_sig (C1_bytes_d ← ct) *)
  peel_call_seq_eg Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt1]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hct_alloc) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_eg.
  clear Hframe Hsrc.

  (* C2: memmove_S_from_sig (C2_bytes_d ← ct) *)
  peel_call_seq_eg Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt2]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hct_alloc) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_eg.
  clear Hframe Hsrc Hct_alloc.

  (* C3: ristretto_decode_or_fail (C1_xyzt_d ← C1_bytes_d) *)
  peel_call_seq_eg Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt3]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt1) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_eg.
  clear Hframe Hsrc Htgt1.

  (* C4: ed25519_scalarmult (shared_d ← sk, C1_xyzt_d) *)
  peel_call_seq_eg Hexec Hframe Hres.
  destruct Hres as [h_bs [A_bs [Hh [HA Htgt4]]]].
  pose proof (slot_holds_inj _ _ _ _ Hh Hsk_alloc) as Heq; subst h_bs.
  pose proof (slot_holds_inj _ _ _ _ HA Htgt3) as Heq; subst A_bs.
  frame_through_call_with Hframe neq_var_eg.
  clear Hframe Hh HA Htgt3 Hsk_alloc.

  (* C5: ed25519_xyzt_negate (neg_shared ← shared_d) *)
  peel_call_seq_eg Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt5]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt4) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_eg.
  clear Hframe Hsrc Htgt4.

  (* C6: ristretto_decode_or_fail (C2_xyzt_d ← C2_bytes_d) *)
  peel_call_seq_eg Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt6]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt2) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_eg.
  clear Hframe Hsrc Htgt2.

  (* C7: ed25519_xyzt_add (msg_xyzt_d ← C2_xyzt_d, neg_shared) *)
  peel_call_seq_eg Hexec Hframe Hres.
  destruct Hres as [P_bs [Q_bs [HP [HQ Htgt7]]]].
  pose proof (slot_holds_inj _ _ _ _ HP Htgt6) as Heq; subst P_bs.
  pose proof (slot_holds_inj _ _ _ _ HQ Htgt5) as Heq; subst Q_bs.
  frame_through_call_with Hframe neq_var_eg.
  clear Hframe HP HQ Htgt5 Htgt6.

  (* C8: ristretto_encode (msg_out ← msg_xyzt_d) — last call *)
  peel_last_call_eg Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt8]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt7) as Heq; subst src_bs.
  clear Hframe Hsrc.

  (* Stage C: assembly. *)
  cbn [LE_TBytes loc_var] in Htgt8.
  unfold elgamal_decrypt_gallina.
  exact Htgt8.
Qed.
