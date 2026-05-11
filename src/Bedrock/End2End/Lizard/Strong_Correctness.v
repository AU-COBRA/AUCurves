(** * Lizard Strong_Correctness — strong correctness for
 *    [lizard_inject_rs] and [lizard_extract_rs].
 *
 * Functional postcondition: under [strong_callee_post_lizard] (each
 * leaf returns its Gallina spec AND frames all other tower slots),
 * the output slot after execution equals the lifted Gallina reference
 * applied to the inputs.
 *
 * Mirrors [Bedrock.End2End.XEdDSA.Sign_Strong_Correctness] structurally
 * but in a much simpler form — Lizard's inject / extract bodies are
 * 3-call sequences with NO dynamic-length scalars (no REdLetU64
 * steps), so the strong_callee_post does not need the scalar-frame
 * conjunct from Ed25519/XEdDSA.
 *
 * Architecture:
 *   §1  Per-leaf Gallina specs (Parameters: 6 leaves, length lemmas).
 *   §2  Gallina reference [lizard_inject_gallina] / [lizard_extract_gallina].
 *   §3  [strong_callee_post_lizard]            : per-call obligation.
 *   §4  Frame lemma                            : Qed.
 *   §5  [lizard_inject_strong_correct]         : main theorem (Qed).
 *   §6  [lizard_extract_strong_correct]        : main theorem (Qed).
 *
 * Status (2026-05-11):
 *   §1-§6 closed.  Print Assumptions reports the 6 leaf Gallina specs
 *   as Parameters.  0 Admitteds.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import micromega.Lia.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.Sign_Verify_RustCmd.
Require Import Bedrock.End2End.Ed25519.Sign_Strong_Correctness.
Require Import Bedrock.End2End.Lizard.Inject_RustCmd.
Require Import Bedrock.End2End.Lizard.Extract_RustCmd.
Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* §1. Per-callee Gallina specs                                       *)
(* ================================================================ *)

(** [lizard_pack_spec]: 16 plaintext bytes → 32-byte buffer with the
    plaintext placed in the middle and derived padding around it.  In
    Signal's reference implementation the padding is derived from a
    hash of the plaintext + a domain string; here we keep the spec
    abstract. *)
Parameter lizard_pack_spec : list Byte.byte -> list Byte.byte.
Parameter lizard_pack_spec_len :
  forall input, length input = 16%nat ->
    length (lizard_pack_spec input) = 32%nat.

(** [lizard_unpack_spec]: inverse of [lizard_pack_spec] — 32 bytes →
    middle 16 bytes (the plaintext). *)
Parameter lizard_unpack_spec : list Byte.byte -> list Byte.byte.
Parameter lizard_unpack_spec_len :
  forall input, length input = 32%nat ->
    length (lizard_unpack_spec input) = 16%nat.

(** [elligator2_to_edwards_spec]: 32-byte field element → 200-byte
    Edwards (xyzt) point.  Composes Elligator2 (field → Montgomery)
    with the Montgomery → Edwards isomorphism. *)
Parameter elligator2_to_edwards_spec : list Byte.byte -> list Byte.byte.
Parameter elligator2_to_edwards_spec_len :
  forall input, length input = 32%nat ->
    length (elligator2_to_edwards_spec input) = 200%nat.

(** [edwards_to_elligator2_spec]: inverse — 200-byte Edwards point →
    32-byte field element.  Composes Edwards → Montgomery with the
    Elligator2 inverse map. *)
Parameter edwards_to_elligator2_spec : list Byte.byte -> list Byte.byte.
Parameter edwards_to_elligator2_spec_len :
  forall input, length input = 200%nat ->
    length (edwards_to_elligator2_spec input) = 32%nat.

(** [ristretto_encode_spec]: 200-byte Edwards (xyzt) point → 32-byte
    Ristretto encoding (deterministic canonical serialisation). *)
Parameter ristretto_encode_spec : list Byte.byte -> list Byte.byte.
Parameter ristretto_encode_spec_len :
  forall input, length input = 200%nat ->
    length (ristretto_encode_spec input) = 32%nat.

(** [ristretto_decode_or_fail_spec]: 32-byte Ristretto encoding →
    200-byte Edwards point.  On invalid input the leaf returns a
    recognisable sentinel point (the option type is handled at the
    FFI boundary in the Rust output; the rust_cmd_ed view models the
    leaf as total over its byte domain). *)
Parameter ristretto_decode_or_fail_spec : list Byte.byte -> list Byte.byte.
Parameter ristretto_decode_or_fail_spec_len :
  forall input, length input = 32%nat ->
    length (ristretto_decode_or_fail_spec input) = 200%nat.

(* ================================================================ *)
(* §2. Gallina references                                             *)
(* ================================================================ *)

(** Clean reference for Lizard inject, depending only on the 16-byte
    plaintext. *)
Definition lizard_inject_gallina (pt : list Byte.byte) : list Byte.byte :=
  let packed := lizard_pack_spec pt in
  let xyzt   := elligator2_to_edwards_spec packed in
  ristretto_encode_spec xyzt.

(** Clean reference for Lizard extract. *)
Definition lizard_extract_gallina (rist : list Byte.byte) : list Byte.byte :=
  let xyzt   := ristretto_decode_or_fail_spec rist in
  let packed := edwards_to_elligator2_spec xyzt in
  lizard_unpack_spec packed.

(* ================================================================ *)
(* §3. Strong callee_post predicate                                   *)
(* ================================================================ *)

(** Per-call obligation: the destination slot is the leaf's spec
    applied to the source bytes, and every other tower slot is framed.
    The 6 Lizard leaves all have a uniform shape: one byte-array input,
    one byte-array output, no scalar arguments — much simpler than the
    Ed25519 / XEdDSA callees. *)
Definition strong_callee_post_lizard
           (fname : String.string)
           (args : list located_ed)
           (dst : located_ed)
           (rs1 rs2 : rust_state_ed) : Prop :=
  frames_except rs1 rs2 dst.(loc_var) /\
  match fname, args with
  | "lizard_pack", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (lizard_pack_spec src_bs)
  | "lizard_unpack", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (lizard_unpack_spec src_bs)
  | "elligator2_to_edwards", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (elligator2_to_edwards_spec src_bs)
  | "edwards_to_elligator2", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (edwards_to_elligator2_spec src_bs)
  | "ristretto_encode", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (ristretto_encode_spec src_bs)
  | "ristretto_decode_or_fail", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (ristretto_decode_or_fail_spec src_bs)
  | _, _ => True
  end.

(* ================================================================ *)
(* §4. Frame lemma — Qed                                              *)
(* ================================================================ *)

Lemma strong_callee_post_lizard_frame_other_slots :
  forall fname args dst rs1 rs2 x,
    strong_callee_post_lizard fname args dst rs1 rs2 ->
    x <> dst.(loc_var) ->
    rs_get_tower_ed rs1 x = rs_get_tower_ed rs2 x.
Proof.
  intros fname args dst rs1 rs2 x [Hframe _] Hne.
  apply (Hframe x Hne).
Qed.

(* ================================================================ *)
(* §5. Strong correctness — inject                                    *)
(* ================================================================ *)

(** [neq_var_inject] proves [v_X <> v_Y] for inject's variable names. *)
Ltac neq_var_inject :=
  cbn [LE_TBytes loc_var];
  cbv [v_pt v_out v_buf32 v_xyzt];
  discriminate.

(** Peel one [REdSeq (REdCall ...) rest] cell and destructure its
    [strong_callee_post_lizard] obligation.  No scalar conjunct
    (Lizard has no dynamic-length scalars), so simpler than the
    XEdDSA / Ed25519 analogues. *)
Ltac peel_call_seq_liz H Hframe Hres :=
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
  | Hc : strong_callee_post_lizard _ _ _ _ _ |- _ =>
      destruct Hc as [Hframe Hres]
  end;
  rename Hrest into H.

Ltac peel_last_call_liz H Hframe Hres :=
  inversion H; subst; clear H;
  match goal with
  | Hc : strong_callee_post_lizard _ _ _ _ _ |- _ =>
      destruct Hc as [Hframe Hres]
  end.

Theorem lizard_inject_strong_correct :
  forall (callee_post_n :
            String.string -> list located_ed -> list located_ed ->
            rust_state_ed -> rust_state_ed -> Prop)
         (function_table : function_table_ed)
         (rs1 rs2 : rust_state_ed)
         (pt out_init : list Byte.byte),
    length pt = 16%nat ->
    slot_holds rs1 v_pt pt ->
    slot_holds rs1 v_out out_init ->
    rust_exec_ed strong_callee_post_lizard callee_post_n function_table
                 lizard_inject_rs rs1 rs2 ->
    slot_holds rs2 v_out (lizard_inject_gallina pt).
Proof.
  intros callee_post_n function_table rs1 rs2 pt out_init
         Hpt_len Hpt Hout Hexec.
  unfold lizard_inject_rs in Hexec.

  (* Stage A: peel 2 REdLetZero allocations. *)
  repeat (match goal with
          | H : rust_exec_ed _ _ _ (REdLetZero _ _ _) _ _ |- _ =>
              inversion H; subst; clear H
          end).

  (* Propagate pt + out slots through the 2 fresh allocations. *)
  match goal with
  | H : rust_exec_ed _ _ _ _ ?rs_alloc _ |- _ =>
      assert (Hpt_alloc : slot_holds rs_alloc v_pt pt) by
        (repeat (apply slot_holds_set_tower_other; [discriminate|]); exact Hpt);
      assert (Hout_alloc : slot_holds rs_alloc v_out out_init) by
        (repeat (apply slot_holds_set_tower_other; [discriminate|]); exact Hout);
      rename H into Hexec
  end.
  clear Hpt Hout.

  (* === Stage B: 3 call inversions === *)

  (* C1: lizard_pack (buf32 ← pt) *)
  peel_call_seq_liz Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt1]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hpt_alloc) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hpt_alloc; [|neq_var_inject].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hout_alloc; [|neq_var_inject].
  clear Hframe Hsrc.

  (* C2: elligator2_to_edwards (xyzt ← buf32) *)
  peel_call_seq_liz Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt2]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt1) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hpt_alloc; [|neq_var_inject].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hout_alloc; [|neq_var_inject].
  clear Hframe Hsrc Htgt1.

  (* C3: ristretto_encode (out ← xyzt) — last call *)
  peel_last_call_liz Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt3]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt2) as Heq; subst src_bs.
  clear Hframe Hsrc.

  (* Stage C: assembly. *)
  cbn [LE_TBytes loc_var] in Htgt3.
  unfold lizard_inject_gallina.
  exact Htgt3.
Qed.

(* ================================================================ *)
(* §6. Strong correctness — extract                                   *)
(* ================================================================ *)

(** [neq_var_extract] proves [v_X <> v_Y] for extract's variable names. *)
Ltac neq_var_extract :=
  cbn [LE_TBytes loc_var];
  cbv [v_rist v_pt_out v_xyzt_ex v_buf32_ex];
  discriminate.

Ltac peel_call_seq_lize H Hframe Hres :=
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
  | Hc : strong_callee_post_lizard _ _ _ _ _ |- _ =>
      destruct Hc as [Hframe Hres]
  end;
  rename Hrest into H.

Ltac peel_last_call_lize H Hframe Hres :=
  inversion H; subst; clear H;
  match goal with
  | Hc : strong_callee_post_lizard _ _ _ _ _ |- _ =>
      destruct Hc as [Hframe Hres]
  end.

Theorem lizard_extract_strong_correct :
  forall (callee_post_n :
            String.string -> list located_ed -> list located_ed ->
            rust_state_ed -> rust_state_ed -> Prop)
         (function_table : function_table_ed)
         (rs1 rs2 : rust_state_ed)
         (rist pt_out_init : list Byte.byte),
    length rist = 32%nat ->
    slot_holds rs1 v_rist rist ->
    slot_holds rs1 v_pt_out pt_out_init ->
    rust_exec_ed strong_callee_post_lizard callee_post_n function_table
                 lizard_extract_rs rs1 rs2 ->
    slot_holds rs2 v_pt_out (lizard_extract_gallina rist).
Proof.
  intros callee_post_n function_table rs1 rs2 rist pt_out_init
         Hrist_len Hrist Hpt_out Hexec.
  unfold lizard_extract_rs in Hexec.

  (* Stage A: peel 2 REdLetZero allocations. *)
  repeat (match goal with
          | H : rust_exec_ed _ _ _ (REdLetZero _ _ _) _ _ |- _ =>
              inversion H; subst; clear H
          end).

  (* Propagate rist + pt_out slots through the 2 fresh allocations. *)
  match goal with
  | H : rust_exec_ed _ _ _ _ ?rs_alloc _ |- _ =>
      assert (Hrist_alloc : slot_holds rs_alloc v_rist rist) by
        (repeat (apply slot_holds_set_tower_other; [discriminate|]); exact Hrist);
      assert (Hpt_out_alloc : slot_holds rs_alloc v_pt_out pt_out_init) by
        (repeat (apply slot_holds_set_tower_other; [discriminate|]); exact Hpt_out);
      rename H into Hexec
  end.
  clear Hrist Hpt_out.

  (* === Stage B: 3 call inversions === *)

  (* C1: ristretto_decode_or_fail (xyzt_ex ← rist) *)
  peel_call_seq_lize Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt1]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hrist_alloc) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hrist_alloc; [|neq_var_extract].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hpt_out_alloc; [|neq_var_extract].
  clear Hframe Hsrc.

  (* C2: edwards_to_elligator2 (buf32_ex ← xyzt_ex) *)
  peel_call_seq_lize Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt2]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt1) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hrist_alloc; [|neq_var_extract].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hpt_out_alloc; [|neq_var_extract].
  clear Hframe Hsrc Htgt1.

  (* C3: lizard_unpack (pt_out ← buf32_ex) — last call *)
  peel_last_call_lize Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt3]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt2) as Heq; subst src_bs.
  clear Hframe Hsrc.

  (* Stage C: assembly. *)
  cbn [LE_TBytes loc_var] in Htgt3.
  unfold lizard_extract_gallina.
  exact Htgt3.
Qed.
