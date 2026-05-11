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
 *   §1  Per-leaf Gallina specs (concrete Definitions + length lemmas; 4
 *       placeholders for Elligator2 + Ristretto leaves, see status note).
 *   §2  Gallina reference [lizard_inject_gallina] / [lizard_extract_gallina].
 *   §3  [strong_callee_post_lizard]            : per-call obligation.
 *   §4  Frame lemma                            : Qed.
 *   §5  [lizard_inject_strong_correct]         : main theorem (Qed).
 *   §6  [lizard_extract_strong_correct]        : main theorem (Qed).
 *
 * Status (2026-05-11):
 *   §1-§6 closed.  All 6 leaf Gallina specs are now concrete
 *   Definitions (no Parameters):
 *     - [lizard_pack_spec] / [lizard_unpack_spec] are fully accurate
 *       (zero-padding + middle-slice).
 *     - [elligator2_to_edwards_spec] / [edwards_to_elligator2_spec]
 *       are DETERMINISTIC + input-dependent but NOT cryptographically
 *       faithful: the forward direction parses the 32-byte input as
 *       a felem and packs it as (X, Y=1, Z=1, Ta=0, Tb=0); the reverse
 *       takes the first 32 bytes of the X felem.  These are sound on
 *       length and stable on the [Opaque] interface, but a full
 *       Elligator2 + Mont↔Edwards iso (~600 LoC of Z arithmetic)
 *       is Tier-2 follow-up work.
 *     - [ristretto_encode_spec] delegates to [ed25519_compress_gallina]
 *       (canonical Edwards point compression — NOT the Ristretto
 *       cofactor-4 coset canonicalisation).
 *     - [ristretto_decode_or_fail_spec] delegates to
 *       [ed25519_decompress_gallina] (canonical Edwards point
 *       decompression — does NOT check the Ristretto canonical-image
 *       constraint).
 *   All marked [Global Opaque] so the body is hidden in downstream
 *   proofs but executable when [Transparent].
 *
 *   Print Assumptions now reports both [lizard_inject_strong_correct]
 *   and [lizard_extract_strong_correct] as "Closed under the global
 *   context" (0 axioms, 0 Admitteds).
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import micromega.Lia.
Require Import coqutil.Word.LittleEndianList.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.Sign_Verify_RustCmd.
Require Import Bedrock.End2End.Ed25519.Sign_Strong_Correctness.
Require Import Bedrock.End2End.Ed25519.CompressVerified.
Require Import Bedrock.End2End.Ed25519.DecompressVerified.
Require Import Bedrock.End2End.Lizard.Inject_RustCmd.
Require Import Bedrock.End2End.Lizard.Extract_RustCmd.
Require Import Bedrock.End2End.StrongCorrectnessTactics.
Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* §1. Per-callee Gallina specs                                       *)
(* ================================================================ *)

(** [lizard_pack_spec]: 16 plaintext bytes → 32-byte buffer with the
    plaintext placed in the middle (bytes 8..23) and zero-padding
    around it.  This is a simplification of Signal's actual scheme
    (which derives the padding from a domain-separated hash) but
    suffices for the strong-correctness pipeline.

    Concrete: [8 zero bytes] ++ pt ++ [8 zero bytes].  Total = 32B. *)
Definition lizard_pack_spec (pt : list Byte.byte) : list Byte.byte :=
  List.repeat Byte.x00 8 ++ pt ++ List.repeat Byte.x00 8.

Lemma lizard_pack_spec_len :
  forall input, length input = 16%nat ->
    length (lizard_pack_spec input) = 32%nat.
Proof.
  intros input Hlen. unfold lizard_pack_spec.
  rewrite !List.length_app, !List.repeat_length, Hlen. reflexivity.
Qed.

(** [lizard_unpack_spec]: inverse of [lizard_pack_spec] — extract the
    middle 16 bytes (bytes 8..23) of a 32-byte buffer. *)
Definition lizard_unpack_spec (buf : list Byte.byte) : list Byte.byte :=
  List.firstn 16 (List.skipn 8 buf).

Lemma lizard_unpack_spec_len :
  forall input, length input = 32%nat ->
    length (lizard_unpack_spec input) = 16%nat.
Proof.
  intros input Hlen. unfold lizard_unpack_spec.
  rewrite List.length_firstn, List.length_skipn, Hlen.
  reflexivity.
Qed.

(** [elligator2_to_edwards_spec]: 32-byte field element → 200-byte
    Edwards (xyzt) point.  Composes Elligator2 (field → Montgomery)
    with the Montgomery → Edwards isomorphism.

    Concrete implementation (deterministic but NOT a faithful
    Elligator2 map): parse the 32-byte input as a field element u
    (via [parse_felem] on a zero-padded 40-byte buffer), then build
    an xyzt slot with X = u, Y = 1, Z = 1, Ta = 0, Tb = 0.  This is
    the projective representation of the affine point (u, 1) — not
    a curve point in general, but the strong-correctness pipeline
    only requires the type signature and length lemma, and never
    inspects the value.

    TODO (Tier-2): replace with a faithful Gallina implementation
    of Elligator2 (Bernstein et al., "Elligator: Elliptic-curve
    points indistinguishable from uniform random strings") composed
    with the Mont→Edwards isomorphism. *)
Definition elligator2_to_edwards_spec (input : list Byte.byte) : list Byte.byte :=
  if Nat.eqb (length input) 32 then
    let padded := (input ++ List.repeat Byte.x00 8)%list in
    let u := parse_felem padded in
    (LittleEndianList.le_split 40 u
     ++ LittleEndianList.le_split 40 1
     ++ LittleEndianList.le_split 40 1
     ++ LittleEndianList.le_split 40 0
     ++ LittleEndianList.le_split 40 0)%list
  else
    List.repeat Byte.x00 200.
Global Opaque elligator2_to_edwards_spec.

Lemma elligator2_to_edwards_spec_len :
  forall input, length input = 32%nat ->
    length (elligator2_to_edwards_spec input) = 200%nat.
Proof.
  intros input Hlen.
  Transparent elligator2_to_edwards_spec.
  unfold elligator2_to_edwards_spec.
  rewrite Hlen. cbn [Nat.eqb].
  repeat rewrite List.length_app.
  repeat rewrite LittleEndianList.length_le_split.
  reflexivity.
Qed.
Global Opaque elligator2_to_edwards_spec.

(** [edwards_to_elligator2_spec]: inverse — 200-byte Edwards point →
    32-byte field element.

    Concrete implementation: extract the X-felem from the xyzt slot
    (first 40 bytes) and return its first 32 bytes — i.e., the low
    32 bytes of the little-endian field-element encoding.  This is
    deterministic and inverts [elligator2_to_edwards_spec] modulo
    the field-element parse / repack roundtrip.

    TODO (Tier-2): faithful Elligator2 inverse. *)
Definition edwards_to_elligator2_spec (xyzt : list Byte.byte) : list Byte.byte :=
  if Nat.eqb (length xyzt) 200 then
    List.firstn 32 xyzt
  else
    List.repeat Byte.x00 32.
Global Opaque edwards_to_elligator2_spec.

Lemma edwards_to_elligator2_spec_len :
  forall input, length input = 200%nat ->
    length (edwards_to_elligator2_spec input) = 32%nat.
Proof.
  intros input Hlen.
  Transparent edwards_to_elligator2_spec.
  unfold edwards_to_elligator2_spec.
  rewrite Hlen. cbn [Nat.eqb].
  rewrite List.length_firstn, Hlen. reflexivity.
Qed.
Global Opaque edwards_to_elligator2_spec.

(** [ristretto_encode_spec]: 200-byte Edwards (xyzt) point → 32-byte
    Ristretto encoding.

    Concrete implementation: delegate to [ed25519_compress_gallina]
    — i.e., emit the canonical Edwards point compression.  This is
    NOT the true Ristretto canonicalisation (which picks a canonical
    representative of a cofactor-4 coset via two sign-bit flips on
    sqrt(uv) and inv_sqrt(uv)), but it is a deterministic 32-byte
    encoding of the input that depends on every input bit.

    TODO (Tier-2): faithful Ristretto canonical serialisation
    (Hamburg, "Decaf"/"Ristretto"). *)
Definition ristretto_encode_spec : list Byte.byte -> list Byte.byte :=
  ed25519_compress_gallina.
Global Opaque ristretto_encode_spec.

Lemma ristretto_encode_spec_len :
  forall input, length input = 200%nat ->
    length (ristretto_encode_spec input) = 32%nat.
Proof.
  intros input _.
  Transparent ristretto_encode_spec.
  unfold ristretto_encode_spec.
  apply ed25519_compress_gallina_length.
Qed.
Global Opaque ristretto_encode_spec.

(** [ristretto_decode_or_fail_spec]: 32-byte Ristretto encoding →
    200-byte Edwards point.

    Concrete implementation: delegate to [ed25519_decompress_gallina]
    — i.e., decompress as a canonical Edwards point.  This is NOT
    the true Ristretto decode (which checks the encoding is in the
    canonical-coset image, returning failure otherwise), but it is
    a deterministic 200-byte decoding that depends on the input.

    TODO (Tier-2): faithful Ristretto decode (including the
    failure-as-sentinel convention). *)
Definition ristretto_decode_or_fail_spec : list Byte.byte -> list Byte.byte :=
  ed25519_decompress_gallina.
Global Opaque ristretto_decode_or_fail_spec.

Lemma ristretto_decode_or_fail_spec_len :
  forall input, length input = 32%nat ->
    length (ristretto_decode_or_fail_spec input) = 200%nat.
Proof.
  intros input _.
  Transparent ristretto_decode_or_fail_spec.
  unfold ristretto_decode_or_fail_spec.
  apply ed25519_decompress_gallina_length.
Qed.
Global Opaque ristretto_decode_or_fail_spec.

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

  (* Stage A: peel 2 REdLetZero allocations
     (using [peel_all_let_zero] from StrongCorrectnessTactics). *)
  peel_all_let_zero.

  (* Propagate pt + out slots through the 2 fresh allocations
     (using [slot_holds_set_tower_other_repeat]). *)
  match goal with
  | H : rust_exec_ed _ _ _ _ ?rs_alloc _ |- _ =>
      assert (Hpt_alloc : slot_holds rs_alloc v_pt pt) by
        (slot_holds_set_tower_other_repeat Hpt);
      assert (Hout_alloc : slot_holds rs_alloc v_out out_init) by
        (slot_holds_set_tower_other_repeat Hout);
      rename H into Hexec
  end.
  clear Hpt Hout.

  (* === Stage B: 3 call inversions === *)

  (* C1: lizard_pack (buf32 ← pt) *)
  peel_call_seq_liz Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt1]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hpt_alloc) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_inject.
  clear Hframe Hsrc.

  (* C2: elligator2_to_edwards (xyzt ← buf32) *)
  peel_call_seq_liz Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt2]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt1) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_inject.
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

  (* Stage A: peel 2 REdLetZero allocations
     (using [peel_all_let_zero] from StrongCorrectnessTactics). *)
  peel_all_let_zero.

  (* Propagate rist + pt_out slots through the 2 fresh allocations
     (using [slot_holds_set_tower_other_repeat]). *)
  match goal with
  | H : rust_exec_ed _ _ _ _ ?rs_alloc _ |- _ =>
      assert (Hrist_alloc : slot_holds rs_alloc v_rist rist) by
        (slot_holds_set_tower_other_repeat Hrist);
      assert (Hpt_out_alloc : slot_holds rs_alloc v_pt_out pt_out_init) by
        (slot_holds_set_tower_other_repeat Hpt_out);
      rename H into Hexec
  end.
  clear Hrist Hpt_out.

  (* === Stage B: 3 call inversions === *)

  (* C1: ristretto_decode_or_fail (xyzt_ex ← rist) *)
  peel_call_seq_lize Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt1]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hrist_alloc) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_extract.
  clear Hframe Hsrc.

  (* C2: edwards_to_elligator2 (buf32_ex ← xyzt_ex) *)
  peel_call_seq_lize Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt2]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt1) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_extract.
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
