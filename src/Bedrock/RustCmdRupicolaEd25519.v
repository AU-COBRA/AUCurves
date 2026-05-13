(** * RustCmdRupicolaEd25519 — Tier-4 protocol-level compile lemmas
 *
 * Sugar lemmas over the 10 core compile lemmas in [RustCmdRupicola.v],
 * tuned for canonical Ed25519 / Signal-protocol sub-patterns.  Each
 * Tier-4 lemma packages 2-3 [REdCall]s + a [REdSeq] skeleton into a
 * single compile rule whose obligations are spelled in terms of
 * [strong_callee_post]'s per-leaf branches (cf. [Sign_Strong_Correctness.v]).
 *
 * Three Tier-4 lemmas:
 *
 *   1. [compile_red_clamp_then_scalarmult_base]
 *        Copy 32-byte prefix of [h_full] into [a_var], clamp [a_var]
 *        in place, then [ed25519_scalarmult_base] [a_var] into
 *        [A_xyzt_var].  3 calls -> 1 compile rule.  Matches RFC 8032
 *        sign steps 2-4.
 *
 *   2. [compile_red_sha512_then_reduce]
 *        SHA-512 an input then reduce mod L.  Used 2x in sign + 1x
 *        in verify.  2 calls -> 1 compile rule.
 *
 *   3. [compile_red_concat_chal_R_M] / [_simple]
 *        Concatenate two byte buffers via two memmoves.  Two
 *        instantiations matching distinct [strong_callee_post]
 *        branches: [memmove_chal_R + memmove_chal_M] (canonical
 *        chal-buffer pattern) and [memmove_chal_R + memmove_nonce_msg]
 *        (nonce-buffer pattern).
 *
 * Each Tier-4 lemma composes [compile_red_seq] + [compile_red_call]
 * (both Qed in [RustCmdRupicola.v]).  Each [compile_red_call]
 * obligation is discharged by destructing the relevant branch of
 * [strong_callee_post].
 *
 * Status (2026-05-10): all four Qed.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.RustCmdRupicola.
Require Import Bedrock.End2End.Ed25519.RemainingBridges.
Require Import Bedrock.End2End.Ed25519.Sign_Strong_Correctness.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Section Ed25519Tier4.
  Context (callee_post_n : String.string -> list located_ed -> list located_ed ->
                           rust_state_ed -> rust_state_ed -> Prop).
  Context (function_table : function_table_ed).

(* ================================================================ *)
(* §1. Tier-4 compile lemma: clamp + scalarmult_base                  *)
(* ================================================================ *)

(** **[compile_red_clamp_then_scalarmult_base]**
 *
 *  Given a 64-byte slot [h_full_var] containing [h_full] and a fresh
 *  [a_var] (32 bytes) and [A_xyzt_var] (200 bytes), the canonical
 *  RFC 8032 sign-step "load+clamp+scalarmult-base" sub-protocol
 *  compiles to a single [pred] obligation evaluated on the
 *  post-state where:
 *      [a_var]      holds [clamp_64_spec (memmove_a_from_h_spec h_full)]
 *      [A_xyzt_var] holds [ed25519_scalarmult_base_spec
 *                            (clamp_64_spec (memmove_a_from_h_spec h_full))]
 *
 *  Side condition: [a_var <> A_xyzt_var] so the [a_var] result
 *  survives the third call's frame.
 *
 *  The post-state expressions match the strong_callee_post branches
 *  for [memmove_a_from_h], [clamp_64], [ed25519_scalarmult_base]
 *  exactly. *)
Lemma compile_red_clamp_then_scalarmult_base :
  forall (rs : rust_state_ed)
         (h_full_var a_var A_xyzt_var : var)
         (h_full : list Byte.byte) (pred : rpred),
    slot_holds rs h_full_var h_full ->
    Datatypes.length h_full = 64%nat ->
    a_var <> A_xyzt_var ->
    (forall rs3,
        slot_holds rs3 a_var
          (clamp_64_spec (memmove_a_from_h_spec h_full)) ->
        slot_holds rs3 A_xyzt_var
          (ed25519_scalarmult_base_spec
             (clamp_64_spec (memmove_a_from_h_spec h_full))) ->
        pred rs3) ->
    rhoare strong_callee_post callee_post_n function_table rs
      (REdSeq (REdCall "memmove_a_from_h"
                 {| loc_var := a_var; loc_type := TBytes 32 |}
                 [{| loc_var := h_full_var; loc_type := TBytes 64 |}])
       (REdSeq (REdCall "clamp_64"
                 {| loc_var := a_var; loc_type := TBytes 32 |}
                 [])
              (REdCall "ed25519_scalarmult_base"
                 {| loc_var := A_xyzt_var; loc_type := TBytes 200 |}
                 [{| loc_var := a_var; loc_type := TBytes 32 |}])))
      pred.
Proof.
  intros rs h_full_var a_var A_xyzt_var h_full pred
         Hh_full Hh_full_len Hne_aA Hpred.
  eapply compile_red_seq.
  { (* Call 1: memmove_a_from_h. *)
    eapply compile_red_call.
    intros rs1 [Hframe1 Hbranch1].
    cbn in Hbranch1.
    destruct Hbranch1 as [Hmsg_len1 [src_bs [Hsrc Htgt]]].
    pose proof (slot_holds_inj _ _ _ _ Hsrc Hh_full) as Heq; subst src_bs.
    exact (conj Hframe1 Htgt). }
  intros rs1 [Hframe1 Htgt1].
  eapply compile_red_seq.
  { (* Call 2: clamp_64 (in-place on a_var). *)
    eapply compile_red_call.
    intros rs2 [Hframe2 Hbranch2].
    cbn in Hbranch2.
    destruct Hbranch2 as [Hmsg_len2 [in_bs [Hsrc2 Htgt2]]].
    pose proof (slot_holds_inj _ _ _ _ Hsrc2 Htgt1) as Heq; subst in_bs.
    exact (conj Hframe2 Htgt2). }
  intros rs2 [Hframe2 Htgt2].
  (* Call 3: ed25519_scalarmult_base. *)
  eapply compile_red_call.
  intros rs3 [Hframe3 Hbranch3].
  cbn in Hbranch3.
  destruct Hbranch3 as [Hmsg_len3 [src_bs3 [Hsrc3 Htgt3]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc3 Htgt2) as Heq; subst src_bs3.
  apply Hpred.
  - apply (slot_holds_frame _ _ _ _ _ Hframe3 Hne_aA Htgt2).
  - exact Htgt3.
Qed.

(* ================================================================ *)
(* §2. Tier-4 compile lemma: sha512 then scalar_reduce                *)
(* ================================================================ *)

(** **[compile_red_sha512_then_reduce]**
 *
 *  Hash an input buffer with SHA-512 into a 64-byte intermediate,
 *  then reduce mod L into a 32-byte scalar.  Used twice in
 *  ed25519_sign (for [r] and [k]) and once in ed25519_verify.
 *
 *  Two calls -> one compile rule.  Side conditions:
 *    - [full_var <> reduced_var]  so [full_var] survives the second
 *      call's frame;
 *    - [input_var <> full_var]    so the SHA call's source isn't its
 *      destination (the strong_callee_post branch destructures on
 *      that pre-state).
 *
 *  The post-state expressions match the strong_callee_post branches
 *  for [sha512_64] and [scalar_reduce] exactly. *)
Lemma compile_red_sha512_then_reduce :
  forall (rs : rust_state_ed)
         (input_var full_var reduced_var : var)
         (n : nat)
         (input_bs : list Byte.byte) (pred : rpred),
    slot_holds rs input_var input_bs ->
    Datatypes.length input_bs = n ->
    full_var <> reduced_var ->
    (forall rs2,
        slot_holds rs2 full_var (sha512_full_spec input_bs) ->
        slot_holds rs2 reduced_var
          (scalar_reduce_spec (sha512_full_spec input_bs)) ->
        pred rs2) ->
    rhoare strong_callee_post callee_post_n function_table rs
      (REdSeq (REdCall "sha512_64"
                 {| loc_var := full_var; loc_type := TBytes 64 |}
                 [{| loc_var := input_var; loc_type := TBytes n |}])
              (REdCall "scalar_reduce"
                 {| loc_var := reduced_var; loc_type := TBytes 32 |}
                 [{| loc_var := full_var; loc_type := TBytes 64 |}]))
      pred.
Proof.
  intros rs input_var full_var reduced_var n input_bs pred
         Hin Hin_len Hne_fr Hpred.
  eapply compile_red_seq.
  { (* sha512_64. *)
    eapply compile_red_call.
    intros rs1 [Hframe1 Hbranch1].
    cbn in Hbranch1.
    destruct Hbranch1 as [Hmsg_len1 [src_bs [Hsrc Htgt]]].
    pose proof (slot_holds_inj _ _ _ _ Hsrc Hin) as Heq; subst src_bs.
    exact (conj Hframe1 Htgt). }
  intros rs1 [Hframe1 Htgt1].
  (* scalar_reduce. *)
  eapply compile_red_call.
  intros rs2 [Hframe2 Hbranch2].
  cbn in Hbranch2.
  destruct Hbranch2 as [Hmsg_len2 [src_bs2 [Hsrc2 Htgt2]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc2 Htgt1) as Heq; subst src_bs2.
  apply Hpred.
  - apply (slot_holds_frame _ _ _ _ _ Hframe2 Hne_fr Htgt1).
  - exact Htgt2.
Qed.

(* ================================================================ *)
(* §3. Tier-4 compile lemma: concat-two via memmove pair              *)
(* ================================================================ *)

(** **[compile_red_concat_chal_R_M]**
 *
 *  The canonical "chal-buffer" concat: [memmove_chal_R] writes
 *  [bs1 ++ skipn |bs1| dst_init] into [dst_var]; then [memmove_chal_M]
 *  writes [firstn 64 dst_C ++ bs2] (note: [memmove_chal_M] is the
 *  appendix-msg form whose strong_callee_post branch produces
 *  [firstn 64 dst_bs ++ src_bs]).
 *
 *  Side conditions: src1/src2 must not alias dst.  The lemma is
 *  parameterized on [n] (dst slot's allocated length) for
 *  flexibility but expects [n >= 64] in practice. *)
Lemma compile_red_concat_chal_R_M :
  forall (rs : rust_state_ed)
         (dst_var src1_var src2_var : var)
         (n n2 : nat)
         (bs1 bs2 dst_init : list Byte.byte) (pred : rpred),
    slot_holds rs src1_var bs1 ->
    slot_holds rs src2_var bs2 ->
    slot_holds rs dst_var dst_init ->
    src1_var <> dst_var ->
    src2_var <> dst_var ->
    (forall rs2,
        slot_holds rs2 dst_var
          (firstn 64 (bs1 ++ skipn (Datatypes.length bs1) dst_init) ++ bs2)%list ->
        pred rs2) ->
    rhoare strong_callee_post callee_post_n function_table rs
      (REdSeq (REdCall "memmove_chal_R"
                 {| loc_var := dst_var; loc_type := TBytes n |}
                 [{| loc_var := src1_var; loc_type := TBytes (Datatypes.length bs1) |}])
              (REdCall "memmove_chal_M"
                 {| loc_var := dst_var; loc_type := TBytes n |}
                 [{| loc_var := src2_var; loc_type := TBytes n2 |}]))
      pred.
Proof.
  intros rs dst_var src1_var src2_var n n2 bs1 bs2 dst_init pred
         Hsrc1 Hsrc2 Hdst Hne_1d Hne_2d Hpred.
  eapply compile_red_seq.
  { (* memmove_chal_R: dst := bs1 ++ skipn |bs1| dst_init. *)
    eapply compile_red_call.
    intros rs1 [Hframe1 Hbranch1].
    cbn in Hbranch1.
    destruct Hbranch1 as [Hmsg_len1 [src_bs [dst_bs [Hsrc_h [Hdst_h Htgt]]]]].
    pose proof (slot_holds_inj _ _ _ _ Hsrc_h Hsrc1) as Heq1; subst src_bs.
    pose proof (slot_holds_inj _ _ _ _ Hdst_h Hdst) as Heq2; subst dst_bs.
    exact (conj Hframe1 Htgt). }
  intros rs1 [Hframe1 Htgt1].
  (* Frame src2 into rs1 (src2 <> dst). *)
  pose proof (slot_holds_frame _ _ _ _ _ Hframe1 Hne_2d Hsrc2) as Hsrc2_1.

  (* memmove_chal_M: dst := firstn 64 dst_C ++ bs2. *)
  eapply compile_red_call.
  intros rs2 [Hframe2 Hbranch2].
  cbn in Hbranch2.
  destruct Hbranch2 as [Hmsg_len2 [src_bs2 [dst_bs2 [Hsrc2_h [Hdst2_h Htgt2]]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc2_h Hsrc2_1) as Heq3; subst src_bs2.
  pose proof (slot_holds_inj _ _ _ _ Hdst2_h Htgt1) as Heq4; subst dst_bs2.
  apply Hpred.
  exact Htgt2.
Qed.

(** **[compile_red_concat_nonce_R_msg]**
 *
 *  The nonce-buffer variant: [memmove_chal_R] (yes, despite the name,
 *  has the right shape) writes [bs1 ++ skipn |bs1| dst_init] then
 *  [memmove_nonce_msg] (which has post [firstn 32 dst_bs ++ src_bs])
 *  appends bs2.  Note the [firstn 32] in [memmove_nonce_msg] vs the
 *  [firstn 64] in [memmove_chal_M] — that's the only structural
 *  difference and the reason we ship both forms. *)
Lemma compile_red_concat_nonce_R_msg :
  forall (rs : rust_state_ed)
         (dst_var src1_var src2_var : var)
         (n n2 : nat)
         (bs1 bs2 dst_init : list Byte.byte) (pred : rpred),
    slot_holds rs src1_var bs1 ->
    slot_holds rs src2_var bs2 ->
    slot_holds rs dst_var dst_init ->
    src1_var <> dst_var ->
    src2_var <> dst_var ->
    (forall rs2,
        slot_holds rs2 dst_var
          (firstn 32 (bs1 ++ skipn (Datatypes.length bs1) dst_init) ++ bs2)%list ->
        pred rs2) ->
    rhoare strong_callee_post callee_post_n function_table rs
      (REdSeq (REdCall "memmove_chal_R"
                 {| loc_var := dst_var; loc_type := TBytes n |}
                 [{| loc_var := src1_var; loc_type := TBytes (Datatypes.length bs1) |}])
              (REdCall "memmove_nonce_msg"
                 {| loc_var := dst_var; loc_type := TBytes n |}
                 [{| loc_var := src2_var; loc_type := TBytes n2 |}]))
      pred.
Proof.
  intros rs dst_var src1_var src2_var n n2 bs1 bs2 dst_init pred
         Hsrc1 Hsrc2 Hdst Hne_1d Hne_2d Hpred.
  eapply compile_red_seq.
  { eapply compile_red_call.
    intros rs1 [Hframe1 Hbranch1].
    cbn in Hbranch1.
    destruct Hbranch1 as [Hmsg_len1 [src_bs [dst_bs [Hsrc_h [Hdst_h Htgt]]]]].
    pose proof (slot_holds_inj _ _ _ _ Hsrc_h Hsrc1) as Heq1; subst src_bs.
    pose proof (slot_holds_inj _ _ _ _ Hdst_h Hdst) as Heq2; subst dst_bs.
    exact (conj Hframe1 Htgt). }
  intros rs1 [Hframe1 Htgt1].
  pose proof (slot_holds_frame _ _ _ _ _ Hframe1 Hne_2d Hsrc2) as Hsrc2_1.
  eapply compile_red_call.
  intros rs2 [Hframe2 Hbranch2].
  cbn in Hbranch2.
  destruct Hbranch2 as [Hmsg_len2 [src_bs2 [dst_bs2 [Hsrc2_h [Hdst2_h Htgt2]]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc2_h Hsrc2_1) as Heq3; subst src_bs2.
  pose proof (slot_holds_inj _ _ _ _ Hdst2_h Htgt1) as Heq4; subst dst_bs2.
  apply Hpred.
  exact Htgt2.
Qed.

End Ed25519Tier4.

(** ** Roadmap

    Four Tier-4 sugar lemmas Qed above:
    - [compile_red_clamp_then_scalarmult_base]
    - [compile_red_sha512_then_reduce]
    - [compile_red_concat_chal_R_M]
    - [compile_red_concat_nonce_R_msg]

    These collapse 7+ [REdCall]s of the Ed25519 sign body
    (steps 2-4: clamp+scalarmult-base; steps 5-7 + 10-12: sha512+reduce
    twice; concat patterns) into 4 Tier-4 invocations.

    Future work:
    - Tier-4 lemmas for verify-side concatenation patterns.
    - [compile_red_full_sign] — single Tier-5 lemma assembling the
      whole 21-call sign body. *)
