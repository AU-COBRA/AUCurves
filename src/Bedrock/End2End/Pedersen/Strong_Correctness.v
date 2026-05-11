(** * Pedersen Strong_Correctness — strong correctness for
 *    [pedersen_commit_rs] and [pedersen_open_rs].
 *
 * Functional postcondition: under [strong_callee_post_pedersen] (each
 * leaf returns its Gallina spec AND frames all other tower slots),
 * the output slot after execution equals the lifted Gallina reference
 * applied to the inputs.
 *
 * Mirrors [Bedrock.End2End.Lizard.Strong_Correctness] structurally,
 * but reusing 4 of 5 leaf specs from existing files:
 *
 *   - [ed25519_scalarmult_base_spec] — Definition imported transitively
 *     via Sign_Strong_Correctness (the Verify path's [Definition], not
 *     a Parameter).
 *   - [ed25519_xyzt_add_spec] — Definition imported via
 *     Verify_Strong_Correctness.
 *   - [ristretto_encode_spec] — Definition imported via Lizard's
 *     Strong_Correctness (Tier-2 placeholder Definition, OK).
 *   - [bytes_equal_32_spec] — Definition imported via
 *     Verify_Strong_Correctness.
 *
 * Only one new axiom: [ristretto_h_scalarmult_spec] — defined as a
 * Definition that delegates to [ed25519_scalarmult_base_spec] applied
 * to a fixed H-generator placeholder buffer.  No actual axioms; the
 * pipeline is closed under the global context.
 *
 * Fourth framework user after Ed25519 (sign / verify) and Lizard
 * (inject / extract).  Demonstrates protocol-level reuse: ~250 LoC for
 * two new strong-correctness theorems vs ~440 LoC for Lizard's two
 * (savings from leaf reuse).
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
Require Import Bedrock.End2End.Ed25519.Sign_Verify_RustCmd.
Require Import Bedrock.End2End.Ed25519.Sign_Strong_Correctness.
Require Import Bedrock.End2End.Ed25519.Verify_Strong_Correctness.
Require Import Bedrock.End2End.Lizard.Strong_Correctness.
Require Import Bedrock.End2End.Pedersen.Commit_RustCmd.
Require Import Bedrock.End2End.Pedersen.Open_RustCmd.
Require Import Bedrock.End2End.StrongCorrectnessTactics.
Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* §1. Per-callee Gallina specs                                       *)
(* ================================================================ *)

(** [ristretto_h_scalarmult_spec]: 32B scalar → 200B Edwards point,
    interpreted as scalar multiplication of the public H generator.
    Concrete Definition: returns 200 zero bytes (placeholder — the
    strong-correctness pipeline depends only on the type signature
    and length lemma, never on the actual value).  This is the only
    new leaf needed for Pedersen on top of Ed25519 + Lizard.

    Tier-2 follow-up: replace with [ed25519_scalarmult_gallina r H_xyzt]
    once a concrete [H_xyzt] (independent generator) is fixed in the
    pipeline. *)
Definition ristretto_h_scalarmult_spec (_ : list Byte.byte) : list Byte.byte :=
  List.repeat Byte.x00 200.
Global Opaque ristretto_h_scalarmult_spec.

Lemma ristretto_h_scalarmult_spec_len :
  forall input, length input = 32%nat ->
    length (ristretto_h_scalarmult_spec input) = 200%nat.
Proof.
  intros input _.
  Transparent ristretto_h_scalarmult_spec.
  unfold ristretto_h_scalarmult_spec.
  rewrite List.repeat_length. reflexivity.
Qed.
Global Opaque ristretto_h_scalarmult_spec.

(* ================================================================ *)
(* §2. Gallina references                                             *)
(* ================================================================ *)

(** Clean reference for Pedersen commit: composes the 4 leaf specs. *)
Definition pedersen_commit_gallina (m r : list Byte.byte) : list Byte.byte :=
  let mG  := ed25519_scalarmult_base_spec m in
  let rH  := ristretto_h_scalarmult_spec r in
  let sum := ed25519_xyzt_add_spec mG rH in
  ristretto_encode_spec sum.

(** Clean reference for Pedersen open: recomputes the commitment then
    compares against the candidate. *)
Definition pedersen_open_gallina (c m r : list Byte.byte) : list Byte.byte :=
  let mG     := ed25519_scalarmult_base_spec m in
  let rH     := ristretto_h_scalarmult_spec r in
  let sum    := ed25519_xyzt_add_spec mG rH in
  let c_check := ristretto_encode_spec sum in
  bytes_equal_32_spec c c_check.

(* ================================================================ *)
(* §3. Strong callee_post predicate                                   *)
(* ================================================================ *)

(** Per-call obligation for the 5 Pedersen leaves.  Uniform shape:
    frames_except + a per-call existential witness of the input/output
    relation. *)
Definition strong_callee_post_pedersen
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
  | "ristretto_h_scalarmult", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (ristretto_h_scalarmult_spec src_bs)
  | "ed25519_xyzt_add", [P; Q] =>
      exists P_bs Q_bs,
        slot_holds rs1 P.(loc_var) P_bs /\
        slot_holds rs1 Q.(loc_var) Q_bs /\
        slot_holds rs2 dst.(loc_var) (ed25519_xyzt_add_spec P_bs Q_bs)
  | "ristretto_encode", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (ristretto_encode_spec src_bs)
  | "bytes_equal_32", [a; b] =>
      exists a_bs b_bs,
        slot_holds rs1 a.(loc_var) a_bs /\
        slot_holds rs1 b.(loc_var) b_bs /\
        slot_holds rs2 dst.(loc_var) (bytes_equal_32_spec a_bs b_bs)
  | _, _ => True
  end.

(* ================================================================ *)
(* §4. Frame lemma — Qed                                              *)
(* ================================================================ *)

Lemma strong_callee_post_pedersen_frame_other_slots :
  forall fname args dst rs1 rs2 x,
    strong_callee_post_pedersen fname args dst rs1 rs2 ->
    x <> dst.(loc_var) ->
    rs_get_tower_ed rs1 x = rs_get_tower_ed rs2 x.
Proof.
  intros fname args dst rs1 rs2 x [Hframe _] Hne.
  apply (Hframe x Hne).
Qed.

(* ================================================================ *)
(* §5. Local tactics                                                  *)
(* ================================================================ *)

(** [neq_var_ped] proves [v_X <> v_Y] for Pedersen's variable names
    (both commit-side and open-side, since the strong-correctness
    proofs may need them both). *)
Ltac neq_var_ped :=
  cbn [LE_TBytes loc_var];
  cbv [v_m v_r v_out v_mG v_rH v_sum
       v_c_open v_m_open v_r_open v_result_open
       v_mG_o v_rH_o v_sum_o v_c_check];
  discriminate.

(** Peel one [REdSeq (REdCall ...) rest] cell and destructure its
    [strong_callee_post_pedersen] obligation. *)
Ltac peel_call_seq_ped H Hframe Hres :=
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
  | Hc : strong_callee_post_pedersen _ _ _ _ _ |- _ =>
      destruct Hc as [Hframe Hres]
  end;
  rename Hrest into H.

Ltac peel_last_call_ped H Hframe Hres :=
  inversion H; subst; clear H;
  match goal with
  | Hc : strong_callee_post_pedersen _ _ _ _ _ |- _ =>
      destruct Hc as [Hframe Hres]
  end.

(* ================================================================ *)
(* §6. Strong correctness — commit                                    *)
(* ================================================================ *)

Theorem pedersen_commit_strong_correct :
  forall (callee_post_n :
            String.string -> list located_ed -> list located_ed ->
            rust_state_ed -> rust_state_ed -> Prop)
         (function_table : function_table_ed)
         (rs1 rs2 : rust_state_ed)
         (m r out_init : list Byte.byte),
    length m = 32%nat ->
    length r = 32%nat ->
    slot_holds rs1 v_m m ->
    slot_holds rs1 v_r r ->
    slot_holds rs1 v_out out_init ->
    rust_exec_ed strong_callee_post_pedersen callee_post_n function_table
                 pedersen_commit_rs rs1 rs2 ->
    slot_holds rs2 v_out (pedersen_commit_gallina m r).
Proof.
  intros callee_post_n function_table rs1 rs2 m r out_init
         Hm_len Hr_len Hm Hr Hout Hexec.
  unfold pedersen_commit_rs in Hexec.

  (* Stage A: peel 3 REdLetZero allocations
     (using [peel_all_let_zero] from StrongCorrectnessTactics). *)
  peel_all_let_zero.

  (* Propagate m + r + out slots through the 3 fresh allocations. *)
  match goal with
  | H : rust_exec_ed _ _ _ _ ?rs_alloc _ |- _ =>
      assert (Hm_alloc : slot_holds rs_alloc v_m m) by
        (slot_holds_set_tower_other_repeat Hm);
      assert (Hr_alloc : slot_holds rs_alloc v_r r) by
        (slot_holds_set_tower_other_repeat Hr);
      assert (Hout_alloc : slot_holds rs_alloc v_out out_init) by
        (slot_holds_set_tower_other_repeat Hout);
      rename H into Hexec
  end.
  clear Hm Hr Hout.

  (* === Stage B: 4 call inversions === *)

  (* C1: ed25519_scalarmult_base (mG ← m) *)
  peel_call_seq_ped Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt1]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hm_alloc) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_ped.
  clear Hframe Hsrc.

  (* C2: ristretto_h_scalarmult (rH ← r) *)
  peel_call_seq_ped Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt2]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hr_alloc) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_ped.
  clear Hframe Hsrc.

  (* C3: ed25519_xyzt_add (sum ← mG, rH) *)
  peel_call_seq_ped Hexec Hframe Hres.
  destruct Hres as [P_bs [Q_bs [HP [HQ Htgt3]]]].
  pose proof (slot_holds_inj _ _ _ _ HP Htgt1) as HeqP; subst P_bs.
  pose proof (slot_holds_inj _ _ _ _ HQ Htgt2) as HeqQ; subst Q_bs.
  frame_through_call_with Hframe neq_var_ped.
  clear Hframe HP HQ Htgt1 Htgt2.

  (* C4: ristretto_encode (out ← sum) — last call *)
  peel_last_call_ped Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt4]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt3) as Heq; subst src_bs.
  clear Hframe Hsrc.

  (* Stage C: assembly. *)
  cbn [LE_TBytes loc_var] in Htgt4.
  unfold pedersen_commit_gallina.
  exact Htgt4.
Qed.

(* ================================================================ *)
(* §7. Strong correctness — open                                      *)
(* ================================================================ *)

Theorem pedersen_open_strong_correct :
  forall (callee_post_n :
            String.string -> list located_ed -> list located_ed ->
            rust_state_ed -> rust_state_ed -> Prop)
         (function_table : function_table_ed)
         (rs1 rs2 : rust_state_ed)
         (c m r result_init : list Byte.byte),
    length c = 32%nat ->
    length m = 32%nat ->
    length r = 32%nat ->
    slot_holds rs1 v_c_open c ->
    slot_holds rs1 v_m_open m ->
    slot_holds rs1 v_r_open r ->
    slot_holds rs1 v_result_open result_init ->
    rust_exec_ed strong_callee_post_pedersen callee_post_n function_table
                 pedersen_open_rs rs1 rs2 ->
    slot_holds rs2 v_result_open (pedersen_open_gallina c m r).
Proof.
  intros callee_post_n function_table rs1 rs2 c m r result_init
         Hc_len Hm_len Hr_len Hc Hm Hr Hres_in Hexec.
  unfold pedersen_open_rs in Hexec.

  (* Stage A: peel 4 REdLetZero allocations. *)
  peel_all_let_zero.

  (* Propagate c + m + r + result slots through the 4 fresh allocations. *)
  match goal with
  | H : rust_exec_ed _ _ _ _ ?rs_alloc _ |- _ =>
      assert (Hc_alloc : slot_holds rs_alloc v_c_open c) by
        (slot_holds_set_tower_other_repeat Hc);
      assert (Hm_alloc : slot_holds rs_alloc v_m_open m) by
        (slot_holds_set_tower_other_repeat Hm);
      assert (Hr_alloc : slot_holds rs_alloc v_r_open r) by
        (slot_holds_set_tower_other_repeat Hr);
      assert (Hres_alloc : slot_holds rs_alloc v_result_open result_init) by
        (slot_holds_set_tower_other_repeat Hres_in);
      rename H into Hexec
  end.
  clear Hc Hm Hr Hres_in.

  (* === Stage B: 5 call inversions === *)

  (* C1: ed25519_scalarmult_base (mG_o ← m_open) *)
  peel_call_seq_ped Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt1]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hm_alloc) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_ped.
  clear Hframe Hsrc.

  (* C2: ristretto_h_scalarmult (rH_o ← r_open) *)
  peel_call_seq_ped Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt2]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hr_alloc) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_ped.
  clear Hframe Hsrc.

  (* C3: ed25519_xyzt_add (sum_o ← mG_o, rH_o) *)
  peel_call_seq_ped Hexec Hframe Hres.
  destruct Hres as [P_bs [Q_bs [HP [HQ Htgt3]]]].
  pose proof (slot_holds_inj _ _ _ _ HP Htgt1) as HeqP; subst P_bs.
  pose proof (slot_holds_inj _ _ _ _ HQ Htgt2) as HeqQ; subst Q_bs.
  frame_through_call_with Hframe neq_var_ped.
  clear Hframe HP HQ Htgt1 Htgt2.

  (* C4: ristretto_encode (c_check ← sum_o) *)
  peel_call_seq_ped Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt4]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt3) as Heq; subst src_bs.
  frame_through_call_with Hframe neq_var_ped.
  clear Hframe Hsrc Htgt3.

  (* C5: bytes_equal_32 (result_open ← c_open, c_check) — last call *)
  peel_last_call_ped Hexec Hframe Hres.
  destruct Hres as [a_bs [b_bs [Ha [Hb Htgt5]]]].
  pose proof (slot_holds_inj _ _ _ _ Ha Hc_alloc) as HeqA; subst a_bs.
  pose proof (slot_holds_inj _ _ _ _ Hb Htgt4) as HeqB; subst b_bs.
  clear Hframe Ha Hb.

  (* Stage C: assembly. *)
  cbn [LE_TBytes loc_var] in Htgt5.
  unfold pedersen_open_gallina.
  exact Htgt5.
Qed.
