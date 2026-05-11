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
 *     Strong_Correctness; delegates to [ed25519_compress_gallina]
 *     (not the true Ristretto canonicalisation; Tier-2).
 *   - [bytes_equal_32_spec] — Definition imported via
 *     Verify_Strong_Correctness.
 *
 * Only one new local Definition: [ristretto_h_scalarmult_spec] — see
 * the per-spec doc-comment below.  It currently sets H := B (the
 * Ed25519 base point), which is a CRYPTOGRAPHIC PLACEHOLDER and not
 * the Ristretto255 H generator; it makes the resulting Pedersen
 * commitment cryptographically TRIVIAL (binding is broken because mG
 * and rH lie on the same generator).  See the doc-comment for the
 * precise gap and the work needed to land a faithful H.  No axioms;
 * the pipeline is closed under the global context.
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
Require Import Bedrock.End2End.Ed25519.ScalarmultVerified.
Require Import Bedrock.End2End.Ed25519.ScalarmultBaseVerified.
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

(** [ristretto_h_scalarmult_spec]: 32B scalar r → 200B Edwards point,
    interpreted as scalar multiplication of the second Pedersen
    generator H.

    -------------------------------------------------------------------
    CRYPTOGRAPHIC GAP — PLACEHOLDER GENERATOR, BINDING IS BROKEN.
    -------------------------------------------------------------------
    A Pedersen commitment Com(m, r) := m*G + r*H is computationally
    BINDING iff log_G(H) is unknown to the committer — i.e. iff H is
    an independent generator of the prime-order subgroup.  The Ed25519
    base point B is the natural choice for G; H must be derived in a
    way that makes log_B(H) infeasible.

    The standard derivation (BIP-340-style, or the convention used by
    Signal's zkgroup) is:

        H := Elligator2(SHA-512("Ristretto255H_basis" || domain_sep))

    i.e. hash a fixed nothing-up-my-sleeve string to a uniformly
    distributed Curve25519 / Edwards point and clear the cofactor.
    Because SHA-512 is modelled as a random oracle, the discrete log
    of the resulting H w.r.t. G is uniform in the prime-order
    subgroup and unknown.

    The current implementation does NONE of the above.  It returns
    [ed25519_scalarmult_spec r base_point_xyzt], i.e. it sets H := B
    (the Ed25519 base point).  Then log_B(H) = 1 is publicly known,
    and an adversary can trivially open any commitment to any message
    by adjusting the randomness:
        Com(m, r) = m*B + r*B = (m + r)*B = Com(m', m + r - m')
    for arbitrary m'.  This BREAKS the binding property of Pedersen.

    The HIDING property is unaffected (rH is still uniform in the
    subgroup since r is uniform), but Pedersen without binding is
    not a commitment scheme.

    SAFETY OF DOWNSTREAM PROOFS: the strong-correctness theorems
    [pedersen_commit_strong_correct] / [pedersen_open_strong_correct]
    establish a STRUCTURAL property ("the Rust program threads each
    leaf's output into the next leaf's input correctly"), NOT a
    cryptographic binding/hiding claim.  They hold verbatim with any
    Definition of [ristretto_h_scalarmult_spec] of the correct
    (input,output) shape, because the leaf is [Global Opaque].
    Replacing this placeholder with the real Elligator2-of-SHA-512
    derivation upgrades the same Qed proof into a faithful Pedersen
    statement (modulo the Ristretto encoding placeholders, see
    [Bedrock.End2End.Lizard.Strong_Correctness]).

    Reference: §A.4 of draft-irtf-cfrg-ristretto255-decaf448-03 for
    Elligator2 on Curve25519; §4 of [Pedersen, "Non-interactive and
    information-theoretic secure verifiable secret sharing", CRYPTO 1991]
    for the binding/hiding requirements on the H generator. *)
Definition ristretto_h_scalarmult_spec (r : list Byte.byte) : list Byte.byte :=
  ed25519_scalarmult_spec r base_point_xyzt.
Global Opaque ristretto_h_scalarmult_spec.

Lemma ristretto_h_scalarmult_spec_len :
  forall input, length input = 32%nat ->
    length (ristretto_h_scalarmult_spec input) = 200%nat.
Proof.
  intros input _.
  Transparent ristretto_h_scalarmult_spec.
  unfold ristretto_h_scalarmult_spec.
  apply ed25519_scalarmult_spec_len.
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
