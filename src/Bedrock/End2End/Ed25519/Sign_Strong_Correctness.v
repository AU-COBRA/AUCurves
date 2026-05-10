(** * Sign_Strong_Correctness — Gap-#3 strong correctness for ed25519_sign_rs.
 *
 * Replaces [rust_exec_ed_preserves_wf]'s weak [rs_well_formed] post
 * with a functional postcondition: under [strong_callee_post] (each
 * leaf returns its Gallina spec AND frames all other slots), the
 * sig_out slot after execution equals [ed25519_sign_gallina seed msg].
 *
 * Architecture:
 *   §1 [bytes_at]            : extract a TBytes slot's contents.
 *   §2 leaf Gallina specs    : sha512_full_spec, clamp_64_spec, ...
 *   §3 [ed25519_sign_gallina]: top-level reference (composition).
 *   §4 [strong_callee_post]  : per-call obligation (spec + frame).
 *   §5 frame lemma           : Qed.
 *   §6 strong correctness    : statement (proof Admitted with plan).
 *
 * Status (2026-05-09, post-finishing-pass):
 *   §1-§5 closed (Qed/Defined).
 *   §6 [ed25519_sign_strong_correct] — **Qed**, depends only on the
 *   6 leaf Gallina specs as Parameters.  Theorem returns
 *   [exists nonce_init chal_init, slot_holds rs2 v_sig_out
 *      (ed25519_sign_gallina_lifted seed msg nonce_init chal_init sig_init)],
 *   where the lifted gallina precisely captures the protocol's
 *   intermediate firstn/skipn structure.
 *   §7 [ed25519_sign_gallina_lifted_clean] — corollary asserting
 *   the lifted gallina equals the clean [ed25519_sign_gallina] under
 *   conventional buffer lengths.  [Admitted] — ~100 LoC of length-
 *   based [firstn]/[skipn] rewrites, mechanical.
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
Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* §1. State accessors                                                *)
(* ================================================================ *)

Definition bytes_at (rs : rust_state_ed) (x : String.string) : option (list Byte.byte) :=
  match rs_get_tower_ed rs x with
  | Some (exist_tval_ed (TBytes _) (VBytes _ bs)) => Some bs
  | _ => None
  end.

Definition slot_holds (rs : rust_state_ed) (x : String.string) (bs : list Byte.byte) : Prop :=
  bytes_at rs x = Some bs.

(** Frame predicate: rs1 and rs2 agree on every slot except [exclude]. *)
Definition frames_except (rs1 rs2 : rust_state_ed) (exclude : String.string) : Prop :=
  forall y, y <> exclude -> rs_get_tower_ed rs1 y = rs_get_tower_ed rs2 y.

(* ================================================================ *)
(* §2. Per-callee Gallina specs                                       *)
(* ================================================================ *)

Parameter sha512_full_spec : list Byte.byte -> list Byte.byte.
Parameter sha512_full_spec_len :
  forall input, length (sha512_full_spec input) = 64%nat.

Parameter clamp_64_spec : list Byte.byte -> list Byte.byte.
Parameter clamp_64_spec_len :
  forall bs, length bs = 32%nat -> length (clamp_64_spec bs) = 32%nat.

Parameter ed25519_scalarmult_base_spec : list Byte.byte -> list Byte.byte.
Parameter ed25519_scalarmult_base_spec_len :
  forall scalar, length scalar = 32%nat ->
    length (ed25519_scalarmult_base_spec scalar) = 200%nat.

Parameter ed25519_compress_spec : list Byte.byte -> list Byte.byte.
Parameter ed25519_compress_spec_len :
  forall xyzt, length xyzt = 200%nat ->
    length (ed25519_compress_spec xyzt) = 32%nat.

(* scalar_reduce_spec, scalar_muladd_spec are imported as Parameters
   from RemainingBridges.v. *)

Definition memmove_a_from_h_spec (h_full : list Byte.byte) : list Byte.byte :=
  firstn 32 h_full.
Definition memmove_prefix_from_h_spec (h_full : list Byte.byte) : list Byte.byte :=
  firstn 32 (skipn 32 h_full).

(* ================================================================ *)
(* §3. Gallina reference                                              *)
(* ================================================================ *)

(** Clean reference, depends only on [seed] and [msg].  Equals the
    "lifted" form below when [nonce_init], [chal_init], [sig_init] meet
    the obvious length constraints (length ≥ 32 / 64 / 32). *)
Definition ed25519_sign_gallina (seed : list Byte.byte) (msg : list Byte.byte)
  : list Byte.byte :=
  let h_full   := sha512_full_spec seed in
  let a        := clamp_64_spec (memmove_a_from_h_spec h_full) in
  let prefix   := memmove_prefix_from_h_spec h_full in
  let A_xyzt   := ed25519_scalarmult_base_spec a in
  let A_bytes  := ed25519_compress_spec A_xyzt in
  let nonce    := (prefix ++ msg)%list in
  let r_full   := sha512_full_spec nonce in
  let r        := scalar_reduce_spec r_full in
  let R_xyzt   := ed25519_scalarmult_base_spec r in
  let R_bytes  := ed25519_compress_spec R_xyzt in
  let chal     := (R_bytes ++ A_bytes ++ msg)%list in
  let k_full   := sha512_full_spec chal in
  let k        := scalar_reduce_spec k_full in
  let s        := scalar_muladd_spec r k a in
  (s ++ R_bytes)%list.

(** "Lifted" reference, parameterized by the initial values of the
    [nonce_buf], [chal_buf], [sig_out] slots.  Tracks the protocol's
    actual intermediate state precisely, including the [firstn] /
    [skipn] structure introduced by the [memmove_*] callees that
    write fragments of larger buffers. *)
Definition ed25519_sign_gallina_lifted
    (seed msg : list Byte.byte)
    (nonce_init chal_init sig_init : list Byte.byte)
  : list Byte.byte :=
  let h_full   := sha512_full_spec seed in
  let a        := clamp_64_spec (memmove_a_from_h_spec h_full) in
  let prefix   := memmove_prefix_from_h_spec h_full in
  let A_xyzt   := ed25519_scalarmult_base_spec a in
  let A_bytes  := ed25519_compress_spec A_xyzt in
  let nonce_C7 := (prefix ++ skipn (length prefix) nonce_init)%list in
  let nonce_C8 := (firstn 32 nonce_C7 ++ msg)%list in
  let r_full   := sha512_full_spec nonce_C8 in
  let r        := scalar_reduce_spec r_full in
  let R_xyzt   := ed25519_scalarmult_base_spec r in
  let R_bytes  := ed25519_compress_spec R_xyzt in
  let chal_C13 := (R_bytes ++ skipn (length R_bytes) chal_init)%list in
  let chal_C14 := (firstn 32 chal_C13 ++ A_bytes ++
                   skipn (32 + length A_bytes) chal_C13)%list in
  let chal_C15 := (firstn 64 chal_C14 ++ msg)%list in
  let k_full   := sha512_full_spec chal_C15 in
  let k        := scalar_reduce_spec k_full in
  let sig_C18  := (scalar_muladd_spec r k a ++ skipn 32 sig_init)%list in
  (firstn 32 sig_C18 ++ R_bytes)%list.

(* ================================================================ *)
(* §4. Strong callee_post predicate                                   *)
(* ================================================================ *)

(** Each branch asserts (1) the dest is [spec(args)] in rs2 and
    (2) all other slots are framed.  The frame conjunct is what
    makes [strong_callee_post_frame] provable. *)
Definition strong_callee_post
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
  | "scalar_muladd", [r; k; a] =>
      (* scalar_muladd writes only the first 32 bytes (s = r + k·a mod L)
         of its destination buffer; the trailing 32 bytes are unchanged.
         Models a 64-byte sig_out slot with [s_bytes ++ skipn 32 prev]. *)
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
  | "clamp_64", [] =>
      exists in_bs,
        slot_holds rs1 dst.(loc_var) in_bs /\
        slot_holds rs2 dst.(loc_var) (clamp_64_spec in_bs)
  | "memmove_a_from_h", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (memmove_a_from_h_spec src_bs)
  | "memmove_prefix_from_h", [src] =>
      exists src_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs2 dst.(loc_var) (memmove_prefix_from_h_spec src_bs)
  | "memmove_nonce_prefix", [src] =>
      exists src_bs dst_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs1 dst.(loc_var) dst_bs /\
        slot_holds rs2 dst.(loc_var) (src_bs ++ skipn (length src_bs) dst_bs)
  | "memmove_nonce_msg", [src] =>
      exists src_bs dst_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs1 dst.(loc_var) dst_bs /\
        slot_holds rs2 dst.(loc_var) (firstn 32 dst_bs ++ src_bs)
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
  | "memmove_sig_R", [src] =>
      exists src_bs dst_bs,
        slot_holds rs1 src.(loc_var) src_bs /\
        slot_holds rs1 dst.(loc_var) dst_bs /\
        slot_holds rs2 dst.(loc_var) (firstn 32 dst_bs ++ src_bs)
  | _, _ => True
  end.

(* ================================================================ *)
(* §4b. Tower-state helpers                                           *)
(* ================================================================ *)

Lemma slot_holds_frame :
  forall rs1 rs2 dst x bs,
    frames_except rs1 rs2 dst ->
    x <> dst ->
    slot_holds rs1 x bs ->
    slot_holds rs2 x bs.
Proof.
  unfold slot_holds, bytes_at, frames_except.
  intros rs1 rs2 dst x bs Hfr Hne Hh.
  rewrite <- (Hfr x Hne). exact Hh.
Qed.

(** Lookup is preserved across an [update_in_place_ed] of a different key. *)
Lemma lookup_update_in_place_ed_other :
  forall env x v y,
    y <> x ->
    lookup_t_ed (update_in_place_ed env x v) y = lookup_t_ed env y.
Proof.
  induction env as [|[z w] rest IH]; intros x v y Hne; simpl.
  - rewrite (proj2 (String.eqb_neq y x) Hne). reflexivity.
  - destruct (String.eqb_spec z x) as [Heq|Hne'].
    + subst z. simpl. rewrite (proj2 (String.eqb_neq y x) Hne). reflexivity.
    + simpl. destruct (String.eqb_spec y z) as [|]; [reflexivity | apply IH; assumption].
Qed.

(** Generalized version: tower-set update of slot [x] with any value
    preserves [slot_holds] for a different slot [y].  The proof uses
    [lookup_update_in_place_ed_other] which doesn't care about the
    new value, so this generalization is essentially free. *)
Lemma slot_holds_set_tower_other :
  forall rs x t v y bs,
    y <> x ->
    slot_holds rs y bs ->
    slot_holds (rs_set_tower_ed rs x (exist_tval_ed t v)) y bs.
Proof.
  intros rs x t v y bs Hne Hh.
  unfold slot_holds, bytes_at, rs_get_tower_ed, rs_set_tower_ed in *.
  simpl.
  rewrite lookup_update_in_place_ed_other by congruence.
  exact Hh.
Qed.

(** Backwards-compatible alias for the old [tt_zero_ed]-specific name. *)
Lemma slot_holds_let_zero_other :
  forall rs x t y bs,
    y <> x ->
    slot_holds rs y bs ->
    slot_holds (rs_set_tower_ed rs x (exist_tval_ed t (tt_zero_ed t))) y bs.
Proof.
  intros rs x t y bs Hne Hh.
  apply (slot_holds_set_tower_other rs x t (tt_zero_ed t) y bs Hne Hh).
Qed.

Lemma slot_holds_inj :
  forall rs x bs1 bs2,
    slot_holds rs x bs1 -> slot_holds rs x bs2 -> bs1 = bs2.
Proof. unfold slot_holds; intros rs x bs1 bs2 H1 H2; congruence. Qed.

(** Length axiom for scalar_muladd_spec — needed so [firstn 32] of
    its output equals itself (used in the final memmove_sig_R step). *)
Parameter scalar_muladd_spec_len :
  forall r k a, length (scalar_muladd_spec r k a) = 32%nat.

(* ================================================================ *)
(* §5. Frame lemma — Qed                                              *)
(* ================================================================ *)

(** **Lemma.**  [strong_callee_post] preserves all slots except dest. *)
Lemma strong_callee_post_frame_other_slots :
  forall fname args dst rs1 rs2 x,
    strong_callee_post fname args dst rs1 rs2 ->
    x <> dst.(loc_var) ->
    rs_get_tower_ed rs1 x = rs_get_tower_ed rs2 x.
Proof.
  intros fname args dst rs1 rs2 x [Hframe _] Hne.
  apply (Hframe x Hne).
Qed.

(** **Corollary.**  [bytes_at] is preserved when the queried slot is
    not the call's destination. *)
Corollary strong_callee_post_bytes_at_frame :
  forall fname args dst rs1 rs2 x,
    strong_callee_post fname args dst rs1 rs2 ->
    x <> dst.(loc_var) ->
    bytes_at rs1 x = bytes_at rs2 x.
Proof.
  intros fname args dst rs1 rs2 x Hpost Hne.
  unfold bytes_at.
  rewrite (strong_callee_post_frame_other_slots
             fname args dst rs1 rs2 x Hpost Hne).
  reflexivity.
Qed.

(* ================================================================ *)
(* §6. Strong correctness theorem                                     *)
(* ================================================================ *)

(** **Main theorem.**  Under [strong_callee_post], the ed25519_sign_rs
    protocol produces a sig_out equal to [ed25519_sign_gallina seed msg].

    Hypotheses:
    - lengths: |seed|=32, |msg|=4096 (RFC 8032);
    - the seed and msg slots in rs1 are loaded with the named bytes;
    - rust_exec_ed terminates under strong_callee_post.

    Proof structure (mechanical, ~600 LoC):

    Stage A — slot allocation (13 [REdLetZero] inversions).
      Each [rexec_let_zero] expands the slot environment with a
      zero-initialized typed buffer.  After this stage, the residual
      cmd is the 21-call body and a working state rs_alloc has all
      local slots present and zeroed, with v_seed/v_msg/v_sig_out
      preserved by the [frames_except] property of let_zero.

    Stage B — per-call substitution (21 [rexec_call] inversions).
      For each call site:
        * inversion of [rexec_seq] then [rexec_call] picks out the
          [strong_callee_post] obligation;
        * destructuring its match-branch yields the dest slot's new
          value as a Gallina spec applied to the source slots' bytes;
        * source bytes are looked up via the maintained
          [slot_holds] invariant, propagated forward by §5's frame
          corollary [strong_callee_post_bytes_at_frame].

    Stage C — assembly.
      After 21 substitutions, the final v_sig_out value unfolds to
      the same expression as [ed25519_sign_gallina seed msg].

    The 21 substitutions are rote and can be automated with a custom
    tactic [step_call] that:
        (1) inverts rexec_seq + rexec_call;
        (2) pulls strong_callee_post into existential form;
        (3) frame-propagates all slots except dest;
        (4) rewrites the running state and continues.

    This is bounded work — ~30 LoC per call × 21 calls = ~600 LoC —
    not stated as a Qed here because the proof body is rote
    mechanization, not novel reasoning.  Treating it as Admitted is
    explicit acknowledgment that the architecture is closed but the
    final clerical step remains. *)
(** Tactic: peel one [REdSeq (REdCall ...) rest] cell from a
    rust_exec_ed hypothesis and destructure the call's
    strong_callee_post into a frame conjunct + result. *)
(** [neq_var] proves goals of the form [v_X <> v_Y] for the [v_*]
    Definitions in [Sign_Verify_RustCmd.v].  These are opaque to
    [discriminate], so unfold first. *)
Ltac neq_var :=
  cbn [LE_TBytes loc_var];
  cbv [v_h_full v_a_slot v_prefix v_A_xyzt v_A_bytes v_nonce_buf
       v_r_full v_r_slot v_R_xyzt v_R_bytes v_chal_buf v_k_full v_k_slot
       v_seed v_msg v_sig_out v_msg_len v_sig_in v_pub];
  discriminate.

Ltac peel_call_seq H Hframe Hres :=
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
  | Hc : strong_callee_post _ _ _ _ _ |- _ =>
      rename Hc into Hcp
  end;
  destruct Hcp as [Hframe Hres];
  rename Hrest into H.

Ltac peel_last_call H Hframe Hres :=
  inversion H; subst; clear H;
  match goal with
  | Hc : strong_callee_post _ _ _ _ _ |- _ =>
      destruct Hc as [Hframe Hres]
  end.

(** Tactic: thread a [slot_holds rs_old x bs] hypothesis across a
    [frames_except rs_old rs_new dst] frame, producing
    [slot_holds rs_new x bs] under the assumption [x <> dst]. *)
Ltac frame_thread Hframe :=
  repeat match goal with
  | H : slot_holds ?rs ?x ?bs, Hf : frames_except ?rs _ _ |- _ =>
      lazymatch Hf with
      | Hframe =>
          apply (slot_holds_frame _ _ _ _ _ Hframe ltac:(neq_var)) in H
      end
  end.

Theorem ed25519_sign_strong_correct :
  forall (callee_post_n :
            String.string -> list located_ed -> list located_ed ->
            rust_state_ed -> rust_state_ed -> Prop)
         (function_table : function_table_ed)
         (rs1 rs2 : rust_state_ed) (seed msg sig_init : list Byte.byte),
    length seed = 32%nat ->
    length msg = 4096%nat ->
    slot_holds rs1 v_seed seed ->
    slot_holds rs1 v_msg  msg ->
    slot_holds rs1 v_sig_out sig_init ->
    rust_exec_ed strong_callee_post callee_post_n function_table ed25519_sign_rs rs1 rs2 ->
    exists nonce_init chal_init,
      slot_holds rs2 v_sig_out
        (ed25519_sign_gallina_lifted seed msg nonce_init chal_init sig_init).
Proof.
  intros callee_post_n function_table rs1 rs2 seed msg sig_init Hseed_len Hmsg_len
         Hseed Hmsg Hsig_init Hexec.
  unfold ed25519_sign_rs in Hexec.

  (* Stage A: peel 13 REdLetZero allocations. *)
  repeat (match goal with
          | H : rust_exec_ed _ _ _ (REdLetZero _ _ _) _ _ |- _ =>
              inversion H; subst; clear H
          end).

  (* Propagate seed/msg/sig_init across the 13 fresh slot allocations
     into the post-allocation state via [slot_holds_let_zero_other]. *)
  match goal with
  | H : rust_exec_ed _ _ _ _ ?rs_alloc _ |- _ =>
      assert (Hseed_alloc : slot_holds rs_alloc v_seed seed) by
        (repeat (apply slot_holds_set_tower_other; [discriminate|]); exact Hseed);
      assert (Hmsg_alloc : slot_holds rs_alloc v_msg msg) by
        (repeat (apply slot_holds_set_tower_other; [discriminate|]); exact Hmsg);
      assert (Hsig_alloc : slot_holds rs_alloc v_sig_out sig_init) by
        (repeat (apply slot_holds_set_tower_other; [discriminate|]); exact Hsig_init);
      rename H into Hexec
  end.
  clear Hseed Hmsg Hsig_init.

  (* === Stage B: 19 call inversions === *)

  (* C1: sha512_64 (h_full ← seed) *)
  peel_call_seq Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt1]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hseed_alloc) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hseed_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var].
  clear Hframe Hsrc.

  (* C2: memmove_a_from_h (a ← h_full) *)
  peel_call_seq Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt2]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt1) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hseed_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt1; [|neq_var].
  clear Hframe Hsrc.

  (* C3: clamp_64 (a, in-place) *)
  peel_call_seq Hexec Hframe Hres.
  destruct Hres as [in_bs [Hsrc Htgt3]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt2) as Heq; subst in_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hseed_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt1; [|neq_var].
  clear Hframe Hsrc Htgt2.

  (* C4: memmove_prefix_from_h (prefix ← h_full) *)
  peel_call_seq Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt4]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt1) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hseed_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt1; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3; [|neq_var].
  clear Hframe Hsrc.

  (* C5: ed25519_scalarmult_base (A_xyzt ← a) *)
  peel_call_seq Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt5]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt3) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hseed_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt1; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt4; [|neq_var].
  clear Hframe Hsrc.

  (* C6: ed25519_compress (A_bytes ← A_xyzt) *)
  peel_call_seq Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt6]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt5) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hseed_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt1; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt4; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt5; [|neq_var].
  clear Hframe Hsrc.

  (* C7: memmove_nonce_prefix (nonce_buf ← prefix) *)
  peel_call_seq Hexec Hframe Hres.
  destruct Hres as [src_bs [dst_bs7 [Hsrc [Hdst Htgt7]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt4) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hseed_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt1; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt4; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt5; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt6; [|neq_var].
  clear Hframe Hsrc Hdst.

  (* C8: memmove_nonce_msg (nonce_buf ← msg) — composes with C7 to
     produce prefix ++ msg in nonce_buf. *)
  peel_call_seq Hexec Hframe Hres.
  destruct Hres as [src_bs [dst_bs [Hsrc [Hdst Htgt8]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hmsg_alloc) as Heq; subst src_bs.
  pose proof (slot_holds_inj _ _ _ _ Hdst Htgt7) as Heq2; subst dst_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hseed_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt1; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt4; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt5; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt6; [|neq_var].
  clear Hframe Hsrc Hdst Htgt7.

  (* C9: sha512_64 (r_full ← nonce_buf) *)
  peel_call_seq Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt9]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt8) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hseed_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt5; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt6; [|neq_var].
  clear Hframe Hsrc Htgt1 Htgt4 Htgt8.

  (* C10: scalar_reduce (r ← r_full) *)
  peel_call_seq Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt10]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt9) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hseed_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt5; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt6; [|neq_var].
  clear Hframe Hsrc Htgt9.

  (* C11: ed25519_scalarmult_base (R_xyzt ← r) *)
  peel_call_seq Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt11]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt10) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hseed_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt5; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt6; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt10; [|neq_var].
  clear Hframe Hsrc.

  (* C12: ed25519_compress (R_bytes ← R_xyzt) *)
  peel_call_seq Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt12]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt11) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hseed_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt5; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt6; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt10; [|neq_var].
  clear Hframe Hsrc Htgt11.

  (* C13: memmove_chal_R (chal_buf ← R_bytes) *)
  peel_call_seq Hexec Hframe Hres.
  destruct Hres as [src_bs [dst_bs13 [Hsrc [Hdst Htgt13]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt12) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hseed_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt5; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt6; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt10; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt12; [|neq_var].
  clear Hframe Hsrc Hdst.

  (* C14: memmove_chal_A (chal_buf ← A_bytes) *)
  peel_call_seq Hexec Hframe Hres.
  destruct Hres as [src_bs [dst_bs [Hsrc [Hdst Htgt14]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt6) as Heq; subst src_bs.
  pose proof (slot_holds_inj _ _ _ _ Hdst Htgt13) as Heq2; subst dst_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hseed_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt5; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt6; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt10; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt12; [|neq_var].
  clear Hframe Hsrc Hdst Htgt13.

  (* C15: memmove_chal_M (chal_buf ← msg) *)
  peel_call_seq Hexec Hframe Hres.
  destruct Hres as [src_bs [dst_bs [Hsrc [Hdst Htgt15]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Hmsg_alloc) as Heq; subst src_bs.
  pose proof (slot_holds_inj _ _ _ _ Hdst Htgt14) as Heq2; subst dst_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hseed_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt10; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt12; [|neq_var].
  clear Hframe Hsrc Hdst Htgt5 Htgt6 Htgt14.

  (* C16: sha512_64 (k_full ← chal_buf) *)
  peel_call_seq Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt16]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt15) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hseed_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt10; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt12; [|neq_var].
  clear Hframe Hsrc Htgt15.

  (* C17: scalar_reduce (k ← k_full) *)
  peel_call_seq Hexec Hframe Hres.
  destruct Hres as [src_bs [Hsrc Htgt17]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt16) as Heq; subst src_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hseed_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hmsg_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Hsig_alloc; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt3; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt10; [|neq_var].
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt12; [|neq_var].
  clear Hframe Hsrc Htgt16.

  (* C18: scalar_muladd (sig_out ← r, k, a) *)
  peel_call_seq Hexec Hframe Hres.
  destruct Hres as [r_bs [k_bs [a_bs [dst_bs [Hsr [Hsk [Hsa [Hsd Htgt18]]]]]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsr Htgt10) as Heq; subst r_bs.
  pose proof (slot_holds_inj _ _ _ _ Hsk Htgt17) as Heq; subst k_bs.
  pose proof (slot_holds_inj _ _ _ _ Hsa Htgt3) as Heq; subst a_bs.
  pose proof (slot_holds_inj _ _ _ _ Hsd Hsig_alloc) as Heq; subst dst_bs.
  apply (slot_holds_frame _ _ _ _ _ Hframe) in Htgt12; [|neq_var].
  clear Hframe Hsr Hsk Hsa Hsd Hseed_alloc Hmsg_alloc Hsig_alloc
        Htgt3 Htgt10 Htgt17.

  (* C19: memmove_sig_R (sig_out ← R_bytes) — last call *)
  peel_last_call Hexec Hframe Hres.
  destruct Hres as [src_bs [dst_bs [Hsrc [Hdst Htgt19]]]].
  pose proof (slot_holds_inj _ _ _ _ Hsrc Htgt12) as Heq; subst src_bs.
  pose proof (slot_holds_inj _ _ _ _ Hdst Htgt18) as Heq2; subst dst_bs.
  clear Hframe Hsrc Hdst.

  (* === Stage C: assembly. ===

     Htgt19 says rs2's v_sig_out =
       firstn 32 (scalar_muladd_spec r k a ++ skipn 32 sig_init)
         ++ ed25519_compress_spec (ed25519_scalarmult_base_spec r).

     We need: rs2's v_sig_out = ed25519_sign_gallina seed msg
            = scalar_muladd_spec r k a ++ ed25519_compress_spec ...

     Since [length (scalar_muladd_spec ...) = 32], firstn 32 of
     [scalar_muladd_spec ... ++ _] is just [scalar_muladd_spec ...]. *)
  cbn [LE_TBytes loc_var] in Htgt19.
  (* Stage C: assemble the existential.  The lifted gallina matches
     the literal computed expression with [nonce_init := dst_bs7],
     [chal_init := dst_bs13]; reflexivity then closes. *)
  exists dst_bs7, dst_bs13.
  unfold ed25519_sign_gallina_lifted.
  exact Htgt19.
Qed.

(** **Corollary statement** (length-based collapse to clean gallina).
    With buffers of the conventional lengths
    (nonce_init: 4128, chal_init: 4160, sig_init: 64), the lifted
    gallina equals the clean [ed25519_sign_gallina].

    The proof reduces nested [firstn]/[skipn] chains using each
    spec's length lemma; mechanical, ~100 LoC.  Stated here for
    completeness; the proof body is left as the closing
    finishing step (see Stage C comment below). *)
Local Open Scope list_scope.
Local Close Scope string_scope.

(** Helper: [firstn n (l1 ++ skipn n l2) = l1] when [length l1 = n]. *)
Local Lemma firstn_app_skipn_self :
  forall {A : Type} n (l1 l2 : list A),
    length l1 = n -> firstn n (l1 ++ skipn n l2) = l1.
Proof.
  intros A n l1 l2 Hlen.
  rewrite firstn_app. rewrite Hlen, Nat.sub_diag, firstn_O, app_nil_r.
  apply firstn_all2. lia.
Qed.

(** Helper: [firstn (n+m) (l1 ++ l2 ++ tail) = l1 ++ l2] when
    [length l1 = n] and [length l2 = m]. *)
Local Lemma firstn_app_app_self :
  forall {A : Type} n m (l1 l2 tail : list A),
    length l1 = n -> length l2 = m ->
    firstn (n + m) (l1 ++ l2 ++ tail) = l1 ++ l2.
Proof.
  intros A n m l1 l2 tail H1 H2.
  rewrite firstn_app.
  replace (firstn (n + m) l1) with l1
    by (symmetry; apply firstn_all2; lia).
  f_equal.
  rewrite H1.
  replace (n + m - n) with m by lia.
  rewrite firstn_app, H2, Nat.sub_diag, firstn_O, app_nil_r.
  apply firstn_all2. lia.
Qed.

(** Helper: [skipn (n+m) (l1 ++ l2 ++ tail) = tail] when
    [length l1 = n] and [length l2 = m]. *)
Local Lemma skipn_app_app_self :
  forall {A : Type} n m (l1 l2 tail : list A),
    length l1 = n -> length l2 = m ->
    skipn (n + m) (l1 ++ l2 ++ tail) = tail.
Proof.
  intros A n m l1 l2 tail H1 H2.
  rewrite skipn_app. rewrite H1.
  replace (n + m - n) with m by lia.
  rewrite skipn_all2 by lia. simpl.
  rewrite skipn_app, H2, Nat.sub_diag, skipn_O.
  rewrite skipn_all2 by lia. reflexivity.
Qed.

Theorem ed25519_sign_gallina_lifted_clean :
  forall seed msg nonce_init chal_init sig_init,
    length seed = 32%nat ->
    length msg = 4096%nat ->
    length nonce_init = 4128%nat ->
    length chal_init = 4160%nat ->
    length sig_init = 64%nat ->
    ed25519_sign_gallina_lifted seed msg nonce_init chal_init sig_init
    = ed25519_sign_gallina seed msg.
Proof.
  intros seed msg nonce_init chal_init sig_init
         Hseed_len Hmsg_len Hnonce_len Hchal_len Hsig_len.
  unfold ed25519_sign_gallina_lifted, ed25519_sign_gallina.
  assert (Hh_full_len : length (sha512_full_spec seed) = 64) by apply sha512_full_spec_len.
  assert (Hmem_a_len : length (memmove_a_from_h_spec (sha512_full_spec seed)) = 32).
  { unfold memmove_a_from_h_spec. rewrite firstn_length, Hh_full_len. reflexivity. }
  assert (Ha_len :
    length (clamp_64_spec (memmove_a_from_h_spec (sha512_full_spec seed))) = 32)
    by (apply clamp_64_spec_len; exact Hmem_a_len).
  assert (Hprefix_len :
    length (memmove_prefix_from_h_spec (sha512_full_spec seed)) = 32).
  { unfold memmove_prefix_from_h_spec. rewrite firstn_length, skipn_length, Hh_full_len.
    reflexivity. }
  assert (HA_xyzt_len :
    length (ed25519_scalarmult_base_spec
      (clamp_64_spec (memmove_a_from_h_spec (sha512_full_spec seed)))) = 200)
    by (apply ed25519_scalarmult_base_spec_len; exact Ha_len).
  assert (HA_bytes_len :
    length (ed25519_compress_spec (ed25519_scalarmult_base_spec
      (clamp_64_spec (memmove_a_from_h_spec (sha512_full_spec seed))))) = 32)
    by (apply ed25519_compress_spec_len; exact HA_xyzt_len).
  rewrite Hprefix_len.
  rewrite (firstn_app_skipn_self 32 _ nonce_init Hprefix_len).
  assert (HR_bytes_len :
    length (ed25519_compress_spec (ed25519_scalarmult_base_spec
      (scalar_reduce_spec (sha512_full_spec
        (memmove_prefix_from_h_spec (sha512_full_spec seed) ++ msg))))) = 32).
  { apply ed25519_compress_spec_len.
    apply ed25519_scalarmult_base_spec_len.
    apply scalar_reduce_output_32. }
  rewrite HR_bytes_len.
  rewrite (firstn_app_skipn_self 32 _ chal_init HR_bytes_len).
  rewrite HA_bytes_len.
  assert (Hskipn64 :
    skipn (32 + 32) (ed25519_compress_spec (ed25519_scalarmult_base_spec
      (scalar_reduce_spec (sha512_full_spec
        (memmove_prefix_from_h_spec (sha512_full_spec seed) ++ msg)))) ++
     skipn 32 chal_init) = skipn 64 chal_init).
  { rewrite skipn_app, HR_bytes_len.
    rewrite skipn_all2 by (rewrite HR_bytes_len; lia).
    change (32 + 32 - 32)%nat with 32%nat.
    rewrite skipn_skipn. simpl. reflexivity. }
  rewrite Hskipn64.
  rewrite (firstn_app_app_self 32 32 _ _ _ HR_bytes_len HA_bytes_len).
  rewrite <- app_assoc.
  rewrite (firstn_app_skipn_self 32 _ sig_init (scalar_muladd_spec_len _ _ _)).
  reflexivity.
Qed.
