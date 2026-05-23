(** * RustCmdRupicolaRistretto — Tier-4 compile lemmas for ristretto255.
 *
 *  Companion to [RustCmdRupicolaEd25519.v] (which provides Tier-4
 *  sugar for the Ed25519 sign/verify primitive blocks).  The new
 *  Tier-4 lemmas here target the algorithmic patterns that recur in
 *  [End2End/Lizard/RistrettoDecode.v] and [RistrettoEncode.v]:
 *
 *    - [compile_red_modp_arith_{mul,add,sub,sq}]
 *        : (_ ⊕ _) mod ed25519_p felem-op then continuation.  Single
 *          output, dispatched via [compile_red_call] +
 *          [strong_callee_post_ristretto].  Qed.
 *    - [compile_red_sqrt_ratio_m1]
 *        : the structured 2-output sqrt-ratio leaf invocation,
 *          dispatched via [compile_red_calln] +
 *          [strong_callee_post_n_ristretto].  Statement Qed-shaped;
 *          body sketches the cascade but the [Section]-quantified
 *          form is closed only at Derive-time instantiation
 *          (see [End2End/Ristretto/Ristretto_RustCmd.v]).
 *    - [compile_red_parse_canonical]
 *        : the option-typed parser dispatch at the entry point,
 *          composed with [REdIfNz] on a parse-status byte.
 *
 *  Each Qed-clean lemma is a thin composition of Tier-0 lemmas from
 *  [RustCmdRupicola.v] — no new framework primitives.
 *
 *  Status (2026-05-22 Phase B.5b):
 *    - §1 [_mul/_add/_sub/_sq] — Qed.
 *    - §2 [sqrt_ratio_m1]      — statement Qed-shaped, body Admitted
 *                                pending the Section [callee_post_n]
 *                                instantiation to [strong_callee_post_n_ristretto].
 *    - §3 [parse_canonical]    — same as §2.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import micromega.Lia.
Require Import coqutil.Word.LittleEndianList.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.RustCmdRupicola.
Require Import Bedrock.End2End.Ed25519.Sign_Strong_Correctness.
Require Import Bedrock.End2End.Ed25519.CompressVerified.
Require Import Bedrock.End2End.Ed25519.XyztAddVerified.
Require Import Bedrock.End2End.Lizard.RistrettoHelpers.
Require Import Bedrock.End2End.Ristretto.RistrettoBridges.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* Tier-4 lemmas for the single-output felem-op pattern.             *)
(* Quantified per-instantiation of [callee_post_n] + [function_table] *)
(* — but we FIX [callee_post] to [strong_callee_post_ristretto]      *)
(* so we can destructure its branches concretely.                    *)
(* ================================================================ *)

Section RistrettoTier4.
  Context (function_table : function_table_ed).
  Context (callee_post_n : String.string -> list located_ed -> list located_ed ->
                           rust_state_ed -> rust_state_ed -> Prop).

  (* ============================================================ *)
  (* §1.  compile_red_modp_arith_{mul,add,sub,sq} — Qed             *)
  (* ============================================================ *)

  (** [compile_red_modp_arith_mul rs result_var a_var b_var ...] —
      the "fe25519_mul; body" pattern.

      Compiles
      {{
        REdSeq (REdCall "fe25519_mul" result_loc [a_loc; b_loc]) k
      }}
      from a state where [a_var] and [b_var] hold known bytes [a_bs]
      and [b_bs].  After the call, [result_var] holds
      [fe25519_mul_spec a_bs b_bs] (cf. [RistrettoBridges.v] §1),
      and the source slots are preserved by frame propagation.

      Side condition: [a_var <> result_var], [b_var <> result_var]
      so the source slots survive the call's frame.

      The proof is the canonical [compile_red_seq] + [compile_red_call]
      cascade with [strong_callee_post_ristretto]'s fe25519_mul branch
      destructured. *)
  Lemma compile_red_modp_arith_mul
        (rs : rust_state_ed)
        (result_var a_var b_var : var)
        (a_bs b_bs : list Byte.byte)
        (k : rust_cmd_ed) (pred : rpred) :
    slot_holds rs a_var a_bs ->
    slot_holds rs b_var b_bs ->
    a_var <> result_var ->
    b_var <> result_var ->
    (forall rs1,
        slot_holds rs1 result_var (fe25519_mul_spec a_bs b_bs) ->
        slot_holds rs1 a_var a_bs ->
        slot_holds rs1 b_var b_bs ->
        rhoare strong_callee_post_ristretto callee_post_n function_table rs1 k pred) ->
    rhoare strong_callee_post_ristretto callee_post_n function_table rs
      (REdSeq (REdCall "fe25519_mul"
                 {| loc_var := result_var; loc_type := TBytes 32 |}
                 [{| loc_var := a_var; loc_type := TBytes 32 |};
                  {| loc_var := b_var; loc_type := TBytes 32 |}])
              k)
      pred.
  Proof.
    intros Ha Hb Hne_a Hne_b Hk.
    eapply compile_red_seq.
    { eapply compile_red_call.
      intros rs1 Hpost.
      cbv [strong_callee_post_ristretto strong_callee_post_fe25519_mul] in Hpost.
      cbn in Hpost.
      destruct Hpost as [Hframe1 [a_bs' [b_bs' [Ha' [Hb' Htgt]]]]].
      pose proof (slot_holds_inj _ _ _ _ Ha' Ha) as Heqa; subst a_bs'.
      pose proof (slot_holds_inj _ _ _ _ Hb' Hb) as Heqb; subst b_bs'.
      exact (conj Hframe1 Htgt). }
    intros rs1 [Hframe1 Htgt1].
    apply Hk.
    - exact Htgt1.
    - eapply slot_holds_frame; [exact Hframe1 | exact Hne_a | exact Ha].
    - eapply slot_holds_frame; [exact Hframe1 | exact Hne_b | exact Hb].
  Qed.

  Lemma compile_red_modp_arith_add
        (rs : rust_state_ed)
        (result_var a_var b_var : var)
        (a_bs b_bs : list Byte.byte)
        (k : rust_cmd_ed) (pred : rpred) :
    slot_holds rs a_var a_bs ->
    slot_holds rs b_var b_bs ->
    a_var <> result_var ->
    b_var <> result_var ->
    (forall rs1,
        slot_holds rs1 result_var (fe25519_add_spec a_bs b_bs) ->
        slot_holds rs1 a_var a_bs ->
        slot_holds rs1 b_var b_bs ->
        rhoare strong_callee_post_ristretto callee_post_n function_table rs1 k pred) ->
    rhoare strong_callee_post_ristretto callee_post_n function_table rs
      (REdSeq (REdCall "fe25519_add"
                 {| loc_var := result_var; loc_type := TBytes 32 |}
                 [{| loc_var := a_var; loc_type := TBytes 32 |};
                  {| loc_var := b_var; loc_type := TBytes 32 |}])
              k)
      pred.
  Proof.
    intros Ha Hb Hne_a Hne_b Hk.
    eapply compile_red_seq.
    { eapply compile_red_call.
      intros rs1 Hpost.
      cbv [strong_callee_post_ristretto strong_callee_post_fe25519_add] in Hpost.
      cbn in Hpost.
      destruct Hpost as [Hframe1 [a_bs' [b_bs' [Ha' [Hb' Htgt]]]]].
      pose proof (slot_holds_inj _ _ _ _ Ha' Ha) as Heqa; subst a_bs'.
      pose proof (slot_holds_inj _ _ _ _ Hb' Hb) as Heqb; subst b_bs'.
      exact (conj Hframe1 Htgt). }
    intros rs1 [Hframe1 Htgt1].
    apply Hk.
    - exact Htgt1.
    - eapply slot_holds_frame; [exact Hframe1 | exact Hne_a | exact Ha].
    - eapply slot_holds_frame; [exact Hframe1 | exact Hne_b | exact Hb].
  Qed.

  Lemma compile_red_modp_arith_sub
        (rs : rust_state_ed)
        (result_var a_var b_var : var)
        (a_bs b_bs : list Byte.byte)
        (k : rust_cmd_ed) (pred : rpred) :
    slot_holds rs a_var a_bs ->
    slot_holds rs b_var b_bs ->
    a_var <> result_var ->
    b_var <> result_var ->
    (forall rs1,
        slot_holds rs1 result_var (fe25519_sub_spec a_bs b_bs) ->
        slot_holds rs1 a_var a_bs ->
        slot_holds rs1 b_var b_bs ->
        rhoare strong_callee_post_ristretto callee_post_n function_table rs1 k pred) ->
    rhoare strong_callee_post_ristretto callee_post_n function_table rs
      (REdSeq (REdCall "fe25519_sub"
                 {| loc_var := result_var; loc_type := TBytes 32 |}
                 [{| loc_var := a_var; loc_type := TBytes 32 |};
                  {| loc_var := b_var; loc_type := TBytes 32 |}])
              k)
      pred.
  Proof.
    intros Ha Hb Hne_a Hne_b Hk.
    eapply compile_red_seq.
    { eapply compile_red_call.
      intros rs1 Hpost.
      cbv [strong_callee_post_ristretto strong_callee_post_fe25519_sub] in Hpost.
      cbn in Hpost.
      destruct Hpost as [Hframe1 [a_bs' [b_bs' [Ha' [Hb' Htgt]]]]].
      pose proof (slot_holds_inj _ _ _ _ Ha' Ha) as Heqa; subst a_bs'.
      pose proof (slot_holds_inj _ _ _ _ Hb' Hb) as Heqb; subst b_bs'.
      exact (conj Hframe1 Htgt). }
    intros rs1 [Hframe1 Htgt1].
    apply Hk.
    - exact Htgt1.
    - eapply slot_holds_frame; [exact Hframe1 | exact Hne_a | exact Ha].
    - eapply slot_holds_frame; [exact Hframe1 | exact Hne_b | exact Hb].
  Qed.

  Lemma compile_red_modp_arith_sq
        (rs : rust_state_ed)
        (result_var a_var : var)
        (a_bs : list Byte.byte)
        (k : rust_cmd_ed) (pred : rpred) :
    slot_holds rs a_var a_bs ->
    a_var <> result_var ->
    (forall rs1,
        slot_holds rs1 result_var (fe25519_sq_spec a_bs) ->
        slot_holds rs1 a_var a_bs ->
        rhoare strong_callee_post_ristretto callee_post_n function_table rs1 k pred) ->
    rhoare strong_callee_post_ristretto callee_post_n function_table rs
      (REdSeq (REdCall "fe25519_sq"
                 {| loc_var := result_var; loc_type := TBytes 32 |}
                 [{| loc_var := a_var; loc_type := TBytes 32 |}])
              k)
      pred.
  Proof.
    intros Ha Hne_a Hk.
    eapply compile_red_seq.
    { eapply compile_red_call.
      intros rs1 Hpost.
      cbv [strong_callee_post_ristretto strong_callee_post_fe25519_sq] in Hpost.
      cbn in Hpost.
      destruct Hpost as [Hframe1 [a_bs' [Ha' Htgt]]].
      pose proof (slot_holds_inj _ _ _ _ Ha' Ha) as Heqa; subst a_bs'.
      exact (conj Hframe1 Htgt). }
    intros rs1 [Hframe1 Htgt1].
    apply Hk.
    - exact Htgt1.
    - eapply slot_holds_frame; [exact Hframe1 | exact Hne_a | exact Ha].
  Qed.

End RistrettoTier4.

(* ================================================================ *)
(* Multi-output Tier-4 lemmas (sqrt_ratio_m1, parse_canonical).      *)
(* These use [strong_callee_post_n_ristretto] in the [callee_post_n] *)
(* slot, so we fix that parameter to our schema (rather than         *)
(* leaving it Section-quantified, which would deny the destructure). *)
(* ================================================================ *)

Section RistrettoTier4Multi.
  Context (function_table : function_table_ed).
  Context (callee_post : String.string -> list located_ed -> located_ed ->
                         rust_state_ed -> rust_state_ed -> Prop).

  (* ============================================================ *)
  (* §2.  compile_red_sqrt_ratio_m1                                *)
  (* ============================================================ *)

  (** [compile_red_sqrt_ratio_m1] — the [(was_square, r) :=
      sqrt_ratio_m1 u v] pattern.

      Compiles to a single 2-output [REdCallN] invoking the
      [ristretto_sqrt_ratio_m1] leaf:
      {{
        REdSeq (REdCallN "ristretto_sqrt_ratio_m1"
                  [ws_loc; r_loc] [u_loc; v_loc])
               k
      }}
      where ws_loc has 1-byte type and r_loc has 32-byte type.

      Post: [ws_var] holds [sqrt_ratio_m1_was_square_spec u_bs v_bs]
      and [r_var] holds [sqrt_ratio_m1_r_spec u_bs v_bs]. *)
  Lemma compile_red_sqrt_ratio_m1
        (rs : rust_state_ed)
        (ws_var r_var u_var v_var : var)
        (u_bs v_bs : list Byte.byte)
        (k : rust_cmd_ed) (pred : rpred) :
    slot_holds rs u_var u_bs ->
    slot_holds rs v_var v_bs ->
    ws_var <> r_var ->
    u_var <> ws_var ->
    u_var <> r_var ->
    v_var <> ws_var ->
    v_var <> r_var ->
    (forall rs1,
        slot_holds rs1 ws_var (sqrt_ratio_m1_was_square_spec u_bs v_bs) ->
        slot_holds rs1 r_var  (sqrt_ratio_m1_r_spec u_bs v_bs) ->
        slot_holds rs1 u_var u_bs ->
        slot_holds rs1 v_var v_bs ->
        rhoare callee_post strong_callee_post_n_ristretto function_table rs1 k pred) ->
    rhoare callee_post strong_callee_post_n_ristretto function_table rs
      (REdSeq (REdCallN "ristretto_sqrt_ratio_m1"
                 [{| loc_var := ws_var; loc_type := TBytes 1 |};
                  {| loc_var := r_var;  loc_type := TBytes 32 |}]
                 [{| loc_var := u_var;  loc_type := TBytes 32 |};
                  {| loc_var := v_var;  loc_type := TBytes 32 |}])
              k)
      pred.
  Proof.
    intros Hu Hv Hne_wr Hne_uw Hne_ur Hne_vw Hne_vr Hk.
    eapply compile_red_seq.
    { eapply compile_red_calln.
      intros rs1 Hpost.
      cbv [strong_callee_post_n_ristretto
           strong_callee_post_ristretto_sqrt_ratio_m1] in Hpost.
      cbn in Hpost.
      destruct Hpost as [Hframe_ws [Hframe_r [_Hne_local
                         [u_bs' [v_bs' [Hu' [Hv' [Htgt_ws Htgt_r]]]]]]]].
      pose proof (slot_holds_inj _ _ _ _ Hu' Hu) as Heq1; subst u_bs'.
      pose proof (slot_holds_inj _ _ _ _ Hv' Hv) as Heq2; subst v_bs'.
      (* Pack the post: (frame_ws /\ frame_r /\ ne_local /\ Htgt_ws /\ Htgt_r). *)
      exact (conj Hframe_ws (conj Hframe_r (conj Htgt_ws Htgt_r))). }
    intros rs1 [Hframe_ws [Hframe_r [Htgt_ws Htgt_r]]].
    apply Hk.
    - exact Htgt_ws.
    - exact Htgt_r.
    - (* u_var is framed across both dests.  Frame_r frames everything
         except r_var; since u_var <> r_var, slot_holds rs1 u_var u_bs.
         (frame_ws is redundant but kept for symmetry.) *)
      eapply slot_holds_frame; [exact Hframe_r | exact Hne_ur | exact Hu].
    - eapply slot_holds_frame; [exact Hframe_r | exact Hne_vr | exact Hv].
  Qed.

  (* ============================================================ *)
  (* §3.  compile_red_parse_canonical                              *)
  (* ============================================================ *)

  (** [compile_red_parse_canonical] — option-typed parser dispatch.

      Compiles
      {{
        match ristretto_parse_canonical_felem bs with
        | None    => bad_cmd
        | Some s  => success_cmd[s]
        end
      }}
      to
      {{
        REdSeq (REdCallN "ristretto_parse_canonical_felem"
                  [s_loc; status_loc] [bs_loc])
        (REdIfNz status_expr bad_cmd success_cmd)
      }}
      where [status_expr] evaluates the status byte at [status_var]
      (= 0 ⇔ success).

      Side conditions:
        - [eval_sexpr_ed rs1 status_expr] in the post-call state
          equals the LE numeric value of the parse-status byte
          (= 0 on success, = 1 on rejection).  Discharged at call site
          via an explicit byte-load sexpr.  Here we accept this as
          a hypothesis [Hstatus_eval] parameterised by the post state. *)
  Lemma compile_red_parse_canonical
        (rs : rust_state_ed)
        (bs_var s_var status_var : var)
        (status_expr : sexpr_ed)
        (bs_input : list Byte.byte)
        (bad_cmd success_cmd : rust_cmd_ed)
        (pred : rpred) :
    slot_holds rs bs_var bs_input ->
    s_var <> status_var ->
    bs_var <> s_var ->
    bs_var <> status_var ->
    (* status_expr in the post-call state evaluates to:
         - 0   if parser returned Some
         - <>0 if parser returned None *)
    (forall rs1,
        slot_holds rs1 status_var (parse_canonical_felem_status_spec bs_input) ->
        match ristretto_parse_canonical_felem bs_input with
        | Some _ => eval_sexpr_ed rs1 status_expr = Some 0
        | None   => exists v, eval_sexpr_ed rs1 status_expr = Some v /\ v <> 0
        end) ->
    (forall rs1,
        slot_holds rs1 s_var (parse_canonical_felem_s_spec bs_input) ->
        slot_holds rs1 status_var (parse_canonical_felem_status_spec bs_input) ->
        slot_holds rs1 bs_var bs_input ->
        (ristretto_parse_canonical_felem bs_input <> None ->
         rhoare callee_post strong_callee_post_n_ristretto function_table rs1 success_cmd pred) /\
        (ristretto_parse_canonical_felem bs_input = None ->
         rhoare callee_post strong_callee_post_n_ristretto function_table rs1 bad_cmd pred)) ->
    rhoare callee_post strong_callee_post_n_ristretto function_table rs
      (REdSeq (REdCallN "ristretto_parse_canonical_felem"
                 [{| loc_var := s_var;      loc_type := TBytes 32 |};
                  {| loc_var := status_var; loc_type := TBytes 1 |}]
                 [{| loc_var := bs_var;     loc_type := TBytes 32 |}])
              (REdIfNz status_expr bad_cmd success_cmd))
      pred.
  Proof.
    intros Hbs Hne_s_st Hne_bs_s Hne_bs_st Hstatus_eval Hk.
    eapply compile_red_seq.
    { eapply compile_red_calln.
      intros rs1 Hpost.
      cbv [strong_callee_post_n_ristretto
           strong_callee_post_ristretto_parse_canonical] in Hpost.
      cbn in Hpost.
      destruct Hpost as [Hframe_s [Hframe_st [_Hne_local
                         [bs' [Hbs' [Htgt_s Htgt_st]]]]]].
      pose proof (slot_holds_inj _ _ _ _ Hbs' Hbs) as Heq; subst bs'.
      exact (conj Hframe_s (conj Hframe_st (conj Htgt_s Htgt_st))). }
    intros rs1 [Hframe_s [Hframe_st [Htgt_s Htgt_st]]].
    (* Specialise Hk to rs1 with the recovered slot facts. *)
    assert (Hbs1 : slot_holds rs1 bs_var bs_input).
    { eapply slot_holds_frame; [exact Hframe_st | exact Hne_bs_st | exact Hbs]. }
    specialize (Hk rs1 Htgt_s Htgt_st Hbs1) as [Hk_succ Hk_fail].
    specialize (Hstatus_eval rs1 Htgt_st).
    eapply compile_red_if_nz.
    - (* status_expr <> 0 ⇒ parse failed ⇒ run bad_cmd *)
      intros v Heval Hnz.
      destruct (ristretto_parse_canonical_felem bs_input) as [zS|] eqn:Hparse;
        cbn in Hstatus_eval.
      + (* Some case: Hstatus_eval reduces to status_expr = Some 0.
           Combined with Heval : status_expr = Some v, get v = 0,
           contradicting Hnz. *)
        rewrite Heval in Hstatus_eval. inversion Hstatus_eval.
        congruence.
      + (* None case: invoke failure branch. *)
        apply Hk_fail. reflexivity.
    - (* status_expr = 0 ⇒ parse succeeded ⇒ run success_cmd *)
      intros Heval0.
      destruct (ristretto_parse_canonical_felem bs_input) as [zS|] eqn:Hparse;
        cbn in Hstatus_eval.
      + (* Some case: invoke success branch. *)
        apply Hk_succ. congruence.
      + (* None case: Hstatus_eval reduces to (exists v, status_expr = Some v /\ v <> 0),
           contradicting Heval0 : status_expr = Some 0. *)
        destruct Hstatus_eval as [v [Hv Hvnz]].
        rewrite Heval0 in Hv. inversion Hv. congruence.
  Qed.

End RistrettoTier4Multi.

(* ================================================================ *)
(* §4. slot_holds_z abstract-Z bridge (sub-blocker #1 fix).           *)
(* ================================================================ *)

(** [slot_holds_z rs x z] — the abstract-Z view of a slot.  Asserts
    that [x] holds the 32-byte canonical LE encoding of [z], and that
    [z] is in the F_p range.  Provides a stable form for chained
    arithmetic continuations: [(le_combine (le_split 32 z)) mod 2^256 =
    z] holds whenever [0 <= z < 2^256], but [assumption] can't unify
    the two forms.  Use [slot_holds_z] to skip the round-trip
    bookkeeping at each compose. *)
Definition slot_holds_z (rs : rust_state_ed) (x : String.string) (z : Z) : Prop :=
  slot_holds rs x (le_split 32 z) /\ 0 <= z < ed25519_p.

Lemma slot_holds_z_intro :
  forall rs x z,
    slot_holds rs x (le_split 32 z) ->
    0 <= z < ed25519_p ->
    slot_holds_z rs x z.
Proof. intros; split; assumption. Qed.

Lemma slot_holds_z_bytes :
  forall rs x z,
    slot_holds_z rs x z ->
    slot_holds rs x (le_split 32 z).
Proof. intros rs x z [H _]; exact H. Qed.

Lemma slot_holds_z_bound :
  forall rs x z,
    slot_holds_z rs x z ->
    0 <= z < ed25519_p.
Proof. intros rs x z [_ H]; exact H. Qed.

Lemma slot_holds_z_frame :
  forall rs1 rs2 dst x z,
    frames_except rs1 rs2 dst ->
    x <> dst ->
    slot_holds_z rs1 x z ->
    slot_holds_z rs2 x z.
Proof.
  intros rs1 rs2 dst x z Hfr Hne [Hh Hb]; split.
  - eapply slot_holds_frame; eauto.
  - exact Hb.
Qed.

(** Round-trip cancellation: combining then splitting again on a
    32-byte LE encoding of an in-range [z] returns the original
    encoding.  Direct corollary of [LittleEndianList.le_combine_split]
    plus [z < 2^256] (which follows from [z < ed25519_p < 2^256]). *)
Lemma le_split_combine_canonical :
  forall z,
    0 <= z < ed25519_p ->
    le_split 32 (le_combine (le_split 32 z)) = le_split 32 z.
Proof.
  intros z [Hlo Hhi].
  rewrite le_combine_split.
  unfold ed25519_p in Hhi.
  rewrite Z.mod_small; [reflexivity|].
  change (2 ^ (Z.of_nat 32 * 8)) with (2 ^ 256).
  lia.
Qed.

(* ================================================================ *)
(* §5. Tier-4 lemmas for the constant setters (sub-blocker #2 fix).   *)
(* ================================================================ *)

Section RistrettoTier4Const.
  Context (function_table : function_table_ed).
  Context (callee_post_n : String.string -> list located_ed -> list located_ed ->
                           rust_state_ed -> rust_state_ed -> Prop).

  Lemma compile_red_const_one
        (rs : rust_state_ed) (result_var : var)
        (k : rust_cmd_ed) (pred : rpred) :
    (forall rs1,
        slot_holds rs1 result_var fe25519_const_one_spec ->
        rhoare strong_callee_post_ristretto callee_post_n function_table rs1 k pred) ->
    rhoare strong_callee_post_ristretto callee_post_n function_table rs
      (REdSeq (REdCall "fe25519_const_one"
                 {| loc_var := result_var; loc_type := TBytes 32 |}
                 [])
              k)
      pred.
  Proof.
    intros Hk.
    eapply compile_red_seq.
    { eapply compile_red_call.
      intros rs1 Hpost.
      cbv [strong_callee_post_ristretto strong_callee_post_fe25519_const_one] in Hpost.
      cbn in Hpost.
      destruct Hpost as [Hframe1 Htgt].
      exact (conj Hframe1 Htgt). }
    intros rs1 [_Hframe1 Htgt1].
    apply Hk. exact Htgt1.
  Qed.

  Lemma compile_red_const_two
        (rs : rust_state_ed) (result_var : var)
        (k : rust_cmd_ed) (pred : rpred) :
    (forall rs1,
        slot_holds rs1 result_var fe25519_const_two_spec ->
        rhoare strong_callee_post_ristretto callee_post_n function_table rs1 k pred) ->
    rhoare strong_callee_post_ristretto callee_post_n function_table rs
      (REdSeq (REdCall "fe25519_const_two"
                 {| loc_var := result_var; loc_type := TBytes 32 |}
                 [])
              k)
      pred.
  Proof.
    intros Hk.
    eapply compile_red_seq.
    { eapply compile_red_call.
      intros rs1 Hpost.
      cbv [strong_callee_post_ristretto strong_callee_post_fe25519_const_two] in Hpost.
      cbn in Hpost.
      destruct Hpost as [Hframe1 Htgt].
      exact (conj Hframe1 Htgt). }
    intros rs1 [_Hframe1 Htgt1].
    apply Hk. exact Htgt1.
  Qed.

  Lemma compile_red_const_d
        (rs : rust_state_ed) (result_var : var)
        (k : rust_cmd_ed) (pred : rpred) :
    (forall rs1,
        slot_holds rs1 result_var fe25519_const_d_spec ->
        rhoare strong_callee_post_ristretto callee_post_n function_table rs1 k pred) ->
    rhoare strong_callee_post_ristretto callee_post_n function_table rs
      (REdSeq (REdCall "fe25519_const_d"
                 {| loc_var := result_var; loc_type := TBytes 32 |}
                 [])
              k)
      pred.
  Proof.
    intros Hk.
    eapply compile_red_seq.
    { eapply compile_red_call.
      intros rs1 Hpost.
      cbv [strong_callee_post_ristretto strong_callee_post_fe25519_const_d] in Hpost.
      cbn in Hpost.
      destruct Hpost as [Hframe1 Htgt].
      exact (conj Hframe1 Htgt). }
    intros rs1 [_Hframe1 Htgt1].
    apply Hk. exact Htgt1.
  Qed.

  (* ============================================================ *)
  (* §6.  compile_red_pack_xyzt5 (sub-blocker #3 fix)              *)
  (* ============================================================ *)

  Lemma compile_red_pack_xyzt5
        (rs : rust_state_ed)
        (out_var x_var y_var z_var ta_var tb_var : var)
        (x_bs y_bs z_bs ta_bs tb_bs : list Byte.byte)
        (k : rust_cmd_ed) (pred : rpred) :
    slot_holds rs x_var  x_bs ->
    slot_holds rs y_var  y_bs ->
    slot_holds rs z_var  z_bs ->
    slot_holds rs ta_var ta_bs ->
    slot_holds rs tb_var tb_bs ->
    x_var  <> out_var ->
    y_var  <> out_var ->
    z_var  <> out_var ->
    ta_var <> out_var ->
    tb_var <> out_var ->
    (forall rs1,
        slot_holds rs1 out_var (pack_xyzt5_spec x_bs y_bs z_bs ta_bs tb_bs) ->
        slot_holds rs1 x_var  x_bs ->
        slot_holds rs1 y_var  y_bs ->
        slot_holds rs1 z_var  z_bs ->
        slot_holds rs1 ta_var ta_bs ->
        slot_holds rs1 tb_var tb_bs ->
        rhoare strong_callee_post_ristretto callee_post_n function_table rs1 k pred) ->
    rhoare strong_callee_post_ristretto callee_post_n function_table rs
      (REdSeq (REdCall "pack_xyzt5"
                 {| loc_var := out_var; loc_type := TBytes 200 |}
                 [{| loc_var := x_var;  loc_type := TBytes 32 |};
                  {| loc_var := y_var;  loc_type := TBytes 32 |};
                  {| loc_var := z_var;  loc_type := TBytes 32 |};
                  {| loc_var := ta_var; loc_type := TBytes 32 |};
                  {| loc_var := tb_var; loc_type := TBytes 32 |}])
              k)
      pred.
  Proof.
    intros Hx Hy Hz Hta Htb Hne_x Hne_y Hne_z Hne_ta Hne_tb Hk.
    eapply compile_red_seq.
    { eapply compile_red_call.
      intros rs1 Hpost.
      cbv [strong_callee_post_ristretto strong_callee_post_pack_xyzt5] in Hpost.
      cbn in Hpost.
      destruct Hpost as [Hframe1
                         [x_bs' [y_bs' [z_bs' [ta_bs' [tb_bs'
                          [Hx' [Hy' [Hz' [Hta' [Htb' Htgt]]]]]]]]]]].
      pose proof (slot_holds_inj _ _ _ _ Hx'  Hx)  as Heqx;  subst x_bs'.
      pose proof (slot_holds_inj _ _ _ _ Hy'  Hy)  as Heqy;  subst y_bs'.
      pose proof (slot_holds_inj _ _ _ _ Hz'  Hz)  as Heqz;  subst z_bs'.
      pose proof (slot_holds_inj _ _ _ _ Hta' Hta) as Heqta; subst ta_bs'.
      pose proof (slot_holds_inj _ _ _ _ Htb' Htb) as Heqtb; subst tb_bs'.
      exact (conj Hframe1 Htgt). }
    intros rs1 [Hframe1 Htgt1].
    apply Hk.
    - exact Htgt1.
    - eapply slot_holds_frame; [exact Hframe1 | exact Hne_x  | exact Hx].
    - eapply slot_holds_frame; [exact Hframe1 | exact Hne_y  | exact Hy].
    - eapply slot_holds_frame; [exact Hframe1 | exact Hne_z  | exact Hz].
    - eapply slot_holds_frame; [exact Hframe1 | exact Hne_ta | exact Hta].
    - eapply slot_holds_frame; [exact Hframe1 | exact Hne_tb | exact Htb].
  Qed.

End RistrettoTier4Const.

(* ================================================================ *)
(* §7. compile_red_set_bytes — verified constant-slot write (T1).     *)
(*     Replaces the trusted fe25519_const_* FFI leaves: REdSetBytes    *)
(*     writes a literal byte array fully within the verified IR.       *)
(* ================================================================ *)

Section SetBytesCompile.
  Context (callee_post : String.string -> list located_ed -> located_ed ->
                         rust_state_ed -> rust_state_ed -> Prop).
  Context (callee_post_n : String.string -> list located_ed -> list located_ed ->
                           rust_state_ed -> rust_state_ed -> Prop).
  Context (function_table : function_table_ed).

  Lemma compile_red_set_bytes
        (rs : rust_state_ed) (loc : located_ed) (bytes : list Z)
        (n : nat) (bs_old : list Byte.byte) (pred : rpred) :
    loc.(loc_type) = TBytes n ->
    rs_get_tower_ed rs loc.(loc_var) =
      Some (exist_tval_ed (TBytes n) (VBytes n bs_old)) ->
    List.length bytes = n ->
    pred (rs_set_tower_ed rs loc.(loc_var)
            (exist_tval_ed (TBytes n) (VBytes n (List.map Z_to_byte bytes)))) ->
    rhoare callee_post callee_post_n function_table rs (REdSetBytes loc bytes) pred.
  Proof.
    intros Hty Hget Hlen Hpred rs' Hexec.
    (* [subst] reconciles the inversion's witnesses with our [n]/[bs_old]
       (the slot lookup is functional), leaving the goal = [Hpred]. *)
    inversion Hexec; subst.
    exact Hpred.
  Qed.

End SetBytesCompile.

(* ========================================================================
   Tier-4 deliverables summary (Phase B.5b, 2026-05-22):

   QED, statement + body closed:
     - compile_red_modp_arith_mul   (§1)
     - compile_red_modp_arith_add   (§1)
     - compile_red_modp_arith_sub   (§1)
     - compile_red_modp_arith_sq    (§1)
     - compile_red_sqrt_ratio_m1    (§2)
     - compile_red_parse_canonical  (§3)

   These six Tier-4 lemmas collapse, respectively:
     - 9 felem-op call sites in [ristretto_decode_gallina]
       (s², u1², u2², v*u2², I*Dx, I*Dx*v, 2*s*Dx, Dy*u1, x*y)
       plus 3 fe25519_add/sub sites (1+ss, 1-ss, p-d*u1²-u2²) — total
       ~12 sites compressed to 12 [eapply] lines via
       [compile_red_modp_arith_*];
     - the 1 sqrt-ratio call site;
     - the 1 entry-point parse-canonical call site.

   The §2/§3 lemmas FIX [callee_post_n] to
   [strong_callee_post_n_ristretto] (concrete dispatch from
   [End2End/Ristretto/RistrettoBridges.v]).  This is consistent with
   the Ed25519 Tier-4 pattern, where [strong_callee_post] is
   instantiated concretely.

   No new framework primitives, no axioms.  Total ~340 LoC including
   docs (~+160 LoC vs the [exact I.] scaffold).
   ======================================================================== *)
