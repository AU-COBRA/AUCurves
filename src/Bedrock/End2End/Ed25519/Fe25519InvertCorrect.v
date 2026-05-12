(** * Fe25519InvertCorrect — functional correctness of fe25519_invert
 *
 *  Proves the rust_cmd_ed body in [Fe25519InvertBody.v] computes
 *  [x ^ (p - 2) mod p] for [p = 2^255 - 19], whenever the three
 *  external leaves [fe25519_sqr], [fe25519_mul], [fe25519_copy]
 *  satisfy their algebraic specs.
 *
 *  Architecture
 *  ============
 *  The rust_cmd_ed semantics handles TFp25519 slots as opaque
 *  [VFp25519 limbs] payloads — the simulation layer does not pin a
 *  particular limb-to-field encoding.  This file therefore is
 *  parameterized by an abstract
 *      Fp25519_holds : rust_state_ed → String.string → F p → Prop
 *  predicate.  The caller (e.g. the bedrock2-to-RustCmd bridge wired
 *  by [Scalarmult_Impl_RustCmd]) will instantiate it with a concrete
 *  encoding (e.g. the fiat-crypto [feval] of the 5×u64 radix-2^51
 *  representation).
 *
 *  The three leaf-algebraic specs are stated as [Hypothesis] inside
 *  the section, along with a frame Hypothesis that scalar-set
 *  preserves [Fp25519_holds].
 *
 *  These are local [Hypothesis], not global [Axiom]s.  The whole
 *  development is additive: it introduces no axioms into the surface
 *  signature of [print_module_preserves_semantics].
 *
 *  Status
 *  ======
 *  - Body definition: closed via [Fe25519InvertBody.v].
 *  - [sqrN_correct] (inner-loop induction): proved structurally with
 *    a clean N-exponent algebraic step.  Closed.
 *  - [fe25519_invert_correct] (headline theorem): stated; chain
 *    walk laid down as commentary.  Closed [Admitted] per task
 *    prompt's STOP rule.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import micromega.Lia.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Spec.Curve25519.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.Fe25519InvertBody.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. Section parameters: abstract field-slot predicate + leaf      *)
(*     algebra hypotheses.                                           *)
(* ================================================================ *)

Section Fe25519InvertCorrect.

  Variable Fp25519_holds : rust_state_ed -> String.string -> F p -> Prop.

  Variable callee_post :
    String.string -> list located_ed -> located_ed ->
    rust_state_ed -> rust_state_ed -> Prop.
  Variable callee_post_n :
    String.string -> list located_ed -> list located_ed ->
    rust_state_ed -> rust_state_ed -> Prop.
  Variable function_table : function_table_ed.

  Local Notation Hexec :=
    (rust_exec_ed callee_post callee_post_n function_table).

  (** Frame (one-exclude): non-[exclude] variables keep their Fp values. *)
  Definition fp_frame (rs1 rs2 : rust_state_ed) (exclude : String.string) :
      Prop :=
    forall y v, y <> exclude -> Fp25519_holds rs1 y v -> Fp25519_holds rs2 y v.

  (** Frame (two-exclude): used for sqrN where both acc and scratch
      are written.  Holds iff every variable distinct from BOTH
      [e1] and [e2] keeps its Fp value. *)
  Definition fp_frame2 (rs1 rs2 : rust_state_ed) (e1 e2 : String.string) :
      Prop :=
    forall y v, y <> e1 -> y <> e2 -> Fp25519_holds rs1 y v ->
                Fp25519_holds rs2 y v.

  Hypothesis sqr_correct :
    forall (dest src : located_ed) (rs1 rs2 : rust_state_ed) (x : F p),
      dest.(loc_type) = TFp25519 ->
      src.(loc_type) = TFp25519 ->
      dest.(loc_var) <> src.(loc_var) ->
      Fp25519_holds rs1 src.(loc_var) x ->
      Hexec (REdCall "fe25519_sqr" dest [src]) rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) (F.pow x 2) /\
      fp_frame rs1 rs2 dest.(loc_var).

  Hypothesis mul_correct :
    forall (dest a b : located_ed) (rs1 rs2 : rust_state_ed) (xa xb : F p),
      dest.(loc_type) = TFp25519 ->
      a.(loc_type) = TFp25519 ->
      b.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a.(loc_var) ->
      dest.(loc_var) <> b.(loc_var) ->
      Fp25519_holds rs1 a.(loc_var) xa ->
      Fp25519_holds rs1 b.(loc_var) xb ->
      Hexec (REdCall "fe25519_mul" dest [a; b]) rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) (F.mul xa xb) /\
      fp_frame rs1 rs2 dest.(loc_var).

  Hypothesis copy_correct :
    forall (dest src : located_ed) (rs1 rs2 : rust_state_ed) (x : F p),
      dest.(loc_type) = TFp25519 ->
      src.(loc_type) = TFp25519 ->
      dest.(loc_var) <> src.(loc_var) ->
      Fp25519_holds rs1 src.(loc_var) x ->
      Hexec (REdCall "fe25519_copy" dest [src]) rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) x /\
      fp_frame rs1 rs2 dest.(loc_var).

  Hypothesis scalar_set_preserves_holds :
    forall (rs : rust_state_ed) (s : String.string) (z : Z) (y : String.string)
           (v : F p),
      Fp25519_holds rs y v ->
      Fp25519_holds (rs_set_scalar_ed rs s z) y v.

  (** Updating the tower env at a distinct key [y] preserves
      [Fp25519_holds].  Stated for arbitrary tower values so that it
      also covers the [REdLetZero] introduction (whose stored value
      is "some well-formed value" — the semantics of [REdLetZero] in
      [SafeRustEd25519Sim.v] allows any well-formed [rust_val_ed t],
      not just the zero value, since the borrow checker / type system
      ensures the slot is not read before being written by the body).
      This mirrors the analogous lemma [slot_holds_set_tower_other]
      in [Sign_Strong_Correctness.v] for byte-slot semantics. *)
  Hypothesis let_zero_preserves_holds :
    forall (rs : rust_state_ed) (x : String.string) (t : tower_type_ed)
           (v : rust_val_ed t) (y : String.string) (vp : F p),
      y <> x ->
      Fp25519_holds rs y vp ->
      Fp25519_holds (rs_set_tower_ed rs x (exist_tval_ed t v)) y vp.

(* ================================================================ *)
(* §2. Convenience lemmas                                            *)
(* ================================================================ *)

  Lemma fp_frame_refl rs x : fp_frame rs rs x.
  Proof. intros y v Hne H; exact H. Qed.

  Lemma fp_frame2_refl rs e1 e2 : fp_frame2 rs rs e1 e2.
  Proof. intros y v _ _ H; exact H. Qed.

  Lemma fp_frame2_trans rs1 rs2 rs3 e1 e2 :
    fp_frame2 rs1 rs2 e1 e2 -> fp_frame2 rs2 rs3 e1 e2 -> fp_frame2 rs1 rs3 e1 e2.
  Proof.
    intros H12 H23 y v Hne1 Hne2 H. apply H23; auto.
  Qed.

  Lemma fp_frame_to_frame2 rs1 rs2 e1 e2 :
    fp_frame rs1 rs2 e1 -> fp_frame2 rs1 rs2 e1 e2.
  Proof. intros H y v H1 _ Hh. apply H; auto. Qed.

  Lemma seq_inv c1 c2 rs1 rs3 :
    Hexec (REdSeq c1 c2) rs1 rs3 ->
    exists rs2, Hexec c1 rs1 rs2 /\ Hexec c2 rs2 rs3.
  Proof.
    intros Hexec_seq.
    inversion Hexec_seq; subst.
    eexists; eauto.
  Qed.

  (** [REdLetZero] inversion: the body executes from the
      tower-set state, with a fresh well-formed zero value of
      type [t] stored at [x]. *)
  Lemma letzero_inv x t c rs1 rs2 :
    Hexec (REdLetZero x t c) rs1 rs2 ->
    exists v : rust_val_ed t,
      well_formed_ed v /\
      Hexec c (rs_set_tower_ed rs1 x (exist_tval_ed t v)) rs2.
  Proof.
    intros H. inversion H; subst.
    (* Use injection on the existT-like part. *)
    eexists; split; eauto.
  Qed.

(* ================================================================ *)
(* §3. sqrN_correct                                                  *)
(* ================================================================ *)

  Lemma fp_pow_double_step (x : F p) (k : nat) :
    F.pow (F.pow x (N.pow 2 (N.of_nat k))) 2
      = F.pow x (N.pow 2 (N.of_nat (S k))).
  Proof.
    rewrite F.pow_pow_l.
    f_equal.
    rewrite Nnat.Nat2N.inj_succ.
    rewrite N.pow_succ_r by lia.
    lia.
  Qed.

  (** sqrN n acc scratch: after [n] iterations, acc holds [x^(2^n)],
      and ALL slots distinct from both [acc] and [scratch] are
      preserved. *)
  Lemma sqrN_correct :
    forall (n : nat) (acc scratch : String.string) (rs1 rs2 : rust_state_ed)
           (x : F p),
      acc <> scratch ->
      Fp25519_holds rs1 acc x ->
      Hexec (sqrN n acc scratch) rs1 rs2 ->
      Fp25519_holds rs2 acc (F.pow x (N.pow 2 (N.of_nat n))) /\
      fp_frame2 rs1 rs2 acc scratch.
  Proof.
    intros n acc scratch rs1 rs2 x Hne Hacc Hexec_n.
    unfold sqrN in Hexec_n.
    revert rs1 rs2 x Hacc Hexec_n.
    induction n as [|n IH]; intros rs1 rs2 x Hacc Hexec_n.
    - (* Base: REdFor _i 0 body — rs1 = rs2. *)
      inversion Hexec_n; subst.
      cbn [N.of_nat N.pow Pos.iter Pos.of_nat].
      rewrite F.pow_1_r.
      split.
      + exact Hacc.
      + apply fp_frame2_refl.
    - (* Step. *)
      inversion Hexec_n; subst.
      rename H4 into Hbody.
      rename H5 into Htail.
      destruct (seq_inv _ _ _ _ Hbody) as [rs_mid [Hsqr Hcopy]].
      set (rs_aft := rs_set_scalar_ed rs1 "_i" (Z.of_nat n)) in *.
      assert (Hacc' : Fp25519_holds rs_aft acc x)
        by (unfold rs_aft; apply scalar_set_preserves_holds; exact Hacc).
      (* sqr_correct: scratch := acc^2 *)
      unfold sqr_call in Hsqr.
      pose proof
        (sqr_correct (LFp scratch) (LFp acc) rs_aft rs_mid x
                     eq_refl eq_refl (fun H => Hne (eq_sym H)) Hacc' Hsqr) as
        [Hscratch_v Hframe_sqr].
      cbn [LFp loc_var loc_type] in Hscratch_v, Hframe_sqr.
      (* acc unchanged through sqr. *)
      assert (Hacc_mid : Fp25519_holds rs_mid acc x)
        by (apply Hframe_sqr; auto).
      (* copy_correct: acc := scratch (= x^2). *)
      unfold copy_call in Hcopy.
      pose proof
        (copy_correct (LFp acc) (LFp scratch) rs_mid rs3 (F.pow x 2)
                      eq_refl eq_refl Hne Hscratch_v Hcopy) as
        [Hacc_after Hframe_copy].
      cbn [LFp loc_var loc_type] in Hacc_after, Hframe_copy.
      (* IH on rs3 → rs2 with new value x^2. *)
      specialize (IH rs3 rs2 (F.pow x 2) Hacc_after Htail).
      destruct IH as [Hacc_final Hframe_iter].
      split.
      + (* x^(2^(S n)) = (x^2)^(2^n) — discharged by N.pow algebra. *)
        replace ((F.pow x 2) ^ N.pow 2 (N.of_nat n))%F
           with (F.pow x (N.pow 2 (N.of_nat (S n)))) in Hacc_final.
        * exact Hacc_final.
        * rewrite F.pow_pow_l.
          f_equal.
          rewrite Nnat.Nat2N.inj_succ.
          rewrite N.pow_succ_r by lia.
          lia.
      + (* Frame: rs1 → rs_aft (scalar set, preserves all Fp)
                  → rs_mid (sqr, exclude scratch — y ≠ scratch OK)
                  → rs3 (copy, exclude acc — y ≠ acc OK)
                  → rs2 (IH, exclude {acc, scratch}). *)
        intros y vy Hne_acc Hne_scratch Hy.
        pose proof (scalar_set_preserves_holds rs1 "_i" (Z.of_nat n) y vy Hy)
          as Hy_aft.
        assert (Hy_mid : Fp25519_holds rs_mid y vy)
          by (apply Hframe_sqr; auto).
        assert (Hy_iter : Fp25519_holds rs3 y vy)
          by (apply Hframe_copy; auto).
        apply Hframe_iter; auto.
  Qed.

(* ================================================================ *)
(* §4. The main chain                                                *)
(* ================================================================ *)

  (** The full chain: 254 squarings + 11 multiplications, producing
      x^(p-2) mod p.

      Exponent: [p - 2 = 2^255 - 21] in Z, equivalently the
      Bernstein addition-chain target.

      Status: STATED but ADMITTED.  The body in
      [fe25519_invert_body] is fixed; sqrN_correct (§3) gives the
      inner-loop step; sqr_correct/mul_correct/copy_correct give the
      individual leaf steps.  What remains is to walk the 30+ steps
      explicitly: 13 [REdLetZero] introductions + 30+ inlined-call
      steps, threading 13-fact Fp25519_holds context forward, then
      collapsing the exponent algebra to [p - 2].

      The exponent identities are pure N-arithmetic
      ([F.pow_mul_l]/[F.pow_add_r] / [N.pow_add_r]):

        z2       = x^2
        tmp,scr  = x^4 ; x^8                  (tmp ↦ x^8)
        z9       = x^9                        (x^8 · x)
        z11      = x^11                       (x^9 · x^2)
        tmp      = x^22                       (x^11)^2
        z2_5_0   = x^31 = x^(2^5-1)           (x^22 · x^9)
        tmp      = x^992 = x^((2^5-1)·2^5)    (sqr×5)
        z2_10_0  = x^(2^10 - 1)               (· z2_5_0)
        tmp      = x^((2^10-1)·2^10)          (sqr×10)
        z2_20_0  = x^(2^20 - 1)               (· z2_10_0)
        tmp      = x^((2^20-1)·2^20)          (sqr×20)
        z2_40_0  = x^(2^40 - 1)               (· z2_20_0)
        tmp      = x^((2^40-1)·2^10)          (sqr×10)
        z2_50_0  = x^(2^50 - 1)               (· z2_10_0)
        tmp      = x^((2^50-1)·2^50)          (sqr×50)
        z2_100_0 = x^(2^100 - 1)              (· z2_50_0)
        tmp      = x^((2^100-1)·2^100)        (sqr×100)
        t2       = x^(2^200 - 1)              (· z2_100_0)
        tmp      = x^((2^200-1)·2^50)         (sqr×50)
        t3       = x^(2^250 - 1)              (· z2_50_0)
        tmp      = x^((2^250-1)·2^5)          (sqr×5)
        out      = x^((2^250-1)·2^5 + 11)     (· z11)
                 = x^(2^255 - 32 + 11)
                 = x^(2^255 - 21)
                 = x^(p - 2)                  (since p = 2^255 - 19).

      Each step is one application of the relevant correctness
      hypothesis; the frame predicates carry forward the unaffected
      slots.  The arithmetic side conditions are commutative-monoid
      identities on N-exponents, dischargeable by [lia].

      Total estimated LoC for the full discharge: 500-1500.  This
      file STOPS here as Admitted per the task prompt's instruction:
      "If you hit a wall on Part 2, STOP at that point and report
      what's left."  The wall here is the engineering cost (≈1000
      LoC of mechanical bookkeeping), not a mathematical
      difficulty. *)

  (** Convenience: the 13 fresh scratch slots used by
      [fe25519_invert_body] are pairwise distinct, and (for the
      theorem's hypothesis [a_loc_fresh]) distinct from the input
      slot [a_loc.(loc_var)] and the output slot [dest.(loc_var)]. *)
  Definition invert_scratch_names : list String.string :=
    [ "tmp"; "scratch"; "z2"; "z9"; "z11"; "z2_5_0"; "z2_10_0"
    ; "z2_20_0"; "z2_40_0"; "z2_50_0"; "z2_100_0"; "t2"; "t3" ].

  Definition not_in_scratch (s : String.string) : Prop :=
    ~ List.In s invert_scratch_names.

  (** Slot-fresh tactic: peel a [REdLetZero] introduction.  Brings the
      execution hypothesis [H] into the form on the inner command, and
      threads [Fp25519_holds] forward via [let_zero_preserves_holds]. *)
  Ltac peel_let_zero H :=
    inversion H; subst; clear H.

  (** Theorem-level extension: needs [a_loc.(loc_var)] to not collide
      with any of the 13 internal scratch slot names.  Likewise for
      [dest.(loc_var)] (so that the final [mul] writes to a slot
      different from "tmp" and "z11"). *)
  Theorem fe25519_invert_correct :
    forall (rs1 rs2 : rust_state_ed) (a_loc dest : located_ed) (x : F p),
      a_loc.(loc_type) = TFp25519 ->
      dest.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a_loc.(loc_var) ->
      not_in_scratch a_loc.(loc_var) ->
      not_in_scratch dest.(loc_var) ->
      Fp25519_holds rs1 a_loc.(loc_var) x ->
      Hexec (fe25519_invert_body dest [a_loc]) rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) (F.pow x (Z.to_N (p - 2))).
  Proof.
    intros rs1 rs2 a_loc dest x Halt Hdt Hdne Halfresh Hdfresh Hax Hexec_n.
    (* Unfold the 13-deep REdLetZero stack and the seqN.  We
       repeatedly invert each [REdLetZero] (no premises beyond
       well_formed_ed on the zero value), then invert each
       [REdSeq] using [seq_inv]. *)
    cbn [fe25519_invert_body seqN] in Hexec_n.

    (* Helper: distinct names within scratch list. *)
    assert (Htmp_scratch  : ("tmp"  <> "scratch")%string) by discriminate.
    assert (Htmp_z2       : ("tmp"  <> "z2"     )%string) by discriminate.
    assert (Hscratch_z2   : ("scratch" <> "z2"  )%string) by discriminate.
    assert (Hscratch_tmp  : ("scratch" <> "tmp" )%string) by discriminate.

    (* Extract fresh-vs-aloc and fresh-vs-dest disequations from
       the [not_in_scratch] hypotheses. *)
    unfold not_in_scratch, invert_scratch_names in Halfresh, Hdfresh.
    assert (Ha_tmp      : a_loc.(loc_var) <> "tmp"     ) by (intro Heq; apply Halfresh; rewrite Heq; cbn; tauto).
    assert (Ha_scratch  : a_loc.(loc_var) <> "scratch" ) by (intro Heq; apply Halfresh; rewrite Heq; cbn; tauto).
    assert (Ha_z2       : a_loc.(loc_var) <> "z2"      ) by (intro Heq; apply Halfresh; rewrite Heq; cbn; tauto).
    assert (Ha_z9       : a_loc.(loc_var) <> "z9"      ) by (intro Heq; apply Halfresh; rewrite Heq; cbn; tauto).
    assert (Ha_z11      : a_loc.(loc_var) <> "z11"     ) by (intro Heq; apply Halfresh; rewrite Heq; cbn; tauto).
    assert (Ha_z2_5_0   : a_loc.(loc_var) <> "z2_5_0"  ) by (intro Heq; apply Halfresh; rewrite Heq; cbn; tauto).
    assert (Ha_z2_10_0  : a_loc.(loc_var) <> "z2_10_0" ) by (intro Heq; apply Halfresh; rewrite Heq; cbn; tauto).
    assert (Ha_z2_20_0  : a_loc.(loc_var) <> "z2_20_0" ) by (intro Heq; apply Halfresh; rewrite Heq; cbn; tauto).
    assert (Ha_z2_40_0  : a_loc.(loc_var) <> "z2_40_0" ) by (intro Heq; apply Halfresh; rewrite Heq; cbn; tauto).
    assert (Ha_z2_50_0  : a_loc.(loc_var) <> "z2_50_0" ) by (intro Heq; apply Halfresh; rewrite Heq; cbn; tauto).
    assert (Ha_z2_100_0 : a_loc.(loc_var) <> "z2_100_0") by (intro Heq; apply Halfresh; rewrite Heq; cbn; tauto).
    assert (Ha_t2       : a_loc.(loc_var) <> "t2"      ) by (intro Heq; apply Halfresh; rewrite Heq; cbn; tauto).
    assert (Ha_t3       : a_loc.(loc_var) <> "t3"      ) by (intro Heq; apply Halfresh; rewrite Heq; cbn; tauto).

    assert (Hd_tmp      : dest.(loc_var) <> "tmp"      ) by (intro Heq; apply Hdfresh; rewrite Heq; cbn; tauto).
    assert (Hd_z11      : dest.(loc_var) <> "z11"      ) by (intro Heq; apply Hdfresh; rewrite Heq; cbn; tauto).

    (* =================================================== *)
    (* Peel the 13 REdLetZero introductions.               *)
    (* =================================================== *)

    (* 1: tmp *)
    destruct (letzero_inv _ _ _ _ _ Hexec_n) as [v0 [Hwf0 Hexec_n']]; clear Hexec_n.
    set (rs_t := rs_set_tower_ed rs1 "tmp" (exist_tval_ed TFp25519 v0)) in *.
    assert (Hax_t : Fp25519_holds rs_t a_loc.(loc_var) x)
      by (unfold rs_t; apply let_zero_preserves_holds; [exact Ha_tmp | exact Hax]).
    clearbody rs_t. clear rs1 Hax Hwf0 v0. rename Hexec_n' into Hexec_n.

    (* 2: scratch *)
    destruct (letzero_inv _ _ _ _ _ Hexec_n) as [v0 [Hwf0 Hexec_n']]; clear Hexec_n.
    set (rs_s := rs_set_tower_ed rs_t "scratch" (exist_tval_ed TFp25519 v0)) in *.
    assert (Hax_s : Fp25519_holds rs_s a_loc.(loc_var) x)
      by (unfold rs_s; apply let_zero_preserves_holds; [exact Ha_scratch | exact Hax_t]).
    clearbody rs_s. clear rs_t Hax_t Hwf0 v0. rename Hexec_n' into Hexec_n.

    (* 3: z2 *)
    destruct (letzero_inv _ _ _ _ _ Hexec_n) as [v0 [Hwf0 Hexec_n']]; clear Hexec_n.
    set (rs_z2 := rs_set_tower_ed rs_s "z2" (exist_tval_ed TFp25519 v0)) in *.
    assert (Hax_z2 : Fp25519_holds rs_z2 a_loc.(loc_var) x)
      by (unfold rs_z2; apply let_zero_preserves_holds; [exact Ha_z2 | exact Hax_s]).
    clearbody rs_z2. clear rs_s Hax_s Hwf0 v0. rename Hexec_n' into Hexec_n.

    (* 4: z9 *)
    destruct (letzero_inv _ _ _ _ _ Hexec_n) as [v0 [Hwf0 Hexec_n']]; clear Hexec_n.
    set (rs_z9 := rs_set_tower_ed rs_z2 "z9" (exist_tval_ed TFp25519 v0)) in *.
    assert (Hax_z9 : Fp25519_holds rs_z9 a_loc.(loc_var) x)
      by (unfold rs_z9; apply let_zero_preserves_holds; [exact Ha_z9 | exact Hax_z2]).
    clearbody rs_z9. clear rs_z2 Hax_z2 Hwf0 v0. rename Hexec_n' into Hexec_n.

    (* 5: z11 *)
    destruct (letzero_inv _ _ _ _ _ Hexec_n) as [v0 [Hwf0 Hexec_n']]; clear Hexec_n.
    set (rs_z11 := rs_set_tower_ed rs_z9 "z11" (exist_tval_ed TFp25519 v0)) in *.
    assert (Hax_z11 : Fp25519_holds rs_z11 a_loc.(loc_var) x)
      by (unfold rs_z11; apply let_zero_preserves_holds; [exact Ha_z11 | exact Hax_z9]).
    clearbody rs_z11. clear rs_z9 Hax_z9 Hwf0 v0. rename Hexec_n' into Hexec_n.

    (* 6: z2_5_0 *)
    destruct (letzero_inv _ _ _ _ _ Hexec_n) as [v0 [Hwf0 Hexec_n']]; clear Hexec_n.
    set (rs_a := rs_set_tower_ed rs_z11 "z2_5_0" (exist_tval_ed TFp25519 v0)) in *.
    assert (Hax_a : Fp25519_holds rs_a a_loc.(loc_var) x)
      by (unfold rs_a; apply let_zero_preserves_holds; [exact Ha_z2_5_0 | exact Hax_z11]).
    clearbody rs_a. clear rs_z11 Hax_z11 Hwf0 v0. rename Hexec_n' into Hexec_n.

    (* 7: z2_10_0 *)
    destruct (letzero_inv _ _ _ _ _ Hexec_n) as [v0 [Hwf0 Hexec_n']]; clear Hexec_n.
    set (rs_b := rs_set_tower_ed rs_a "z2_10_0" (exist_tval_ed TFp25519 v0)) in *.
    assert (Hax_b : Fp25519_holds rs_b a_loc.(loc_var) x)
      by (unfold rs_b; apply let_zero_preserves_holds; [exact Ha_z2_10_0 | exact Hax_a]).
    clearbody rs_b. clear rs_a Hax_a Hwf0 v0. rename Hexec_n' into Hexec_n.

    (* 8: z2_20_0 *)
    destruct (letzero_inv _ _ _ _ _ Hexec_n) as [v0 [Hwf0 Hexec_n']]; clear Hexec_n.
    set (rs_c := rs_set_tower_ed rs_b "z2_20_0" (exist_tval_ed TFp25519 v0)) in *.
    assert (Hax_c : Fp25519_holds rs_c a_loc.(loc_var) x)
      by (unfold rs_c; apply let_zero_preserves_holds; [exact Ha_z2_20_0 | exact Hax_b]).
    clearbody rs_c. clear rs_b Hax_b Hwf0 v0. rename Hexec_n' into Hexec_n.

    (* 9: z2_40_0 *)
    destruct (letzero_inv _ _ _ _ _ Hexec_n) as [v0 [Hwf0 Hexec_n']]; clear Hexec_n.
    set (rs_d := rs_set_tower_ed rs_c "z2_40_0" (exist_tval_ed TFp25519 v0)) in *.
    assert (Hax_d : Fp25519_holds rs_d a_loc.(loc_var) x)
      by (unfold rs_d; apply let_zero_preserves_holds; [exact Ha_z2_40_0 | exact Hax_c]).
    clearbody rs_d. clear rs_c Hax_c Hwf0 v0. rename Hexec_n' into Hexec_n.

    (* 10: z2_50_0 *)
    destruct (letzero_inv _ _ _ _ _ Hexec_n) as [v0 [Hwf0 Hexec_n']]; clear Hexec_n.
    set (rs_e := rs_set_tower_ed rs_d "z2_50_0" (exist_tval_ed TFp25519 v0)) in *.
    assert (Hax_e : Fp25519_holds rs_e a_loc.(loc_var) x)
      by (unfold rs_e; apply let_zero_preserves_holds; [exact Ha_z2_50_0 | exact Hax_d]).
    clearbody rs_e. clear rs_d Hax_d Hwf0 v0. rename Hexec_n' into Hexec_n.

    (* 11: z2_100_0 *)
    destruct (letzero_inv _ _ _ _ _ Hexec_n) as [v0 [Hwf0 Hexec_n']]; clear Hexec_n.
    set (rs_f := rs_set_tower_ed rs_e "z2_100_0" (exist_tval_ed TFp25519 v0)) in *.
    assert (Hax_f : Fp25519_holds rs_f a_loc.(loc_var) x)
      by (unfold rs_f; apply let_zero_preserves_holds; [exact Ha_z2_100_0 | exact Hax_e]).
    clearbody rs_f. clear rs_e Hax_e Hwf0 v0. rename Hexec_n' into Hexec_n.

    (* 12: t2 *)
    destruct (letzero_inv _ _ _ _ _ Hexec_n) as [v0 [Hwf0 Hexec_n']]; clear Hexec_n.
    set (rs_g := rs_set_tower_ed rs_f "t2" (exist_tval_ed TFp25519 v0)) in *.
    assert (Hax_g : Fp25519_holds rs_g a_loc.(loc_var) x)
      by (unfold rs_g; apply let_zero_preserves_holds; [exact Ha_t2 | exact Hax_f]).
    clearbody rs_g. clear rs_f Hax_f Hwf0 v0. rename Hexec_n' into Hexec_n.

    (* 13: t3 *)
    destruct (letzero_inv _ _ _ _ _ Hexec_n) as [v0 [Hwf0 Hexec_n']]; clear Hexec_n.
    set (rs_h := rs_set_tower_ed rs_g "t3" (exist_tval_ed TFp25519 v0)) in *.
    assert (Hax_h : Fp25519_holds rs_h a_loc.(loc_var) x)
      by (unfold rs_h; apply let_zero_preserves_holds; [exact Ha_t3 | exact Hax_g]).
    clearbody rs_h. clear rs_g Hax_g Hwf0 v0. rename Hexec_n' into Hexec_n.

    (* =================================================== *)
    (* Now the seqN body. 32 commands in sequence.         *)
    (* =================================================== *)
    (* We use [seq_inv] iteratively.  After splitting each
       [REdSeq head tail], we apply the appropriate leaf
       correctness lemma to [head] and propagate [Fp25519_holds]
       facts forward through the frame.  The final command is
       executed directly (no [seq_inv] needed). *)

    (* --- Step 1: REdCall fe25519_sqr (LFp "z2") [a_loc] => z2 = x^2 --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs01 [H1 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    assert (Hne_z2_aloc : (LFp "z2").(loc_var) <> a_loc.(loc_var))
      by (cbn; intro Heq; apply Ha_z2; symmetry; exact Heq).
    pose proof (sqr_correct (LFp "z2") a_loc rs_h rs01 x
                eq_refl Halt Hne_z2_aloc Hax_h H1)
      as [Hz2_v Hframe_1].
    cbn [LFp loc_var loc_type] in Hz2_v, Hframe_1.
    assert (Hax_01 : Fp25519_holds rs01 a_loc.(loc_var) x).
    { apply Hframe_1; [exact Ha_z2 | exact Hax_h]. }
    clear Hax_h Hframe_1 Hne_z2_aloc.

    (* --- Step 2: sqr_call "tmp" "z2" => tmp = x^4 --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs02 [H2 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (sqr_correct (LFp "tmp") (LFp "z2") rs01 rs02 (F.pow x 2)
                eq_refl eq_refl
                (fun H => Htmp_z2 H) Hz2_v H2)
      as [Htmp_v Hframe_2].
    cbn [LFp loc_var loc_type] in Htmp_v, Hframe_2.
    rewrite F.pow_pow_l in Htmp_v.
    change (2 * 2)%N with 4%N in Htmp_v.
    assert (Hax_02 : Fp25519_holds rs02 a_loc.(loc_var) x)
      by (apply Hframe_2; [exact Ha_tmp | exact Hax_01]).
    assert (Hz2_02 : Fp25519_holds rs02 "z2" (F.pow x 2))
      by (apply Hframe_2; [discriminate | exact Hz2_v]).
    clear Hax_01 Hz2_v Hframe_2.

    (* --- Step 3: sqr_call "scratch" "tmp" => scratch = x^8 --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs03 [H3 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (sqr_correct (LFp "scratch") (LFp "tmp") rs02 rs03 (F.pow x 4)
                eq_refl eq_refl
                (fun H => Hscratch_tmp H) Htmp_v H3)
      as [Hscr_v Hframe_3].
    cbn [LFp loc_var loc_type] in Hscr_v, Hframe_3.
    rewrite F.pow_pow_l in Hscr_v.
    change (4 * 2)%N with 8%N in Hscr_v.
    assert (Hax_03 : Fp25519_holds rs03 a_loc.(loc_var) x)
      by (apply Hframe_3; [exact Ha_scratch | exact Hax_02]).
    assert (Htmp_03 : Fp25519_holds rs03 "tmp" (F.pow x 4))
      by (apply Hframe_3; [discriminate | exact Htmp_v]).
    assert (Hz2_03 : Fp25519_holds rs03 "z2" (F.pow x 2))
      by (apply Hframe_3; [discriminate | exact Hz2_02]).
    clear Hax_02 Htmp_v Hz2_02 Hframe_3.

    (* --- Step 4: copy_call "tmp" "scratch" => tmp = x^8 --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs04 [H4 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (copy_correct (LFp "tmp") (LFp "scratch") rs03 rs04 (F.pow x 8)
                eq_refl eq_refl
                (fun H => Htmp_scratch H) Hscr_v H4)
      as [Htmp_v Hframe_4].
    cbn [LFp loc_var loc_type] in Htmp_v, Hframe_4.
    assert (Hax_04 : Fp25519_holds rs04 a_loc.(loc_var) x)
      by (apply Hframe_4; [exact Ha_tmp | exact Hax_03]).
    assert (Hz2_04 : Fp25519_holds rs04 "z2" (F.pow x 2))
      by (apply Hframe_4; [discriminate | exact Hz2_03]).
    clear Hax_03 Hscr_v Hz2_03 Hframe_4 Htmp_03.

    (* --- Step 5: REdCall fe25519_mul (LFp "z9") [LFp "tmp"; a_loc]
                   => z9 = x^9 --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs05 [H5 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    assert (Hne_z9_a : (LFp "z9").(loc_var) <> a_loc.(loc_var))
      by (cbn; intro Heq; apply Ha_z9; symmetry; exact Heq).
    pose proof (mul_correct (LFp "z9") (LFp "tmp") a_loc rs04 rs05
                (F.pow x 8) x
                eq_refl eq_refl Halt
                (ltac:(cbn; discriminate))
                Hne_z9_a Htmp_v Hax_04 H5)
      as [Hz9_v Hframe_5].
    cbn [LFp loc_var loc_type] in Hz9_v, Hframe_5.
    (* z9 = x^8 · x.  Rewrite as x^9 via pow_add_r. *)
    replace (F.mul (F.pow x 8) x) with (F.pow x 9) in Hz9_v.
    2:{ change 9%N with (8 + 1)%N.
        rewrite F.pow_add_r.
        f_equal. apply F.pow_1_r. }
    assert (Hax_05 : Fp25519_holds rs05 a_loc.(loc_var) x)
      by (apply Hframe_5; [exact Ha_z9 | exact Hax_04]).
    assert (Htmp_05 : Fp25519_holds rs05 "tmp" (F.pow x 8))
      by (apply Hframe_5; [discriminate | exact Htmp_v]).
    assert (Hz2_05 : Fp25519_holds rs05 "z2" (F.pow x 2))
      by (apply Hframe_5; [discriminate | exact Hz2_04]).
    clear Hax_04 Htmp_v Hz2_04 Hframe_5 Hne_z9_a.

    (* --- Step 6: mul_call "z11" "z9" "z2" => z11 = x^11 --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs06 [H6 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (mul_correct (LFp "z11") (LFp "z9") (LFp "z2") rs05 rs06
                (F.pow x 9) (F.pow x 2)
                eq_refl eq_refl eq_refl
                (ltac:(cbn; discriminate)) (ltac:(cbn; discriminate))
                Hz9_v Hz2_05 H6)
      as [Hz11_v Hframe_6].
    cbn [LFp loc_var loc_type] in Hz11_v, Hframe_6.
    replace (F.mul (F.pow x 9) (F.pow x 2)) with (F.pow x 11) in Hz11_v
      by (rewrite <- F.pow_add_r; reflexivity).
    assert (Hax_06 : Fp25519_holds rs06 a_loc.(loc_var) x)
      by (apply Hframe_6; [exact Ha_z11 | exact Hax_05]).
    assert (Htmp_06 : Fp25519_holds rs06 "tmp" (F.pow x 8))
      by (apply Hframe_6; [discriminate | exact Htmp_05]).
    assert (Hz9_06 : Fp25519_holds rs06 "z9" (F.pow x 9))
      by (apply Hframe_6; [discriminate | exact Hz9_v]).
    assert (Hz2_06 : Fp25519_holds rs06 "z2" (F.pow x 2))
      by (apply Hframe_6; [discriminate | exact Hz2_05]).
    clear Hax_05 Hz9_v Hz2_05 Htmp_05 Hframe_6.

    (* --- Step 7: sqr_call "tmp" "z11" => tmp = x^22 --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs07 [H7 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (sqr_correct (LFp "tmp") (LFp "z11") rs06 rs07 (F.pow x 11)
                eq_refl eq_refl
                (ltac:(cbn; discriminate)) Hz11_v H7)
      as [Htmp_v Hframe_7].
    cbn [LFp loc_var loc_type] in Htmp_v, Hframe_7.
    rewrite F.pow_pow_l in Htmp_v.
    change (11 * 2)%N with 22%N in Htmp_v.
    assert (Hax_07 : Fp25519_holds rs07 a_loc.(loc_var) x)
      by (apply Hframe_7; [exact Ha_tmp | exact Hax_06]).
    assert (Hz9_07 : Fp25519_holds rs07 "z9" (F.pow x 9))
      by (apply Hframe_7; [discriminate | exact Hz9_06]).
    assert (Hz11_07 : Fp25519_holds rs07 "z11" (F.pow x 11))
      by (apply Hframe_7; [discriminate | exact Hz11_v]).
    assert (Hz2_07 : Fp25519_holds rs07 "z2" (F.pow x 2))
      by (apply Hframe_7; [discriminate | exact Hz2_06]).
    clear Hax_06 Hz9_06 Hz11_v Hz2_06 Htmp_06 Hframe_7.

    (* --- Step 8: mul_call "z2_5_0" "tmp" "z9" => z2_5_0 = x^31 --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs08 [H8 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (mul_correct (LFp "z2_5_0") (LFp "tmp") (LFp "z9") rs07 rs08
                (F.pow x 22) (F.pow x 9)
                eq_refl eq_refl eq_refl
                (ltac:(cbn; discriminate)) (ltac:(cbn; discriminate))
                Htmp_v Hz9_07 H8)
      as [Hz2_5_v Hframe_8].
    cbn [LFp loc_var loc_type] in Hz2_5_v, Hframe_8.
    replace (F.mul (F.pow x 22) (F.pow x 9)) with (F.pow x 31) in Hz2_5_v
      by (rewrite <- F.pow_add_r; reflexivity).
    assert (Hax_08 : Fp25519_holds rs08 a_loc.(loc_var) x)
      by (apply Hframe_8; [exact Ha_z2_5_0 | exact Hax_07]).
    assert (Hz9_08 : Fp25519_holds rs08 "z9" (F.pow x 9))
      by (apply Hframe_8; [discriminate | exact Hz9_07]).
    assert (Hz11_08 : Fp25519_holds rs08 "z11" (F.pow x 11))
      by (apply Hframe_8; [discriminate | exact Hz11_07]).
    clear Hax_07 Hz9_07 Hz11_07 Htmp_v Hz2_07 Hframe_8.

    (* --- Step 9: sqr_call "tmp" "z2_5_0" => tmp = x^62 --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs09 [H9 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (sqr_correct (LFp "tmp") (LFp "z2_5_0") rs08 rs09 (F.pow x 31)
                eq_refl eq_refl
                (ltac:(cbn; discriminate)) Hz2_5_v H9)
      as [Htmp_v Hframe_9].
    cbn [LFp loc_var loc_type] in Htmp_v, Hframe_9.
    rewrite F.pow_pow_l in Htmp_v.
    change (31 * 2)%N with 62%N in Htmp_v.
    assert (Hax_09 : Fp25519_holds rs09 a_loc.(loc_var) x)
      by (apply Hframe_9; [exact Ha_tmp | exact Hax_08]).
    assert (Hz9_09 : Fp25519_holds rs09 "z9" (F.pow x 9))
      by (apply Hframe_9; [discriminate | exact Hz9_08]).
    assert (Hz11_09 : Fp25519_holds rs09 "z11" (F.pow x 11))
      by (apply Hframe_9; [discriminate | exact Hz11_08]).
    assert (Hz2_5_09 : Fp25519_holds rs09 "z2_5_0" (F.pow x 31))
      by (apply Hframe_9; [discriminate | exact Hz2_5_v]).
    clear Hax_08 Hz9_08 Hz11_08 Hz2_5_v Hframe_9.

    (* --- Step 10: sqrN 4 "tmp" "scratch" => tmp = x^(62 · 2^4) = x^992 --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs10 [H10 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (sqrN_correct 4 "tmp" "scratch" rs09 rs10 (F.pow x 62)
                (ltac:(discriminate)) Htmp_v H10)
      as [Htmp_v' Hframe_10].
    (* (x^62)^(2^4) = x^(62 · 16) = x^992 *)
    rewrite F.pow_pow_l in Htmp_v'.
    change (62 * N.pow 2 (N.of_nat 4))%N with 992%N in Htmp_v'.
    assert (Hax_10 : Fp25519_holds rs10 a_loc.(loc_var) x)
      by (apply Hframe_10; [exact Ha_tmp | exact Ha_scratch | exact Hax_09]).
    assert (Hz9_10 : Fp25519_holds rs10 "z9" (F.pow x 9))
      by (apply Hframe_10; [discriminate | discriminate | exact Hz9_09]).
    assert (Hz11_10 : Fp25519_holds rs10 "z11" (F.pow x 11))
      by (apply Hframe_10; [discriminate | discriminate | exact Hz11_09]).
    assert (Hz2_5_10 : Fp25519_holds rs10 "z2_5_0" (F.pow x 31))
      by (apply Hframe_10; [discriminate | discriminate | exact Hz2_5_09]).
    clear Hax_09 Hz9_09 Hz11_09 Hz2_5_09 Htmp_v Hframe_10.

    (* --- Step 11: mul_call "z2_10_0" "tmp" "z2_5_0" => z2_10_0 = x^1023 --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs11 [H11 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (mul_correct (LFp "z2_10_0") (LFp "tmp") (LFp "z2_5_0") rs10 rs11
                (F.pow x 992) (F.pow x 31)
                eq_refl eq_refl eq_refl
                (ltac:(cbn; discriminate)) (ltac:(cbn; discriminate))
                Htmp_v' Hz2_5_10 H11)
      as [Hz2_10_v Hframe_11].
    cbn [LFp loc_var loc_type] in Hz2_10_v, Hframe_11.
    replace (F.mul (F.pow x 992) (F.pow x 31)) with (F.pow x 1023) in Hz2_10_v
      by (rewrite <- F.pow_add_r; reflexivity).
    assert (Hax_11 : Fp25519_holds rs11 a_loc.(loc_var) x)
      by (apply Hframe_11; [exact Ha_z2_10_0 | exact Hax_10]).
    assert (Hz9_11 : Fp25519_holds rs11 "z9" (F.pow x 9))
      by (apply Hframe_11; [discriminate | exact Hz9_10]).
    assert (Hz11_11 : Fp25519_holds rs11 "z11" (F.pow x 11))
      by (apply Hframe_11; [discriminate | exact Hz11_10]).
    assert (Hz2_5_11 : Fp25519_holds rs11 "z2_5_0" (F.pow x 31))
      by (apply Hframe_11; [discriminate | exact Hz2_5_10]).
    clear Hax_10 Hz9_10 Hz11_10 Hz2_5_10 Htmp_v' Hframe_11.

    (* --- Step 12: sqr_call "tmp" "z2_10_0" => tmp = x^2046 --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs12 [H12 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (sqr_correct (LFp "tmp") (LFp "z2_10_0") rs11 rs12 (F.pow x 1023)
                eq_refl eq_refl
                (ltac:(cbn; discriminate)) Hz2_10_v H12)
      as [Htmp_v Hframe_12].
    cbn [LFp loc_var loc_type] in Htmp_v, Hframe_12.
    rewrite F.pow_pow_l in Htmp_v.
    change (1023 * 2)%N with 2046%N in Htmp_v.
    assert (Hax_12 : Fp25519_holds rs12 a_loc.(loc_var) x)
      by (apply Hframe_12; [exact Ha_tmp | exact Hax_11]).
    assert (Hz9_12 : Fp25519_holds rs12 "z9" (F.pow x 9))
      by (apply Hframe_12; [discriminate | exact Hz9_11]).
    assert (Hz11_12 : Fp25519_holds rs12 "z11" (F.pow x 11))
      by (apply Hframe_12; [discriminate | exact Hz11_11]).
    assert (Hz2_5_12 : Fp25519_holds rs12 "z2_5_0" (F.pow x 31))
      by (apply Hframe_12; [discriminate | exact Hz2_5_11]).
    assert (Hz2_10_12 : Fp25519_holds rs12 "z2_10_0" (F.pow x 1023))
      by (apply Hframe_12; [discriminate | exact Hz2_10_v]).
    clear Hax_11 Hz9_11 Hz11_11 Hz2_5_11 Hz2_10_v Hframe_12.

    (* --- Step 13: sqrN 9 "tmp" "scratch" => tmp = x^(2046 · 2^9) = x^1047552 --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs13 [H13 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (sqrN_correct 9 "tmp" "scratch" rs12 rs13 (F.pow x 2046)
                (ltac:(discriminate)) Htmp_v H13)
      as [Htmp_v' Hframe_13].
    rewrite F.pow_pow_l in Htmp_v'.
    change (2046 * N.pow 2 (N.of_nat 9))%N with 1047552%N in Htmp_v'.
    assert (Hax_13 : Fp25519_holds rs13 a_loc.(loc_var) x)
      by (apply Hframe_13; [exact Ha_tmp | exact Ha_scratch | exact Hax_12]).
    assert (Hz9_13 : Fp25519_holds rs13 "z9" (F.pow x 9))
      by (apply Hframe_13; [discriminate | discriminate | exact Hz9_12]).
    assert (Hz11_13 : Fp25519_holds rs13 "z11" (F.pow x 11))
      by (apply Hframe_13; [discriminate | discriminate | exact Hz11_12]).
    assert (Hz2_5_13 : Fp25519_holds rs13 "z2_5_0" (F.pow x 31))
      by (apply Hframe_13; [discriminate | discriminate | exact Hz2_5_12]).
    assert (Hz2_10_13 : Fp25519_holds rs13 "z2_10_0" (F.pow x 1023))
      by (apply Hframe_13; [discriminate | discriminate | exact Hz2_10_12]).
    clear Hax_12 Hz9_12 Hz11_12 Hz2_5_12 Hz2_10_12 Htmp_v Hframe_13.

    (* --- Step 14: mul_call "z2_20_0" "tmp" "z2_10_0" => z2_20_0 = x^(2^20-1) = x^1048575 --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs14 [H14 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (mul_correct (LFp "z2_20_0") (LFp "tmp") (LFp "z2_10_0") rs13 rs14
                (F.pow x 1047552) (F.pow x 1023)
                eq_refl eq_refl eq_refl
                (ltac:(cbn; discriminate)) (ltac:(cbn; discriminate))
                Htmp_v' Hz2_10_13 H14)
      as [Hz2_20_v Hframe_14].
    cbn [LFp loc_var loc_type] in Hz2_20_v, Hframe_14.
    replace (F.mul (F.pow x 1047552) (F.pow x 1023)) with (F.pow x 1048575) in Hz2_20_v
      by (rewrite <- F.pow_add_r; reflexivity).
    assert (Hax_14 : Fp25519_holds rs14 a_loc.(loc_var) x)
      by (apply Hframe_14; [exact Ha_z2_20_0 | exact Hax_13]).
    assert (Hz9_14 : Fp25519_holds rs14 "z9" (F.pow x 9))
      by (apply Hframe_14; [discriminate | exact Hz9_13]).
    assert (Hz11_14 : Fp25519_holds rs14 "z11" (F.pow x 11))
      by (apply Hframe_14; [discriminate | exact Hz11_13]).
    assert (Hz2_5_14 : Fp25519_holds rs14 "z2_5_0" (F.pow x 31))
      by (apply Hframe_14; [discriminate | exact Hz2_5_13]).
    assert (Hz2_10_14 : Fp25519_holds rs14 "z2_10_0" (F.pow x 1023))
      by (apply Hframe_14; [discriminate | exact Hz2_10_13]).
    clear Hax_13 Hz9_13 Hz11_13 Hz2_5_13 Hz2_10_13 Htmp_v' Hframe_14.

    (* --- Step 15: sqr_call "tmp" "z2_20_0" => tmp = x^2097150 --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs15 [H15 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (sqr_correct (LFp "tmp") (LFp "z2_20_0") rs14 rs15 (F.pow x 1048575)
                eq_refl eq_refl
                (ltac:(cbn; discriminate)) Hz2_20_v H15)
      as [Htmp_v Hframe_15].
    cbn [LFp loc_var loc_type] in Htmp_v, Hframe_15.
    rewrite F.pow_pow_l in Htmp_v.
    change (1048575 * 2)%N with 2097150%N in Htmp_v.
    assert (Hax_15 : Fp25519_holds rs15 a_loc.(loc_var) x)
      by (apply Hframe_15; [exact Ha_tmp | exact Hax_14]).
    assert (Hz9_15 : Fp25519_holds rs15 "z9" (F.pow x 9))
      by (apply Hframe_15; [discriminate | exact Hz9_14]).
    assert (Hz11_15 : Fp25519_holds rs15 "z11" (F.pow x 11))
      by (apply Hframe_15; [discriminate | exact Hz11_14]).
    assert (Hz2_5_15 : Fp25519_holds rs15 "z2_5_0" (F.pow x 31))
      by (apply Hframe_15; [discriminate | exact Hz2_5_14]).
    assert (Hz2_10_15 : Fp25519_holds rs15 "z2_10_0" (F.pow x 1023))
      by (apply Hframe_15; [discriminate | exact Hz2_10_14]).
    assert (Hz2_20_15 : Fp25519_holds rs15 "z2_20_0" (F.pow x 1048575))
      by (apply Hframe_15; [discriminate | exact Hz2_20_v]).
    clear Hax_14 Hz9_14 Hz11_14 Hz2_5_14 Hz2_10_14 Hz2_20_v Hframe_15.

    (* --- Step 16: sqrN 19 "tmp" "scratch" => tmp = x^(2^20-1)·2^20 --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs16 [H16 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (sqrN_correct 19 "tmp" "scratch" rs15 rs16 (F.pow x 2097150)
                (ltac:(discriminate)) Htmp_v H16)
      as [Htmp_v' Hframe_16].
    rewrite F.pow_pow_l in Htmp_v'.
    (* 2097150 · 2^19 = 1099510579200 = (2^20-1)·2^20 *)
    change (2097150 * N.pow 2 (N.of_nat 19))%N with 1099510579200%N in Htmp_v'.
    assert (Hax_16 : Fp25519_holds rs16 a_loc.(loc_var) x)
      by (apply Hframe_16; [exact Ha_tmp | exact Ha_scratch | exact Hax_15]).
    assert (Hz9_16 : Fp25519_holds rs16 "z9" (F.pow x 9))
      by (apply Hframe_16; [discriminate | discriminate | exact Hz9_15]).
    assert (Hz11_16 : Fp25519_holds rs16 "z11" (F.pow x 11))
      by (apply Hframe_16; [discriminate | discriminate | exact Hz11_15]).
    assert (Hz2_5_16 : Fp25519_holds rs16 "z2_5_0" (F.pow x 31))
      by (apply Hframe_16; [discriminate | discriminate | exact Hz2_5_15]).
    assert (Hz2_10_16 : Fp25519_holds rs16 "z2_10_0" (F.pow x 1023))
      by (apply Hframe_16; [discriminate | discriminate | exact Hz2_10_15]).
    assert (Hz2_20_16 : Fp25519_holds rs16 "z2_20_0" (F.pow x 1048575))
      by (apply Hframe_16; [discriminate | discriminate | exact Hz2_20_15]).
    clear Hax_15 Hz9_15 Hz11_15 Hz2_5_15 Hz2_10_15 Hz2_20_15 Htmp_v Hframe_16.

    (* --- Step 17: mul_call "z2_40_0" "tmp" "z2_20_0" => z2_40_0 = x^(2^40-1) --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs17 [H17 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (mul_correct (LFp "z2_40_0") (LFp "tmp") (LFp "z2_20_0") rs16 rs17
                (F.pow x 1099510579200) (F.pow x 1048575)
                eq_refl eq_refl eq_refl
                (ltac:(cbn; discriminate)) (ltac:(cbn; discriminate))
                Htmp_v' Hz2_20_16 H17)
      as [Hz2_40_v Hframe_17].
    cbn [LFp loc_var loc_type] in Hz2_40_v, Hframe_17.
    replace (F.mul (F.pow x 1099510579200) (F.pow x 1048575))
      with (F.pow x 1099511627775) in Hz2_40_v
      by (rewrite <- F.pow_add_r; reflexivity).
    assert (Hax_17 : Fp25519_holds rs17 a_loc.(loc_var) x)
      by (apply Hframe_17; [exact Ha_z2_40_0 | exact Hax_16]).
    assert (Hz9_17 : Fp25519_holds rs17 "z9" (F.pow x 9))
      by (apply Hframe_17; [discriminate | exact Hz9_16]).
    assert (Hz11_17 : Fp25519_holds rs17 "z11" (F.pow x 11))
      by (apply Hframe_17; [discriminate | exact Hz11_16]).
    assert (Hz2_5_17 : Fp25519_holds rs17 "z2_5_0" (F.pow x 31))
      by (apply Hframe_17; [discriminate | exact Hz2_5_16]).
    assert (Hz2_10_17 : Fp25519_holds rs17 "z2_10_0" (F.pow x 1023))
      by (apply Hframe_17; [discriminate | exact Hz2_10_16]).
    clear Hax_16 Hz9_16 Hz11_16 Hz2_5_16 Hz2_10_16 Hz2_20_16 Htmp_v' Hframe_17.

    (* --- Step 18: sqr_call "tmp" "z2_40_0" => tmp = x^(2 · (2^40-1)) --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs18 [H18 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (sqr_correct (LFp "tmp") (LFp "z2_40_0") rs17 rs18 (F.pow x 1099511627775)
                eq_refl eq_refl
                (ltac:(cbn; discriminate)) Hz2_40_v H18)
      as [Htmp_v Hframe_18].
    cbn [LFp loc_var loc_type] in Htmp_v, Hframe_18.
    rewrite F.pow_pow_l in Htmp_v.
    change (1099511627775 * 2)%N with 2199023255550%N in Htmp_v.
    assert (Hax_18 : Fp25519_holds rs18 a_loc.(loc_var) x)
      by (apply Hframe_18; [exact Ha_tmp | exact Hax_17]).
    assert (Hz9_18 : Fp25519_holds rs18 "z9" (F.pow x 9))
      by (apply Hframe_18; [discriminate | exact Hz9_17]).
    assert (Hz11_18 : Fp25519_holds rs18 "z11" (F.pow x 11))
      by (apply Hframe_18; [discriminate | exact Hz11_17]).
    assert (Hz2_5_18 : Fp25519_holds rs18 "z2_5_0" (F.pow x 31))
      by (apply Hframe_18; [discriminate | exact Hz2_5_17]).
    assert (Hz2_10_18 : Fp25519_holds rs18 "z2_10_0" (F.pow x 1023))
      by (apply Hframe_18; [discriminate | exact Hz2_10_17]).
    clear Hax_17 Hz9_17 Hz11_17 Hz2_5_17 Hz2_10_17 Hz2_40_v Hframe_18.

    (* --- Step 19: sqrN 9 "tmp" "scratch" => tmp = x^((2^40-1) · 2^10) = x^(2^50 - 2^10) --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs19 [H19 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (sqrN_correct 9 "tmp" "scratch" rs18 rs19 (F.pow x 2199023255550)
                (ltac:(discriminate)) Htmp_v H19)
      as [Htmp_v' Hframe_19].
    rewrite F.pow_pow_l in Htmp_v'.
    (* 2199023255550 · 2^9 = 1125899906841600 = (2^40-1) · 2^10 = 2^50 - 2^10 *)
    change (2199023255550 * N.pow 2 (N.of_nat 9))%N with 1125899906841600%N in Htmp_v'.
    assert (Hax_19 : Fp25519_holds rs19 a_loc.(loc_var) x)
      by (apply Hframe_19; [exact Ha_tmp | exact Ha_scratch | exact Hax_18]).
    assert (Hz9_19 : Fp25519_holds rs19 "z9" (F.pow x 9))
      by (apply Hframe_19; [discriminate | discriminate | exact Hz9_18]).
    assert (Hz11_19 : Fp25519_holds rs19 "z11" (F.pow x 11))
      by (apply Hframe_19; [discriminate | discriminate | exact Hz11_18]).
    assert (Hz2_5_19 : Fp25519_holds rs19 "z2_5_0" (F.pow x 31))
      by (apply Hframe_19; [discriminate | discriminate | exact Hz2_5_18]).
    assert (Hz2_10_19 : Fp25519_holds rs19 "z2_10_0" (F.pow x 1023))
      by (apply Hframe_19; [discriminate | discriminate | exact Hz2_10_18]).
    clear Hax_18 Hz9_18 Hz11_18 Hz2_5_18 Hz2_10_18 Htmp_v Hframe_19.

    (* --- Step 20: mul_call "z2_50_0" "tmp" "z2_10_0" => z2_50_0 = x^(2^50-1) --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs20 [H20 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (mul_correct (LFp "z2_50_0") (LFp "tmp") (LFp "z2_10_0") rs19 rs20
                (F.pow x 1125899906841600) (F.pow x 1023)
                eq_refl eq_refl eq_refl
                (ltac:(cbn; discriminate)) (ltac:(cbn; discriminate))
                Htmp_v' Hz2_10_19 H20)
      as [Hz2_50_v Hframe_20].
    cbn [LFp loc_var loc_type] in Hz2_50_v, Hframe_20.
    (* 1125899906841600 + 1023 = 1125899906842623 = 2^50 - 1 *)
    replace (F.mul (F.pow x 1125899906841600) (F.pow x 1023))
      with (F.pow x 1125899906842623) in Hz2_50_v
      by (rewrite <- F.pow_add_r; reflexivity).
    assert (Hax_20 : Fp25519_holds rs20 a_loc.(loc_var) x)
      by (apply Hframe_20; [exact Ha_z2_50_0 | exact Hax_19]).
    assert (Hz9_20 : Fp25519_holds rs20 "z9" (F.pow x 9))
      by (apply Hframe_20; [discriminate | exact Hz9_19]).
    assert (Hz11_20 : Fp25519_holds rs20 "z11" (F.pow x 11))
      by (apply Hframe_20; [discriminate | exact Hz11_19]).
    assert (Hz2_5_20 : Fp25519_holds rs20 "z2_5_0" (F.pow x 31))
      by (apply Hframe_20; [discriminate | exact Hz2_5_19]).
    clear Hax_19 Hz9_19 Hz11_19 Hz2_5_19 Hz2_10_19 Htmp_v' Hframe_20.

    (* --- Step 21: sqr_call "tmp" "z2_50_0" => tmp = x^(2 · (2^50-1)) --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs21 [H21 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (sqr_correct (LFp "tmp") (LFp "z2_50_0") rs20 rs21 (F.pow x 1125899906842623)
                eq_refl eq_refl
                (ltac:(cbn; discriminate)) Hz2_50_v H21)
      as [Htmp_v Hframe_21].
    cbn [LFp loc_var loc_type] in Htmp_v, Hframe_21.
    rewrite F.pow_pow_l in Htmp_v.
    change (1125899906842623 * 2)%N with 2251799813685246%N in Htmp_v.
    assert (Hax_21 : Fp25519_holds rs21 a_loc.(loc_var) x)
      by (apply Hframe_21; [exact Ha_tmp | exact Hax_20]).
    assert (Hz9_21 : Fp25519_holds rs21 "z9" (F.pow x 9))
      by (apply Hframe_21; [discriminate | exact Hz9_20]).
    assert (Hz11_21 : Fp25519_holds rs21 "z11" (F.pow x 11))
      by (apply Hframe_21; [discriminate | exact Hz11_20]).
    assert (Hz2_5_21 : Fp25519_holds rs21 "z2_5_0" (F.pow x 31))
      by (apply Hframe_21; [discriminate | exact Hz2_5_20]).
    assert (Hz2_50_21 : Fp25519_holds rs21 "z2_50_0" (F.pow x 1125899906842623))
      by (apply Hframe_21; [discriminate | exact Hz2_50_v]).
    clear Hax_20 Hz9_20 Hz11_20 Hz2_5_20 Hz2_50_v Hframe_21.

    (* --- Step 22: sqrN 49 "tmp" "scratch" => tmp = x^((2^50-1)·2^50) = x^(2^100 - 2^50) --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs22 [H22 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (sqrN_correct 49 "tmp" "scratch" rs21 rs22 (F.pow x 2251799813685246)
                (ltac:(discriminate)) Htmp_v H22)
      as [Htmp_v' Hframe_22].
    rewrite F.pow_pow_l in Htmp_v'.
    (* 2251799813685246 · 2^49 = 1267650600228228054527279890432, but actually
       we want (2^50-1) · 2^50 = 2^100 - 2^50 = 1267650600228228055644210753536.
       Wait — let me recompute.  2 * (2^50-1) = 2^51 - 2 = 2251799813685246.
       (2^51-2) * 2^49 = 2^100 - 2^50 = 1267650600228229401496703205376 - 1125899906842624.
       2^100 = 1267650600228229401496703205376.  Then 2^100 - 2^50 = 1267650600228228275596796362752.
       Let me just check via vm_compute. *)
    change (2251799813685246 * N.pow 2 (N.of_nat 49))%N
      with 1267650600228228275596796362752%N in Htmp_v'.
    assert (Hax_22 : Fp25519_holds rs22 a_loc.(loc_var) x)
      by (apply Hframe_22; [exact Ha_tmp | exact Ha_scratch | exact Hax_21]).
    assert (Hz9_22 : Fp25519_holds rs22 "z9" (F.pow x 9))
      by (apply Hframe_22; [discriminate | discriminate | exact Hz9_21]).
    assert (Hz11_22 : Fp25519_holds rs22 "z11" (F.pow x 11))
      by (apply Hframe_22; [discriminate | discriminate | exact Hz11_21]).
    assert (Hz2_5_22 : Fp25519_holds rs22 "z2_5_0" (F.pow x 31))
      by (apply Hframe_22; [discriminate | discriminate | exact Hz2_5_21]).
    assert (Hz2_50_22 : Fp25519_holds rs22 "z2_50_0" (F.pow x 1125899906842623))
      by (apply Hframe_22; [discriminate | discriminate | exact Hz2_50_21]).
    clear Hax_21 Hz9_21 Hz11_21 Hz2_5_21 Hz2_50_21 Htmp_v Hframe_22.

    (* --- Step 23: mul_call "z2_100_0" "tmp" "z2_50_0" => z2_100_0 = x^(2^100-1) --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs23 [H23 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (mul_correct (LFp "z2_100_0") (LFp "tmp") (LFp "z2_50_0") rs22 rs23
                (F.pow x 1267650600228228275596796362752) (F.pow x 1125899906842623)
                eq_refl eq_refl eq_refl
                (ltac:(cbn; discriminate)) (ltac:(cbn; discriminate))
                Htmp_v' Hz2_50_22 H23)
      as [Hz2_100_v Hframe_23].
    cbn [LFp loc_var loc_type] in Hz2_100_v, Hframe_23.
    (* 2^100 - 2^50 + 2^50 - 1 = 2^100 - 1 = 1267650600228229401496703205375 *)
    replace (F.mul (F.pow x 1267650600228228275596796362752)
                   (F.pow x 1125899906842623))
      with (F.pow x 1267650600228229401496703205375) in Hz2_100_v
      by (rewrite <- F.pow_add_r; reflexivity).
    assert (Hax_23 : Fp25519_holds rs23 a_loc.(loc_var) x)
      by (apply Hframe_23; [exact Ha_z2_100_0 | exact Hax_22]).
    assert (Hz9_23 : Fp25519_holds rs23 "z9" (F.pow x 9))
      by (apply Hframe_23; [discriminate | exact Hz9_22]).
    assert (Hz11_23 : Fp25519_holds rs23 "z11" (F.pow x 11))
      by (apply Hframe_23; [discriminate | exact Hz11_22]).
    assert (Hz2_50_23 : Fp25519_holds rs23 "z2_50_0" (F.pow x 1125899906842623))
      by (apply Hframe_23; [discriminate | exact Hz2_50_22]).
    clear Hax_22 Hz9_22 Hz11_22 Hz2_5_22 Hz2_50_22 Htmp_v' Hframe_23.

    (* --- Step 24: sqr_call "tmp" "z2_100_0" => tmp = x^(2(2^100-1)) --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs24 [H24 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (sqr_correct (LFp "tmp") (LFp "z2_100_0") rs23 rs24
                (F.pow x 1267650600228229401496703205375)
                eq_refl eq_refl
                (ltac:(cbn; discriminate)) Hz2_100_v H24)
      as [Htmp_v Hframe_24].
    cbn [LFp loc_var loc_type] in Htmp_v, Hframe_24.
    rewrite F.pow_pow_l in Htmp_v.
    (* 1267650600228229401496703205375 * 2 = 2535301200456458802993406410750 *)
    change (1267650600228229401496703205375 * 2)%N
      with 2535301200456458802993406410750%N in Htmp_v.
    assert (Hax_24 : Fp25519_holds rs24 a_loc.(loc_var) x)
      by (apply Hframe_24; [exact Ha_tmp | exact Hax_23]).
    assert (Hz9_24 : Fp25519_holds rs24 "z9" (F.pow x 9))
      by (apply Hframe_24; [discriminate | exact Hz9_23]).
    assert (Hz11_24 : Fp25519_holds rs24 "z11" (F.pow x 11))
      by (apply Hframe_24; [discriminate | exact Hz11_23]).
    assert (Hz2_50_24 : Fp25519_holds rs24 "z2_50_0" (F.pow x 1125899906842623))
      by (apply Hframe_24; [discriminate | exact Hz2_50_23]).
    assert (Hz2_100_24 : Fp25519_holds rs24 "z2_100_0" (F.pow x 1267650600228229401496703205375))
      by (apply Hframe_24; [discriminate | exact Hz2_100_v]).
    clear Hax_23 Hz9_23 Hz11_23 Hz2_50_23 Hz2_100_v Hframe_24.

    (* --- Step 25: sqrN 99 "tmp" "scratch" => tmp = x^((2^100-1) · 2^100) --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs25 [H25 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (sqrN_correct 99 "tmp" "scratch" rs24 rs25
                (F.pow x 2535301200456458802993406410750)
                (ltac:(discriminate)) Htmp_v H25)
      as [Htmp_v' Hframe_25].
    rewrite F.pow_pow_l in Htmp_v'.
    (* 2535301200456458802993406410750 * 2^99 = (2^100-1)*2^100 = 2^200 - 2^100 *)
    change (2535301200456458802993406410750 * N.pow 2 (N.of_nat 99))%N
      with 1606938044258990275541962092339894951921974764381296132096000%N in Htmp_v'.
    assert (Hax_25 : Fp25519_holds rs25 a_loc.(loc_var) x)
      by (apply Hframe_25; [exact Ha_tmp | exact Ha_scratch | exact Hax_24]).
    assert (Hz9_25 : Fp25519_holds rs25 "z9" (F.pow x 9))
      by (apply Hframe_25; [discriminate | discriminate | exact Hz9_24]).
    assert (Hz11_25 : Fp25519_holds rs25 "z11" (F.pow x 11))
      by (apply Hframe_25; [discriminate | discriminate | exact Hz11_24]).
    assert (Hz2_50_25 : Fp25519_holds rs25 "z2_50_0" (F.pow x 1125899906842623))
      by (apply Hframe_25; [discriminate | discriminate | exact Hz2_50_24]).
    assert (Hz2_100_25 : Fp25519_holds rs25 "z2_100_0" (F.pow x 1267650600228229401496703205375))
      by (apply Hframe_25; [discriminate | discriminate | exact Hz2_100_24]).
    clear Hax_24 Hz9_24 Hz11_24 Hz2_50_24 Htmp_v Hframe_25.

    (* --- Step 26: mul_call "t2" "tmp" "z2_100_0" => t2 = x^(2^200-1) --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs26 [H26 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (mul_correct (LFp "t2") (LFp "tmp") (LFp "z2_100_0") rs25 rs26
                (F.pow x 1606938044258990275541962092339894951921974764381296132096000)
                (F.pow x 1267650600228229401496703205375)
                eq_refl eq_refl eq_refl
                (ltac:(cbn; discriminate)) (ltac:(cbn; discriminate))
                Htmp_v' Hz2_100_25 H26)
      as [Ht2_v Hframe_26].
    cbn [LFp loc_var loc_type] in Ht2_v, Hframe_26.
    (* 2^200 - 1 = 1606938044258990275541962092341162602522202993782792835301375 *)
    replace (F.mul (F.pow x 1606938044258990275541962092339894951921974764381296132096000)
                   (F.pow x 1267650600228229401496703205375))
      with (F.pow x 1606938044258990275541962092341162602522202993782792835301375%N) in Ht2_v
      by (rewrite <- F.pow_add_r; reflexivity).
    assert (Hax_26 : Fp25519_holds rs26 a_loc.(loc_var) x)
      by (apply Hframe_26; [exact Ha_t2 | exact Hax_25]).
    assert (Hz9_26 : Fp25519_holds rs26 "z9" (F.pow x 9))
      by (apply Hframe_26; [discriminate | exact Hz9_25]).
    assert (Hz11_26 : Fp25519_holds rs26 "z11" (F.pow x 11))
      by (apply Hframe_26; [discriminate | exact Hz11_25]).
    assert (Hz2_50_26 : Fp25519_holds rs26 "z2_50_0" (F.pow x 1125899906842623))
      by (apply Hframe_26; [discriminate | exact Hz2_50_25]).
    clear Hax_25 Hz9_25 Hz11_25 Hz2_50_25 Hz2_100_25 Htmp_v' Hframe_26.

    (* --- Step 27: sqr_call "tmp" "t2" => tmp = x^(2(2^200-1)) --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs27 [H27 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (sqr_correct (LFp "tmp") (LFp "t2") rs26 rs27
                (F.pow x 1606938044258990275541962092341162602522202993782792835301375%N)
                eq_refl eq_refl
                (ltac:(cbn; discriminate)) Ht2_v H27)
      as [Htmp_v Hframe_27].
    cbn [LFp loc_var loc_type] in Htmp_v, Hframe_27.
    rewrite F.pow_pow_l in Htmp_v.
    change (1606938044258990275541962092341162602522202993782792835301375 * 2)%N
      with 3213876088517980551083924184682325205044405987565585670602750%N in Htmp_v.
    assert (Hax_27 : Fp25519_holds rs27 a_loc.(loc_var) x)
      by (apply Hframe_27; [exact Ha_tmp | exact Hax_26]).
    assert (Hz9_27 : Fp25519_holds rs27 "z9" (F.pow x 9))
      by (apply Hframe_27; [discriminate | exact Hz9_26]).
    assert (Hz11_27 : Fp25519_holds rs27 "z11" (F.pow x 11))
      by (apply Hframe_27; [discriminate | exact Hz11_26]).
    assert (Hz2_50_27 : Fp25519_holds rs27 "z2_50_0" (F.pow x 1125899906842623))
      by (apply Hframe_27; [discriminate | exact Hz2_50_26]).
    clear Hax_26 Hz9_26 Hz11_26 Hz2_50_26 Ht2_v Hframe_27.

    (* --- Step 28: sqrN 49 "tmp" "scratch" => tmp = x^((2^200-1)·2^50) --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs28 [H28 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (sqrN_correct 49 "tmp" "scratch" rs27 rs28
                (F.pow x 3213876088517980551083924184682325205044405987565585670602750)
                (ltac:(discriminate)) Htmp_v H28)
      as [Htmp_v' Hframe_28].
    rewrite F.pow_pow_l in Htmp_v'.
    (* (2(2^200-1)) * 2^49 = (2^201 - 2) * 2^49 = 2^250 - 2^50 *)
    change (3213876088517980551083924184682325205044405987565585670602750 * N.pow 2 (N.of_nat 49))%N
      with 1809251394333065553493296640760748560207343510400633813116523624223735808000%N in Htmp_v'.
    assert (Hax_28 : Fp25519_holds rs28 a_loc.(loc_var) x)
      by (apply Hframe_28; [exact Ha_tmp | exact Ha_scratch | exact Hax_27]).
    assert (Hz9_28 : Fp25519_holds rs28 "z9" (F.pow x 9))
      by (apply Hframe_28; [discriminate | discriminate | exact Hz9_27]).
    assert (Hz11_28 : Fp25519_holds rs28 "z11" (F.pow x 11))
      by (apply Hframe_28; [discriminate | discriminate | exact Hz11_27]).
    assert (Hz2_50_28 : Fp25519_holds rs28 "z2_50_0" (F.pow x 1125899906842623))
      by (apply Hframe_28; [discriminate | discriminate | exact Hz2_50_27]).
    clear Hax_27 Hz9_27 Hz11_27 Hz2_50_27 Htmp_v Hframe_28.

    (* --- Step 29: mul_call "t3" "tmp" "z2_50_0" => t3 = x^(2^250-1) --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs29 [H29 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (mul_correct (LFp "t3") (LFp "tmp") (LFp "z2_50_0") rs28 rs29
                (F.pow x 1809251394333065553493296640760748560207343510400633813116523624223735808000)
                (F.pow x 1125899906842623)
                eq_refl eq_refl eq_refl
                (ltac:(cbn; discriminate)) (ltac:(cbn; discriminate))
                Htmp_v' Hz2_50_28 H29)
      as [Ht3_v Hframe_29].
    cbn [LFp loc_var loc_type] in Ht3_v, Hframe_29.
    (* 2^250 - 2^50 + 2^50 - 1 = 2^250 - 1 *)
    replace (F.mul (F.pow x 1809251394333065553493296640760748560207343510400633813116523624223735808000)
                   (F.pow x 1125899906842623))
      with (F.pow x 1809251394333065553493296640760748560207343510400633813116524750123642650623) in Ht3_v
      by (rewrite <- F.pow_add_r; reflexivity).
    assert (Hax_29 : Fp25519_holds rs29 a_loc.(loc_var) x)
      by (apply Hframe_29; [exact Ha_t3 | exact Hax_28]).
    assert (Hz11_29 : Fp25519_holds rs29 "z11" (F.pow x 11))
      by (apply Hframe_29; [discriminate | exact Hz11_28]).
    clear Hax_28 Hz9_28 Hz11_28 Hz2_50_28 Htmp_v' Hframe_29.

    (* --- Step 30: sqr_call "tmp" "t3" => tmp = x^(2(2^250-1)) --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs30 [H30 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (sqr_correct (LFp "tmp") (LFp "t3") rs29 rs30
                (F.pow x 1809251394333065553493296640760748560207343510400633813116524750123642650623)
                eq_refl eq_refl
                (ltac:(cbn; discriminate)) Ht3_v H30)
      as [Htmp_v Hframe_30].
    cbn [LFp loc_var loc_type] in Htmp_v, Hframe_30.
    rewrite F.pow_pow_l in Htmp_v.
    change (1809251394333065553493296640760748560207343510400633813116524750123642650623 * 2)%N
      with 3618502788666131106986593281521497120414687020801267626233049500247285301246%N in Htmp_v.
    assert (Hax_30 : Fp25519_holds rs30 a_loc.(loc_var) x)
      by (apply Hframe_30; [exact Ha_tmp | exact Hax_29]).
    assert (Hz11_30 : Fp25519_holds rs30 "z11" (F.pow x 11))
      by (apply Hframe_30; [discriminate | exact Hz11_29]).
    clear Hax_29 Hz11_29 Ht3_v Hframe_30.

    (* --- Step 31: sqrN 4 "tmp" "scratch" => tmp = x^((2^250-1)·2^5) --- *)
    cbn [seqN] in Hexec_n.
    destruct (seq_inv _ _ _ _ Hexec_n) as [rs31 [H31 Hexec_n']]; clear Hexec_n.
    rename Hexec_n' into Hexec_n.
    pose proof (sqrN_correct 4 "tmp" "scratch" rs30 rs31
                (F.pow x 3618502788666131106986593281521497120414687020801267626233049500247285301246)
                (ltac:(discriminate)) Htmp_v H31)
      as [Htmp_v' Hframe_31].
    rewrite F.pow_pow_l in Htmp_v'.
    (* (2(2^250-1)) * 2^4 = (2^251 - 2) * 2^4 = 2^255 - 2^5 = 2^255 - 32 *)
    change (3618502788666131106986593281521497120414687020801267626233049500247285301246 * N.pow 2 (N.of_nat 4))%N
      with 57896044618658097711785492504343953926634992332820282019728792003956564819936%N in Htmp_v'.
    assert (Hax_31 : Fp25519_holds rs31 a_loc.(loc_var) x)
      by (apply Hframe_31; [exact Ha_tmp | exact Ha_scratch | exact Hax_30]).
    assert (Hz11_31 : Fp25519_holds rs31 "z11" (F.pow x 11))
      by (apply Hframe_31; [discriminate | discriminate | exact Hz11_30]).
    clear Hax_30 Hz11_30 Htmp_v Hframe_31.

    (* --- Step 32: REdCall fe25519_mul dest [LFp "tmp"; LFp "z11"]
                   => dest = x^(2^255 - 32 + 11) = x^(2^255 - 21) = x^(p-2) --- *)
    cbn [seqN] in Hexec_n.
    (* This is the last command — no more seqN to split. *)
    assert (Hne_d_tmp : dest.(loc_var) <> (LFp "tmp").(loc_var))
      by (cbn; exact Hd_tmp).
    assert (Hne_d_z11 : dest.(loc_var) <> (LFp "z11").(loc_var))
      by (cbn; exact Hd_z11).
    pose proof (mul_correct dest (LFp "tmp") (LFp "z11") rs31 rs2
                (F.pow x 57896044618658097711785492504343953926634992332820282019728792003956564819936)
                (F.pow x 11)
                Hdt eq_refl eq_refl
                Hne_d_tmp Hne_d_z11
                Htmp_v' Hz11_31 Hexec_n)
      as [Hdest_v _].
    (* (2^255 - 32) + 11 = 2^255 - 21 = p - 2 (since p = 2^255 - 19) *)
    replace (F.mul (F.pow x 57896044618658097711785492504343953926634992332820282019728792003956564819936)
                   (F.pow x 11))
      with (F.pow x (Z.to_N (p - 2))) in Hdest_v
      by (rewrite <- F.pow_add_r; reflexivity).
    exact Hdest_v.
  Qed.

End Fe25519InvertCorrect.

(* Sanity check: list assumptions of the headline theorem.  Inside the
   Section, these are the [Variable]/[Hypothesis] parameters (which
   become axioms in the kernel's eyes when the Section closes — but
   they appear as parameters of the abstracted definition, not as
   global axioms). *)
Print Assumptions fe25519_invert_correct.
Print Assumptions sqrN_correct.
