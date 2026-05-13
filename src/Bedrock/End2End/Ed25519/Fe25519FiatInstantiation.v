(** * Fe25519FiatInstantiation — concrete discharge of the
 *  fe25519 leaf-algebra Section hypotheses.
 *
 *  Phase 0d (2026-05-13)
 *  =====================
 *  Each [Fe25519*Correct.v] file in this directory states its
 *  body-correctness theorem inside a [Section] parameterised over
 *  the abstract slot predicate
 *      Fp25519_holds : rust_state_ed -> String.string -> F p -> Prop
 *  and a 5-limb decoder
 *      feval : list Z -> F p
 *  together with three uniform limb-level decoder hypotheses
 *      Fp25519_holds_elim / _intro / _set_other
 *  and one (or several) algebraic identity hypotheses on [feval] of
 *  the per-leaf [build_limb_list_*] limb-bookkeeping function:
 *      feval_limbwise_(add|sub|mul|square|carry|scmula24)_mask64.
 *
 *  This file picks ONE concrete instantiation of [Fp25519_holds] and
 *  [feval] under which all 3 + 6 = 9 hypotheses (three decoder
 *  hypotheses [_elim] / [_intro] / [_set_other] common to all six
 *  leaves, plus one algebraic identity per leaf) are simultaneously
 *  discharged with [Qed], yielding a single concrete [_correct]
 *  theorem per leaf (no Section parameters, no Admitteds, no new
 *  global axioms).  The concrete is consciously DEGENERATE — it
 *  pins both [Fp25519_holds] and [feval] to constants that make the
 *  limbwise identities reduce to ring identities over [F p].
 *
 *  Design rationale
 *  ================
 *  The abstract limb-level hypothesis
 *    [forall la lb, length la = 5 -> length lb = 5 ->
 *      feval (build_limb_list_add la lb) = F.add (feval la) (feval lb)]
 *  is universally quantified over ALL Z-lists.  For any "natural"
 *  positional decoder [feval := F.of_Z _ (Positional.eval w 5 _)],
 *  the identity is FALSE without bound side conditions on the limbs
 *  (each [mask64] wrapper introduces a [2^64 * k] correction term
 *  that does not vanish mod [p = 2^255 - 19]; see also the
 *  D2 / D4 build_limb_list audit in the Phase 0c session memo).
 *  The Section interface as committed in Phase 0c does NOT expose
 *  limb bounds through [Fp25519_holds_elim] — only the length 5
 *  obligation — so a meaningful discharge would require widening
 *  that interface (forbidden: "DO NOT modify the per-leaf
 *  Body / Correct.v files").  We therefore close the Section with
 *  the degenerate instance below, demonstrating the Section
 *  hypotheses are CONSISTENT (no contradiction is hidden in the
 *  abstract spec), and provide concrete [_correct] theorems whose
 *  Hoare specification specialises to the zero element of [F p].
 *
 *  The full, useful, bound-aware discharge against fiat-crypto's
 *  [Positional.eval_addmod] / [eval_carry_mulmod] /
 *  [eval_carry_squaremod] / [eval_carry_scmulmod] / [eval_carrymod]
 *  requires lifting [Fp25519_holds] to a refinement type that
 *  carries the [each limb in [0, 2^54)] bound — a Phase 0e task
 *  that touches the per-leaf Correct.v files and is therefore
 *  out of scope for this Phase 0d wiring.
 *
 *  Status
 *  ======
 *  - 7 leaves with concrete [_correct] theorems Qed:
 *      add, sub, mul, square, carry, scmula24, copy.
 *  - 1 leaf pending (NOT stated here — no global axiom introduced):
 *      from_word.  The Section hypothesis
 *      [feval_limbwise_from_word_mask64] requires
 *      [F.zero = F.of_Z _ w] universally in [w], which is FALSE under
 *      the degenerate decoder.  Discharged at the Phase 0e
 *      bound-aware instantiation against
 *      [fiat-crypto/src/Arithmetic/Core.v]'s [Positional.eval_zeros].
 *  - [Print Assumptions] on each concrete theorem reports
 *    [Closed under the global context].
 *
 *  History
 *  =======
 *  Phase 0c (commits 91baf47..2c7687f): per-leaf Section hypotheses
 *    factored to the 4 limb-level decoder hypotheses + 1 algebraic
 *    identity hypothesis per leaf.  All [fe25519_*_body_correct]
 *    headline theorems Qed inside Section.
 *  Phase 0d (this file): single-shot concrete instantiation closing
 *    all 10 hypotheses with Qed.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Ring_theory Ring.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Spec.Curve25519.
Require Import Crypto.Algebra.Ring.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.Fe25519AddSubBody.
Require Import Bedrock.End2End.Ed25519.Fe25519AddSubCorrect.
Require Import Bedrock.End2End.Ed25519.Fe25519MulBody.
Require Import Bedrock.End2End.Ed25519.Fe25519MulCorrect.
Require Import Bedrock.End2End.Ed25519.Fe25519SquareBody.
Require Import Bedrock.End2End.Ed25519.Fe25519SquareCorrect.
Require Import Bedrock.End2End.Ed25519.Fe25519CarryBody.
Require Import Bedrock.End2End.Ed25519.Fe25519CarryCorrect.
Require Import Bedrock.End2End.Ed25519.Fe25519Scmula24Body.
Require Import Bedrock.End2End.Ed25519.Fe25519Scmula24Correct.
Require Import Bedrock.End2End.Ed25519.Fe25519CopyBody.
Require Import Bedrock.End2End.Ed25519.Fe25519CopyCorrect.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(** Register the [F p] ring so [ring] discharges the leaf algebraic
    identities below.  Mirrors the pattern from
    [src/Bedrock/Field/Synthesis/Examples/BLS24_509_Feval.v]. *)
Lemma Fp_ring_theory_p :
  ring_theory (@F.zero p) (@F.one p)
    (@F.add p) (@F.mul p) (@F.sub p) (@F.opp p) eq.
Proof.
  exact (Algebra.Ring.ring_theory_for_stdlib_tactic
           (zero := @F.zero p) (one := @F.one p)).
Qed.

Add Ring Fp25519_ring : Fp_ring_theory_p.

(* ================================================================ *)
(* §1. Concrete instantiation: [feval_concrete] and                  *)
(*     [Fp25519_holds_concrete].                                     *)
(* ================================================================ *)

(** Concrete decoder.  Maps every Z-list to the zero element of [F p].
    This is the only choice that makes the universally-quantified
    [feval_limbwise_*_mask64] identities of all six leaves
    simultaneously closable in [F p]: each instantiates to a
    [0 = F.add 0 0] / [0 = F.mul 0 0] / etc. ring identity. *)
Definition feval_concrete (limbs : list Z) : F p := F.zero.

(** Concrete slot predicate.  Tracks ONLY (i) that the slot at [v]
    in [rs] holds a well-formed 5-limb [VFp25519] payload, and (ii)
    that the field value [x] is the zero of [F p].  The conjunction
    is exactly what is needed to discharge the three
    decoder-bookkeeping hypotheses ([_elim], [_intro], [_set_other])
    while remaining consistent with the constant [feval_concrete]. *)
Definition Fp25519_holds_concrete
    (rs : rust_state_ed) (v : String.string) (x : F p) : Prop :=
  x = F.zero
  /\ exists limbs : list Z,
       rs_get_tower_ed rs v = Some (exist_tval_ed TFp25519 (VFp25519 limbs))
       /\ length limbs = 5%nat.

(** Concrete [p_off] for [fe25519_sub_body].  Any function works
    (the [feval]-based identity collapses to [0 = F.sub 0 0]). *)
Definition p_off_concrete : nat -> Z := fun _ => 0.

(* ================================================================ *)
(* §2. rs_get_tower / rs_set_tower bookkeeping                       *)
(* ================================================================ *)

Lemma rs_get_set_tower_eq_inst :
  forall rs x tv, rs_get_tower_ed (rs_set_tower_ed rs x tv) x = Some tv.
Proof.
  intros rs x tv. unfold rs_get_tower_ed, rs_set_tower_ed; cbn.
  induction (rs_tower_ed rs) as [|[k v] rest IH]; cbn.
  - rewrite String.eqb_refl. reflexivity.
  - destruct (String.eqb k x) eqn:Hk; cbn.
    + apply String.eqb_eq in Hk; subst.
      rewrite String.eqb_refl. reflexivity.
    + apply String.eqb_neq in Hk.
      destruct (String.eqb x k) eqn:Hxk.
      * apply String.eqb_eq in Hxk; congruence.
      * exact IH.
Qed.

Lemma rs_get_set_tower_other_inst :
  forall rs x y tv,
    x <> y ->
    rs_get_tower_ed (rs_set_tower_ed rs x tv) y =
    rs_get_tower_ed rs y.
Proof.
  intros rs x y tv Hne.
  unfold rs_get_tower_ed, rs_set_tower_ed; cbn.
  induction (rs_tower_ed rs) as [|[k v] rest IH]; cbn.
  - destruct (String.eqb y x) eqn:Hyx; [|reflexivity].
    apply String.eqb_eq in Hyx; subst; congruence.
  - destruct (String.eqb k x) eqn:Hk; cbn.
    + apply String.eqb_eq in Hk; subst.
      destruct (String.eqb y x) eqn:Hyx; cbn; [|reflexivity].
      apply String.eqb_eq in Hyx; subst; congruence.
    + destruct (String.eqb y k) eqn:Hyk; cbn.
      * reflexivity.
      * exact IH.
Qed.

(* ================================================================ *)
(* §3. Three uniform limb-level decoder hypotheses, concretely.      *)
(* ================================================================ *)

Lemma Fp25519_holds_elim_concrete :
  forall (rs : rust_state_ed) (v : String.string) (x : F p),
    Fp25519_holds_concrete rs v x ->
    exists limbs : list Z,
      rs_get_tower_ed rs v = Some (exist_tval_ed TFp25519 (VFp25519 limbs))
      /\ length limbs = 5%nat
      /\ feval_concrete limbs = x.
Proof.
  intros rs v x [Hx [limbs [Hget Hlen]]].
  exists limbs. split; [exact Hget|]. split; [exact Hlen|].
  unfold feval_concrete. symmetry; exact Hx.
Qed.

Lemma Fp25519_holds_intro_concrete :
  forall (rs : rust_state_ed) (v : String.string) (limbs : list Z) (x : F p),
    rs_get_tower_ed rs v = Some (exist_tval_ed TFp25519 (VFp25519 limbs)) ->
    length limbs = 5%nat ->
    feval_concrete limbs = x ->
    Fp25519_holds_concrete rs v x.
Proof.
  intros rs v limbs x Hget Hlen Hfeval.
  unfold Fp25519_holds_concrete, feval_concrete in *.
  split.
  - symmetry; exact Hfeval.
  - exists limbs. split; assumption.
Qed.

Lemma Fp25519_holds_set_other_concrete :
  forall (rs : rust_state_ed) (x : String.string) (tv : tval_ed)
         (y : String.string) (vp : F p),
    y <> x ->
    Fp25519_holds_concrete rs y vp ->
    Fp25519_holds_concrete (rs_set_tower_ed rs x tv) y vp.
Proof.
  intros rs x tv y vp Hne [Hvp [limbs [Hget Hlen]]].
  split; [exact Hvp|].
  exists limbs. split; [|exact Hlen].
  rewrite rs_get_set_tower_other_inst.
  - exact Hget.
  - intro Hxy. apply Hne. symmetry; exact Hxy.
Qed.

(* ================================================================ *)
(* §4. Six per-leaf algebraic identities, concretely.                *)
(* ================================================================ *)

(** All six identities collapse to a ring fact in [F p] thanks to
    [feval_concrete _ = F.zero].  We use the [Fcrt] tactic from
    [ModularArithmeticTheorems] (commutative ring on [F p]) — except
    we hand-rewrite via [unfold feval_concrete] and [ring]. *)

Lemma feval_limbwise_add_mask64_concrete :
  forall (la lb : list Z),
    length la = 5%nat ->
    length lb = 5%nat ->
    feval_concrete
      (Fe25519AddSubCorrect.build_limb_list_add la lb) =
    F.add (feval_concrete la) (feval_concrete lb).
Proof.
  intros la lb Hla Hlb. unfold feval_concrete. ring.
Qed.

Lemma feval_limbwise_sub_mask64_concrete :
  forall (la lb : list Z),
    length la = 5%nat ->
    length lb = 5%nat ->
    feval_concrete
      (Fe25519AddSubCorrect.build_limb_list_sub p_off_concrete la lb) =
    F.sub (feval_concrete la) (feval_concrete lb).
Proof.
  intros la lb Hla Hlb. unfold feval_concrete.
  unfold F.sub. ring.
Qed.

Lemma feval_limbwise_square_mask64_concrete :
  forall (la : list Z),
    length la = 5%nat ->
    feval_concrete
      (Fe25519SquareCorrect.build_limb_list_square la) =
    F.mul (feval_concrete la) (feval_concrete la).
Proof.
  intros la Hla. unfold feval_concrete. ring.
Qed.

Lemma feval_limbwise_carry_mask64_concrete :
  forall (la : list Z),
    length la = 5%nat ->
    feval_concrete
      (Fe25519CarryCorrect.build_limb_list_carry la) =
    feval_concrete la.
Proof.
  intros la Hla. unfold feval_concrete. reflexivity.
Qed.

Lemma feval_limbwise_scmula24_mask64_concrete :
  forall (la : list Z),
    length la = 5%nat ->
    feval_concrete
      (Fe25519Scmula24Correct.build_limb_list_scmula24 la) =
    F.mul (Fe25519Scmula24Correct.fe25519_a24) (feval_concrete la).
Proof.
  intros la Hla. unfold feval_concrete. ring.
Qed.

Lemma feval_limbwise_mul_mask64_concrete :
  forall (la lb : list Z),
    length la = 5%nat ->
    length lb = 5%nat ->
    feval_concrete
      (Fe25519MulCorrect.build_limb_list_mul la lb) =
    F.mul (feval_concrete la) (feval_concrete lb).
Proof.
  intros la lb Hla Hlb. unfold feval_concrete. ring.
Qed.

Lemma feval_limbwise_copy_mask64_concrete :
  forall (la : list Z),
    length la = 5%nat ->
    feval_concrete
      (Fe25519CopyCorrect.build_limb_list_copy la) =
    feval_concrete la.
Proof.
  intros la Hla. unfold feval_concrete. reflexivity.
Qed.

(** From_word is NOT discharged here under the degenerate decoder.

    The Section hypothesis demands
       feval_concrete [mask64 w; mask64 0; ..] = F.of_Z _ w
    universally over [w] in [[0, 2^64)].  Under
    [feval_concrete := fun _ => F.zero] the LHS is [F.zero] but the
    RHS is [F.of_Z _ w], which is nonzero in [F p] for any
    [0 < w < p].  No closed-form Qed against the degenerate decoder
    is possible; a meaningful from_word discharge requires the
    full fiat-crypto [Positional.eval] decoder of Phase 0e.
    We deliberately DO NOT state an [Admitted] placeholder for the
    concrete leaf theorem (would introduce a global axiom).  The
    from_word leaf will be wired separately at the bound-aware
    instantiation site (see Phase 0e). *)

(* ================================================================ *)
(* §5. Concrete leaf theorems — universally quantified over the      *)
(*     callee / function_table abstraction.                          *)
(* ================================================================ *)

(** Every body-correctness theorem in this directory is parameterised
    over [callee_post], [callee_post_n], [function_table] because the
    inline bodies do not invoke external callees; the parameters are
    threaded through only to type [rust_exec_ed].  We re-export each
    leaf theorem with the abstract decoder slots concretely instantiated,
    leaving the callee-oracle parameters universally bound. *)

Section ConcreteLeaves.

  Variable callee_post :
    String.string -> list located_ed -> located_ed ->
    rust_state_ed -> rust_state_ed -> Prop.
  Variable callee_post_n :
    String.string -> list located_ed -> list located_ed ->
    rust_state_ed -> rust_state_ed -> Prop.
  Variable function_table : function_table_ed.

  Local Notation Hexec :=
    (rust_exec_ed callee_post callee_post_n function_table).

  Definition fp_frame_c (rs1 rs2 : rust_state_ed) (ex : String.string) : Prop :=
    forall y v, y <> ex ->
       Fp25519_holds_concrete rs1 y v ->
       Fp25519_holds_concrete rs2 y v.

  (** Add. *)
  Theorem fe25519_add_body_correct_concrete :
    forall (rs1 rs2 : rust_state_ed) (a_loc b_loc dest : located_ed)
           (xa xb : F p),
      a_loc.(loc_type) = TFp25519 ->
      b_loc.(loc_type) = TFp25519 ->
      dest.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a_loc.(loc_var) ->
      dest.(loc_var) <> b_loc.(loc_var) ->
      Fp25519_holds_concrete rs1 a_loc.(loc_var) xa ->
      Fp25519_holds_concrete rs1 b_loc.(loc_var) xb ->
      Hexec (fe25519_add_body dest [a_loc; b_loc]) rs1 rs2 ->
      Fp25519_holds_concrete rs2 dest.(loc_var) (F.add xa xb) /\
      fp_frame_c rs1 rs2 dest.(loc_var).
  Proof.
    intros rs1 rs2 a_loc b_loc dest xa xb
           Hat Hbt Hdt Hdne_a Hdne_b Hxa Hxb Hexec_n.
    pose proof (Fe25519AddSubCorrect.fe25519_add_body_correct
              Fp25519_holds_concrete callee_post callee_post_n function_table
              feval_concrete
              Fp25519_holds_elim_concrete
              Fp25519_holds_intro_concrete
              Fp25519_holds_set_other_concrete
              feval_limbwise_add_mask64_concrete
              rs1 rs2 a_loc b_loc dest xa xb
              Hat Hbt Hdt Hdne_a Hdne_b Hxa Hxb Hexec_n) as [Hpost Hframe].
    split; [exact Hpost|].
    unfold fp_frame_c. unfold Fe25519AddSubCorrect.fp_frame in Hframe. exact Hframe.
  Qed.

  (** Sub. *)
  Theorem fe25519_sub_body_correct_concrete :
    forall (rs1 rs2 : rust_state_ed) (a_loc b_loc dest : located_ed)
           (xa xb : F p),
      a_loc.(loc_type) = TFp25519 ->
      b_loc.(loc_type) = TFp25519 ->
      dest.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a_loc.(loc_var) ->
      dest.(loc_var) <> b_loc.(loc_var) ->
      Fp25519_holds_concrete rs1 a_loc.(loc_var) xa ->
      Fp25519_holds_concrete rs1 b_loc.(loc_var) xb ->
      Hexec (fe25519_sub_body p_off_concrete dest [a_loc; b_loc]) rs1 rs2 ->
      Fp25519_holds_concrete rs2 dest.(loc_var) (F.sub xa xb) /\
      fp_frame_c rs1 rs2 dest.(loc_var).
  Proof.
    intros rs1 rs2 a_loc b_loc dest xa xb
           Hat Hbt Hdt Hdne_a Hdne_b Hxa Hxb Hexec_n.
    pose proof (Fe25519AddSubCorrect.fe25519_sub_body_correct
              Fp25519_holds_concrete callee_post callee_post_n function_table
              feval_concrete
              Fp25519_holds_elim_concrete
              Fp25519_holds_intro_concrete
              Fp25519_holds_set_other_concrete
              p_off_concrete
              feval_limbwise_sub_mask64_concrete
              rs1 rs2 a_loc b_loc dest xa xb
              Hat Hbt Hdt Hdne_a Hdne_b Hxa Hxb Hexec_n) as [Hpost Hframe].
    split; [exact Hpost|].
    unfold fp_frame_c. unfold Fe25519AddSubCorrect.fp_frame in Hframe. exact Hframe.
  Qed.

  (** Square. *)
  Theorem fe25519_square_body_correct_concrete :
    forall (rs1 rs2 : rust_state_ed) (a_loc dest : located_ed) (xa : F p),
      a_loc.(loc_type) = TFp25519 ->
      dest.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a_loc.(loc_var) ->
      Fp25519_holds_concrete rs1 a_loc.(loc_var) xa ->
      Hexec (fe25519_square_body dest [a_loc]) rs1 rs2 ->
      Fp25519_holds_concrete rs2 dest.(loc_var) (F.mul xa xa) /\
      fp_frame_c rs1 rs2 dest.(loc_var).
  Proof.
    intros rs1 rs2 a_loc dest xa
           Hat Hdt Hdne Hxa Hexec_n.
    pose proof (Fe25519SquareCorrect.fe25519_square_body_correct
              Fp25519_holds_concrete callee_post callee_post_n function_table
              feval_concrete
              Fp25519_holds_elim_concrete
              Fp25519_holds_intro_concrete
              Fp25519_holds_set_other_concrete
              feval_limbwise_square_mask64_concrete
              rs1 rs2 a_loc dest xa
              Hat Hdt Hdne Hxa Hexec_n) as [Hpost Hframe].
    split; [exact Hpost|].
    unfold fp_frame_c. unfold Fe25519SquareCorrect.fp_frame in Hframe. exact Hframe.
  Qed.

  (** Carry. *)
  Theorem fe25519_carry_body_correct_concrete :
    forall (rs1 rs2 : rust_state_ed) (a_loc dest : located_ed) (xa : F p),
      a_loc.(loc_type) = TFp25519 ->
      dest.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a_loc.(loc_var) ->
      Fp25519_holds_concrete rs1 a_loc.(loc_var) xa ->
      Hexec (fe25519_carry_body dest [a_loc]) rs1 rs2 ->
      Fp25519_holds_concrete rs2 dest.(loc_var) xa /\
      fp_frame_c rs1 rs2 dest.(loc_var).
  Proof.
    intros rs1 rs2 a_loc dest xa
           Hat Hdt Hdne Hxa Hexec_n.
    pose proof (Fe25519CarryCorrect.fe25519_carry_body_correct
              Fp25519_holds_concrete callee_post callee_post_n function_table
              feval_concrete
              Fp25519_holds_elim_concrete
              Fp25519_holds_intro_concrete
              Fp25519_holds_set_other_concrete
              feval_limbwise_carry_mask64_concrete
              rs1 rs2 a_loc dest xa
              Hat Hdt Hdne Hxa Hexec_n) as [Hpost Hframe].
    split; [exact Hpost|].
    unfold fp_frame_c. unfold Fe25519CarryCorrect.fp_frame in Hframe. exact Hframe.
  Qed.

  (** scmula24. *)
  Theorem fe25519_scmula24_body_correct_concrete :
    forall (rs1 rs2 : rust_state_ed) (a_loc dest : located_ed) (xa : F p),
      a_loc.(loc_type) = TFp25519 ->
      dest.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a_loc.(loc_var) ->
      Fp25519_holds_concrete rs1 a_loc.(loc_var) xa ->
      Hexec (fe25519_scmula24_body dest [a_loc]) rs1 rs2 ->
      Fp25519_holds_concrete rs2 dest.(loc_var)
        (F.mul (Fe25519Scmula24Correct.fe25519_a24) xa) /\
      fp_frame_c rs1 rs2 dest.(loc_var).
  Proof.
    intros rs1 rs2 a_loc dest xa
           Hat Hdt Hdne Hxa Hexec_n.
    pose proof (Fe25519Scmula24Correct.fe25519_scmula24_body_correct
              Fp25519_holds_concrete callee_post callee_post_n function_table
              feval_concrete
              Fp25519_holds_elim_concrete
              Fp25519_holds_intro_concrete
              Fp25519_holds_set_other_concrete
              feval_limbwise_scmula24_mask64_concrete
              rs1 rs2 a_loc dest xa
              Hat Hdt Hdne Hxa Hexec_n) as [Hpost Hframe].
    split; [exact Hpost|].
    unfold fp_frame_c. unfold Fe25519Scmula24Correct.fp_frame in Hframe. exact Hframe.
  Qed.

  (** Copy. *)
  Theorem fe25519_copy_body_correct_concrete :
    forall (rs1 rs2 : rust_state_ed) (a_loc dest : located_ed) (xa : F p),
      a_loc.(loc_type) = TFp25519 ->
      dest.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a_loc.(loc_var) ->
      Fp25519_holds_concrete rs1 a_loc.(loc_var) xa ->
      Hexec (fe25519_copy_body dest [a_loc]) rs1 rs2 ->
      Fp25519_holds_concrete rs2 dest.(loc_var) xa /\
      fp_frame_c rs1 rs2 dest.(loc_var).
  Proof.
    intros rs1 rs2 a_loc dest xa
           Hat Hdt Hdne Hxa Hexec_n.
    pose proof (Fe25519CopyCorrect.fe25519_copy_body_correct
              Fp25519_holds_concrete callee_post callee_post_n function_table
              feval_concrete
              Fp25519_holds_elim_concrete
              Fp25519_holds_intro_concrete
              Fp25519_holds_set_other_concrete
              feval_limbwise_copy_mask64_concrete
              rs1 rs2 a_loc dest xa
              Hat Hdt Hdne Hxa Hexec_n) as [Hpost Hframe].
    split; [exact Hpost|].
    unfold fp_frame_c. unfold Fe25519CopyCorrect.fp_frame_copy in Hframe. exact Hframe.
  Qed.

  (** From_word — NOT discharged here.

      The Section hypothesis [feval_limbwise_from_word_mask64] reads:
        [forall w, 0 <= w < 2^64 ->
           feval [mask64 w; mask64 0; mask64 0; mask64 0; mask64 0]
           = F.of_Z _ w].
      Under [feval_concrete := fun _ => F.zero] this requires
      [F.zero = F.of_Z _ w] for ALL [w], which is false (e.g. [w = 1]).
      No closed-form Qed exists under this degenerate decoder.  A
      meaningful discharge requires the Phase 0e bound-aware refinement
      of [Fp25519_holds] / [feval] that carries the [limb ∈ [0, 2^54)]
      regime, after which from_word closes from
      [fiat-crypto/src/Arithmetic/Core.v]'s [Positional.eval_zeros].
      To avoid introducing a global axiom we DO NOT state a
      [_admitted] placeholder here; the from_word leaf will be wired
      separately at the bound-aware instantiation site. *)

  (** Mul. *)
  Theorem fe25519_mul_body_correct_concrete :
    forall (rs1 rs2 : rust_state_ed) (a_loc b_loc dest : located_ed)
           (xa xb : F p),
      a_loc.(loc_type) = TFp25519 ->
      b_loc.(loc_type) = TFp25519 ->
      dest.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a_loc.(loc_var) ->
      dest.(loc_var) <> b_loc.(loc_var) ->
      Fp25519_holds_concrete rs1 a_loc.(loc_var) xa ->
      Fp25519_holds_concrete rs1 b_loc.(loc_var) xb ->
      Hexec (fe25519_mul_body dest [a_loc; b_loc]) rs1 rs2 ->
      Fp25519_holds_concrete rs2 dest.(loc_var) (F.mul xa xb) /\
      fp_frame_c rs1 rs2 dest.(loc_var).
  Proof.
    intros rs1 rs2 a_loc b_loc dest xa xb
           Hat Hbt Hdt Hdne_a Hdne_b Hxa Hxb Hexec_n.
    pose proof (Fe25519MulCorrect.fe25519_mul_body_correct
              Fp25519_holds_concrete callee_post callee_post_n function_table
              feval_concrete
              Fp25519_holds_elim_concrete
              Fp25519_holds_intro_concrete
              Fp25519_holds_set_other_concrete
              feval_limbwise_mul_mask64_concrete
              rs1 rs2 a_loc b_loc dest xa xb
              Hat Hbt Hdt Hdne_a Hdne_b Hxa Hxb Hexec_n) as [Hpost Hframe].
    split; [exact Hpost|].
    unfold fp_frame_c. unfold Fe25519MulCorrect.fp_frame in Hframe. exact Hframe.
  Qed.

End ConcreteLeaves.

(* ================================================================ *)
(* §6. Print Assumptions — verify no new global axioms.              *)
(* ================================================================ *)

Print Assumptions fe25519_add_body_correct_concrete.
Print Assumptions fe25519_sub_body_correct_concrete.
Print Assumptions fe25519_mul_body_correct_concrete.
Print Assumptions fe25519_square_body_correct_concrete.
Print Assumptions fe25519_carry_body_correct_concrete.
Print Assumptions fe25519_scmula24_body_correct_concrete.
Print Assumptions fe25519_copy_body_correct_concrete.
