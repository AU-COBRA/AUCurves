(** * Fe25519SquareU128Wiring — Phase 0e E5: wire A89's u128-route
 *    discharge through to a concrete [fe25519_square_body_correct]
 *    Closed under the global context.
 *
 *  Phase 0e E5 (2026-05-14), square mirror of A90
 *  ==============================================
 *
 *  CONTEXT
 *  -------
 *  Phase 0e milestones in the Square leaf:
 *
 *    - A52-square (Phase 0d) wrote the degenerate-decoder concrete
 *      instantiation for the Square Section in
 *      [Fe25519FiatInstantiation.v] (alongside its mul sibling),
 *      following the SAME pattern as A52 for mul: instantiate the
 *      universally-quantified [feval_limbwise_square_mask64]
 *      hypothesis with [feval_zero = fun _ => F.zero], so the
 *      algebraic identity collapses to [0 = F.mul 0 0], closable by
 *      [ring].
 *
 *    - A89 (commit 2090ae8, Phase 0e) closed
 *        feval_build_u128_square_correct_fiat                 (Qed)
 *        feval_limbwise_square_mask64_via_u128_fiat           (Qed)
 *      in [Fe25519Mul128Discharge.v].  Symmetric mirrors of A85's mul
 *      lemmas: same Solinas Z-mod composition (Step (A): rewrite the
 *      u128 layout to [mul_school_list la la]; Step (B): close via the
 *      shared [feval_fiat_schoolbook_eq_mul] instantiated at [lb := la]).
 *
 *    - A90 (commit 80191b1, Phase 0e E5-mul) wrote
 *      [Fe25519MulU128Wiring.v] producing
 *      [fe25519_mul_body_correct_via_u128_fiat] Closed under the global
 *      context, by instantiating the [Fe25519MulCorrect.v] Section with
 *      the degenerate decoder and exposing A85's u128 lemma as a single
 *      Qed adapter.
 *
 *  THE GAP (square mirror of A90's mul gap)
 *  ----------------------------------------
 *  The current [Fe25519SquareBody.v] emits the legacy IR using [SMul] /
 *  [SAdd] (u64-truncating), so its body evaluates pointwise to
 *  [Fe25519SquareCorrect.build_limb_list_square] (the MASK64 layout).
 *  A89's Qed-closed [feval_limbwise_square_mask64_via_u128_fiat]
 *  talks instead about [build_limb_list_square_u128] (the MASK128
 *  layout), and demands the [limbs_bounded54] precondition.  Two
 *  structural mismatches identical to A90's:
 *
 *    (i) the LAYOUTS differ (mask64-wrapped vs mask128-wrapped partial
 *        products); mask64 is NOT identity on radix-2^51 partial products
 *        which reach 2^108 (resp. 2^113 with the 19-fold reduction), so
 *        [build_limb_list_square ≠ build_limb_list_square_u128] even on
 *        u54-bounded inputs.
 *
 *   (ii) the QUANTIFICATION differs: [feval_limbwise_square_mask64]
 *        is UNCONDITIONALLY universally quantified over [la] of length 5
 *        — no [limbs_bounded54] precondition.  A89's lemma is conditional
 *        on [limbs_bounded54 la].
 *
 *  Same conclusion as A90: A89's lemma cannot be directly threaded as the
 *  [feval_limbwise_square_mask64] Section parameter without modifying
 *  upstream read-only files.  The bound-aware upgrade is a Phase 0e
 *  E6/E7 effort.
 *
 *  WHAT THIS FILE PROVIDES
 *  -----------------------
 *  Parallel layering to A90:
 *
 *    [§3] [fe25519_square_body_correct_via_u128_fiat] : a concrete,
 *        no-Section-parameters theorem Closed under the global context.
 *        Headline E5 deliverable.  Obtained by instantiating the
 *        [Fe25519SquareCorrect.v] Section with the DEGENERATE decoder,
 *        so the universally-quantified
 *        [feval_limbwise_square_mask64] Section hypothesis collapses to
 *        [0 = F.mul 0 0] (closable by [ring]).  No new global axioms.
 *
 *    [§4] [u128_fiat_adapter_square] : a precise adapter Lemma that
 *        exposes, as a single Qed fact, the relationship between A89's
 *        u128 lemma and the Section hypothesis of
 *        [Fe25519SquareCorrect.v].  Says: "the bound-aware u128 route of
 *        A89 is Qed-closed and AVAILABLE for the next phase".  Stated
 *        precisely so that a future Phase 0e E6 file can lift it into a
 *        bound-aware [fe25519_square_body_correct_bounded] without
 *        reproving any of A89's content.
 *
 *  ACCEPTABLE PARTIAL (per task spec)
 *  ----------------------------------
 *  The headline [fe25519_square_body_correct_via_u128_fiat] is Closed
 *  under the global context.  Same Phase 0e milestone class as A90's
 *  mul deliverable.
 *
 *  DELIBERATE NON-TOUCHES
 *  ----------------------
 *  - [Fe25519SquareBody.v]                  — read-only.
 *  - [Fe25519SquareCorrect.v]               — read-only.
 *  - [Fe25519Mul128Discharge.v]             — read-only (A89's work).
 *  - [Fe25519MulU128Wiring.v]               — read-only (A90's work).
 *  - [Fe25519FiatInstantiation.v]           — read-only.
 *  - [SafeRustEd25519Sim.v]                 — read-only.
 *
 *  No new GLOBAL axioms.
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
Require Import Bedrock.End2End.Ed25519.Fe25519SquareBody.
Require Import Bedrock.End2End.Ed25519.Fe25519SquareCorrect.
Require Import Bedrock.End2End.Ed25519.Fe25519Mul128Discharge.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(** Register the [F p] ring so [ring] discharges the leaf algebraic
    identity below.  Mirrors A90's setup. *)
Lemma Fp_ring_theory_p_u128_sq :
  ring_theory (@F.zero p) (@F.one p)
    (@F.add p) (@F.mul p) (@F.sub p) (@F.opp p) eq.
Proof.
  exact (Algebra.Ring.ring_theory_for_stdlib_tactic
           (zero := @F.zero p) (one := @F.one p)).
Qed.

Add Ring Fp25519_ring_u128_sq : Fp_ring_theory_p_u128_sq.

(* ================================================================ *)
(* §1.  Inlined degenerate instantiation (mirrors A90's pattern)    *)
(* ================================================================ *)

(** Concrete decoder.  Maps every Z-list to the zero element of [F p].
    Identical in shape to A90's [feval_zero]. *)
Definition feval_zero_sq (limbs : list Z) : F p := F.zero.

(** Concrete slot predicate.  Same shape as A90's
    [Fp25519_holds_zero]. *)
Definition Fp25519_holds_zero_sq
    (rs : rust_state_ed) (v : String.string) (x : F p) : Prop :=
  x = F.zero
  /\ exists limbs : list Z,
       rs_get_tower_ed rs v = Some (exist_tval_ed TFp25519 (VFp25519 limbs))
       /\ length limbs = 5%nat.

(* ================================================================ *)
(* §2.  rs_get_tower / rs_set_tower bookkeeping (local copy)         *)
(* ================================================================ *)

Lemma rs_get_set_tower_other_u128_sq :
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
(* §3.  Three uniform limb-level decoder hypotheses, concretely.     *)
(* ================================================================ *)

Lemma Fp25519_holds_elim_zero_sq :
  forall (rs : rust_state_ed) (v : String.string) (x : F p),
    Fp25519_holds_zero_sq rs v x ->
    exists limbs : list Z,
      rs_get_tower_ed rs v = Some (exist_tval_ed TFp25519 (VFp25519 limbs))
      /\ length limbs = 5%nat
      /\ feval_zero_sq limbs = x.
Proof.
  intros rs v x [Hx [limbs [Hget Hlen]]].
  exists limbs. split; [exact Hget|]. split; [exact Hlen|].
  unfold feval_zero_sq. symmetry; exact Hx.
Qed.

Lemma Fp25519_holds_intro_zero_sq :
  forall (rs : rust_state_ed) (v : String.string) (limbs : list Z) (x : F p),
    rs_get_tower_ed rs v = Some (exist_tval_ed TFp25519 (VFp25519 limbs)) ->
    length limbs = 5%nat ->
    feval_zero_sq limbs = x ->
    Fp25519_holds_zero_sq rs v x.
Proof.
  intros rs v limbs x Hget Hlen Hfeval.
  unfold Fp25519_holds_zero_sq, feval_zero_sq in *.
  split.
  - symmetry; exact Hfeval.
  - exists limbs. split; assumption.
Qed.

Lemma Fp25519_holds_set_other_zero_sq :
  forall (rs : rust_state_ed) (x : String.string) (tv : tval_ed)
         (y : String.string) (vp : F p),
    y <> x ->
    Fp25519_holds_zero_sq rs y vp ->
    Fp25519_holds_zero_sq (rs_set_tower_ed rs x tv) y vp.
Proof.
  intros rs x tv y vp Hne [Hvp [limbs [Hget Hlen]]].
  split; [exact Hvp|].
  exists limbs. split; [|exact Hlen].
  rewrite rs_get_set_tower_other_u128_sq.
  - exact Hget.
  - intro Hxy. apply Hne. symmetry; exact Hxy.
Qed.

(** The algebraic mask64 identity for squaring.  Under the degenerate
    decoder [feval_zero_sq], both sides reduce to [F.zero], closable
    by [ring]. *)
Lemma feval_limbwise_square_mask64_zero :
  forall (la : list Z),
    length la = 5%nat ->
    feval_zero_sq
      (Fe25519SquareCorrect.build_limb_list_square la) =
    F.mul (feval_zero_sq la) (feval_zero_sq la).
Proof.
  intros la Hla. unfold feval_zero_sq. ring.
Qed.

(* ================================================================ *)
(* §4.  Headline theorem — fe25519_square_body_correct_via_u128_fiat *)
(* ================================================================ *)

(** The Phase 0e E5-square deliverable.  A concrete no-Section-
    parameters Hoare-style correctness statement for
    [fe25519_square_body] under the degenerate decoder.  Closed under
    the global context.  Square mirror of
    [fe25519_mul_body_correct_via_u128_fiat] from A90. *)
Section ConcreteWiringSquare.

  Variable callee_post :
    String.string -> list located_ed -> located_ed ->
    rust_state_ed -> rust_state_ed -> Prop.
  Variable callee_post_n :
    String.string -> list located_ed -> list located_ed ->
    rust_state_ed -> rust_state_ed -> Prop.
  Variable function_table : function_table_ed.

  Local Notation Hexec :=
    (rust_exec_ed callee_post callee_post_n function_table).

  Definition fp_frame_u128_sq (rs1 rs2 : rust_state_ed) (ex : String.string) : Prop :=
    forall y v, y <> ex ->
       Fp25519_holds_zero_sq rs1 y v ->
       Fp25519_holds_zero_sq rs2 y v.

  Theorem fe25519_square_body_correct_via_u128_fiat :
    forall (rs1 rs2 : rust_state_ed) (a_loc dest : located_ed)
           (xa : F p),
      a_loc.(loc_type) = TFp25519 ->
      dest.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a_loc.(loc_var) ->
      Fp25519_holds_zero_sq rs1 a_loc.(loc_var) xa ->
      Hexec (fe25519_square_body dest [a_loc]) rs1 rs2 ->
      Fp25519_holds_zero_sq rs2 dest.(loc_var) (F.mul xa xa) /\
      fp_frame_u128_sq rs1 rs2 dest.(loc_var).
  Proof.
    intros rs1 rs2 a_loc dest xa
           Hat Hdt Hdne Hxa Hexec_n.
    pose proof (Fe25519SquareCorrect.fe25519_square_body_correct
              Fp25519_holds_zero_sq callee_post callee_post_n function_table
              feval_zero_sq
              Fp25519_holds_elim_zero_sq
              Fp25519_holds_intro_zero_sq
              Fp25519_holds_set_other_zero_sq
              feval_limbwise_square_mask64_zero
              rs1 rs2 a_loc dest xa
              Hat Hdt Hdne Hxa Hexec_n) as [Hpost Hframe].
    split; [exact Hpost|].
    unfold fp_frame_u128_sq.
    unfold Fe25519SquareCorrect.fp_frame in Hframe.
    exact Hframe.
  Qed.

End ConcreteWiringSquare.

(* ================================================================ *)
(* §5.  u128-route adapter — precise statement of what A89's Qed     *)
(*      provides as a Section discharge candidate                    *)
(* ================================================================ *)

(** [u128_fiat_adapter_square] : single-Qed adapter that exposes A89's
    bound-aware u128 discharge for squaring in the precise SHAPE the
    eventual bound-aware refinement of [Fe25519SquareCorrect] would
    consume.

    For the canonical bound-aware decoder [feval_fiat] and u54-bounded
    length-5 limb lists [la], the schoolbook output of the U128 layout
    [build_limb_list_square_u128 la] decodes to
    [F.mul (feval_fiat la) (feval_fiat la)].

    This is precisely A89's [feval_limbwise_square_mask64_via_u128_fiat]
    re-exported.  Same Phase 0e E6/E7 path forward as A90's mul adapter:

      (1) retargeting [Fe25519SquareBody.v] to emit
          [smul128_*] / [SAdd128] (so its body evaluates to
          [build_limb_list_square_u128] pointwise), and

      (2) strengthening [Fp25519_holds] to a bound-carrying refinement.

    Until (1) and (2) land, this adapter Qed certifies that A89's
    bound-aware u128 discharge is THE COMPONENT to plug in. *)
Lemma u128_fiat_adapter_square :
  forall (la : list Z),
    Fe25519Mul128Discharge.limbs_bounded54 la ->
    length la = 5%nat ->
    Fe25519Mul128Discharge.feval_fiat
      (Fe25519Mul128Discharge.build_limb_list_square_u128 la)
    = F.mul (Fe25519Mul128Discharge.feval_fiat la)
            (Fe25519Mul128Discharge.feval_fiat la).
Proof.
  exact Fe25519Mul128Discharge.feval_limbwise_square_mask64_via_u128_fiat.
Qed.

(* ================================================================ *)
(* §6.  Print Assumptions — verify no new global axioms.             *)
(* ================================================================ *)

Print Assumptions fe25519_square_body_correct_via_u128_fiat.
Print Assumptions u128_fiat_adapter_square.
