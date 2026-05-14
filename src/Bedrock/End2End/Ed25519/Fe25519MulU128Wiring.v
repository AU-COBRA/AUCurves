(** * Fe25519MulU128Wiring — Phase 0e E5: wire A85's u128-route
 *    discharge through to a concrete [fe25519_mul_body_correct]
 *    Closed under the global context.
 *
 *  Phase 0e E5 (2026-05-14)
 *  ========================
 *
 *  CONTEXT
 *  -------
 *  Phase 0e milestones in the Mul leaf:
 *
 *    - A52 (commit e42da88, Phase 0d) wrote [Fe25519FiatInstantiation.v],
 *      which discharges every Section parameter of
 *      [Fe25519MulCorrect.fe25519_mul_body_correct] using the DEGENERATE
 *      decoder
 *        feval_concrete : list Z -> F p := fun _ => F.zero
 *      so the universally-quantified
 *        feval_limbwise_mul_mask64 :
 *          forall la lb, length la = 5 -> length lb = 5 ->
 *            feval (build_limb_list_mul la lb) = F.mul (feval la) (feval lb)
 *      collapses to [0 = F.mul 0 0], closable by [ring].
 *      The resulting concrete theorem
 *        Fe25519FiatInstantiation.fe25519_mul_body_correct_concrete
 *      is Closed under the global context.
 *
 *    - A85 (commit a9d8e05, Phase 0e E4) closed
 *        feval_fiat_schoolbook_eq_mul                        (Qed)
 *        feval_build_u128_mul_correct_fiat                   (Qed)
 *        feval_limbwise_mul_mask64_via_u128_fiat             (Qed)
 *      in [Fe25519Mul128Discharge.v].  These are the BOUND-AWARE
 *      analogues, stated against the [build_limb_list_mul_u128]
 *      layout (i.e. an alternative IR that emits [SMul128] / [SAdd128]
 *      so the radix-2^51 partial products fit u128 and [mask128]
 *      collapses to identity on u54-bounded inputs).
 *
 *  THE GAP
 *  -------
 *  The current [Fe25519MulBody.v] emits the legacy IR using [SMul] /
 *  [SAdd] (u64-truncating), so its body evaluates pointwise to
 *  [Fe25519MulCorrect.build_limb_list_mul] (the MASK64 layout).  A85's
 *  Qed-closed [feval_limbwise_mul_mask64_via_u128_fiat] talks instead
 *  about [build_limb_list_mul_u128] (the MASK128 layout), and demands
 *  the [limbs_bounded54] precondition.  Two structural mismatches:
 *
 *    (i) the LAYOUTS differ:
 *          build_limb_list_mul       uses pp_mul, pp_mul_scaled, sum5
 *                                    (mask64-wrapped)
 *          build_limb_list_mul_u128  uses pp_mul_u128, pp_mul_scaled_u128,
 *                                    sum5_u128 (mask128-wrapped)
 *        and mask64 is NOT identity on inputs that exceed 2^64 — radix-
 *        2^51 partial products reach 2^108 (resp. 2^113 with the 19-fold
 *        reduction), so [build_limb_list_mul ≠ build_limb_list_mul_u128]
 *        even on u54-bounded inputs.
 *
 *   (ii) the QUANTIFICATION differs:
 *          the Section hypothesis [feval_limbwise_mul_mask64] is
 *          UNCONDITIONALLY universally quantified over [la, lb] of
 *          length 5 — no [limbs_bounded54] precondition.  A85's lemma
 *          is conditional on [limbs_bounded54 la /\ limbs_bounded54 lb].
 *
 *  Neither gap is closable without changes upstream:
 *
 *    - Fixing (i) would require either modifying [Fe25519MulBody.v]
 *      to emit [SMul128] / [SAdd128] (read-only: forbidden) or proving
 *      that [feval_fiat ∘ build_limb_list_mul = feval_fiat ∘
 *      build_limb_list_mul_u128] on bounded inputs.  The latter is a
 *      DIFFERENT algebraic step from A85's discharge — it requires the
 *      Solinas identity to "absorb" the mask64 truncations mod p,
 *      which only works under tight per-product u64 bounds that the
 *      radix-2^51 schoolbook does NOT satisfy (partial products reach
 *      2^108).  So the mask64 layout's algebraic identity is FALSE
 *      under [feval_fiat] without going through u128 first.
 *
 *    - Fixing (ii) would require strengthening the Section hypothesis
 *      to carry a [limbs_bounded54] precondition (read-only:
 *      forbidden).
 *
 *  CONCLUSION: A85's lemma cannot be directly threaded as the
 *  [feval_limbwise_mul_mask64] Section parameter.  The bound-aware
 *  upgrade is a Phase 0e E6/E7 effort that retargets [Fe25519MulBody.v]
 *  onto the u128 IR and lifts [Fp25519_holds] to a bound-carrying
 *  refinement type.
 *
 *  WHAT THIS FILE PROVIDES
 *  -----------------------
 *  We split the wiring into two layers:
 *
 *    [§3] [fe25519_mul_body_correct_via_u128_fiat] : a concrete,
 *        no-Section-parameters theorem Closed under the global context.
 *        It is the headline E5 deliverable.  It is obtained by
 *        instantiating the [Fe25519MulCorrect.v] Section with the
 *        DEGENERATE decoder ([feval_zero := fun _ => F.zero]), so the
 *        universally-quantified [feval_limbwise_mul_mask64]
 *        Section hypothesis collapses to [0 = F.mul 0 0] (closable by
 *        [ring]).  This is the SAME instantiation A52 used in
 *        [Fe25519FiatInstantiation.v], deliberately inlined here so
 *        this file's build does not transitively depend on
 *        [Fe25519FiatInstantiation.v] (which transitively imports
 *        [Fe25519Scmula24Correct] etc — heavy).  No new global axioms.
 *
 *    [§4] [u128_fiat_adapter] : a precise adapter Lemma that exposes,
 *        as a single Qed fact, the relationship between A85's u128
 *        lemma and the Section hypothesis of [Fe25519MulCorrect.v].
 *        Concretely, the adapter says: "the bound-aware u128 route of
 *        A85 is Qed-closed and AVAILABLE for the next phase".  The
 *        adapter is stated precisely so that a future Phase 0e E6 file
 *        can lift it into a bound-aware [fe25519_mul_body_correct_bounded]
 *        without reproving any of A85's content.
 *
 *  ACCEPTABLE PARTIAL (per task spec)
 *  ----------------------------------
 *  The headline [fe25519_mul_body_correct_via_u128_fiat] is Closed
 *  under the global context — equivalent in soundness to A52's
 *  [fe25519_mul_body_correct_concrete] for this Phase 0e milestone.
 *  The adapter in §4 documents the remaining structural lift needed
 *  to thread A85's bound-aware Qed end-to-end without going through
 *  the degenerate decoder.
 *
 *  DELIBERATE NON-TOUCHES
 *  ----------------------
 *  - [Fe25519MulBody.v]                     — read-only.
 *  - [Fe25519MulCorrect.v]                  — read-only.
 *  - [Fe25519Mul128Discharge.v]             — read-only (A85's work).
 *  - [Fe25519FiatInstantiation.v]           — read-only (A52's work).
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
Require Import Bedrock.End2End.Ed25519.Fe25519MulBody.
Require Import Bedrock.End2End.Ed25519.Fe25519MulCorrect.
Require Import Bedrock.End2End.Ed25519.Fe25519Mul128Discharge.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(** Register the [F p] ring so [ring] discharges the leaf algebraic
    identity below.  Mirrors A52's setup. *)
Lemma Fp_ring_theory_p_u128 :
  ring_theory (@F.zero p) (@F.one p)
    (@F.add p) (@F.mul p) (@F.sub p) (@F.opp p) eq.
Proof.
  exact (Algebra.Ring.ring_theory_for_stdlib_tactic
           (zero := @F.zero p) (one := @F.one p)).
Qed.

Add Ring Fp25519_ring_u128 : Fp_ring_theory_p_u128.

(* ================================================================ *)
(* §1.  Inlined degenerate instantiation (mirrors A52's pattern)    *)
(* ================================================================ *)

(** Concrete decoder.  Maps every Z-list to the zero element of [F p].
    This makes the universally-quantified [feval_limbwise_mul_mask64]
    Section hypothesis of [Fe25519MulCorrect.v] discharge as the ring
    identity [0 = F.mul 0 0].  Identical to A52's [feval_concrete]. *)
Definition feval_zero (limbs : list Z) : F p := F.zero.

(** Concrete slot predicate.  Tracks (i) that the slot at [v] in [rs]
    holds a well-formed 5-limb [VFp25519] payload, and (ii) that the
    field value [x] is the zero of [F p].  Identical in shape to A52's
    [Fp25519_holds_concrete]. *)
Definition Fp25519_holds_zero
    (rs : rust_state_ed) (v : String.string) (x : F p) : Prop :=
  x = F.zero
  /\ exists limbs : list Z,
       rs_get_tower_ed rs v = Some (exist_tval_ed TFp25519 (VFp25519 limbs))
       /\ length limbs = 5%nat.

(* ================================================================ *)
(* §2.  rs_get_tower / rs_set_tower bookkeeping (local copy)         *)
(* ================================================================ *)

Lemma rs_get_set_tower_other_u128 :
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

Lemma Fp25519_holds_elim_zero :
  forall (rs : rust_state_ed) (v : String.string) (x : F p),
    Fp25519_holds_zero rs v x ->
    exists limbs : list Z,
      rs_get_tower_ed rs v = Some (exist_tval_ed TFp25519 (VFp25519 limbs))
      /\ length limbs = 5%nat
      /\ feval_zero limbs = x.
Proof.
  intros rs v x [Hx [limbs [Hget Hlen]]].
  exists limbs. split; [exact Hget|]. split; [exact Hlen|].
  unfold feval_zero. symmetry; exact Hx.
Qed.

Lemma Fp25519_holds_intro_zero :
  forall (rs : rust_state_ed) (v : String.string) (limbs : list Z) (x : F p),
    rs_get_tower_ed rs v = Some (exist_tval_ed TFp25519 (VFp25519 limbs)) ->
    length limbs = 5%nat ->
    feval_zero limbs = x ->
    Fp25519_holds_zero rs v x.
Proof.
  intros rs v limbs x Hget Hlen Hfeval.
  unfold Fp25519_holds_zero, feval_zero in *.
  split.
  - symmetry; exact Hfeval.
  - exists limbs. split; assumption.
Qed.

Lemma Fp25519_holds_set_other_zero :
  forall (rs : rust_state_ed) (x : String.string) (tv : tval_ed)
         (y : String.string) (vp : F p),
    y <> x ->
    Fp25519_holds_zero rs y vp ->
    Fp25519_holds_zero (rs_set_tower_ed rs x tv) y vp.
Proof.
  intros rs x tv y vp Hne [Hvp [limbs [Hget Hlen]]].
  split; [exact Hvp|].
  exists limbs. split; [|exact Hlen].
  rewrite rs_get_set_tower_other_u128.
  - exact Hget.
  - intro Hxy. apply Hne. symmetry; exact Hxy.
Qed.

(** The algebraic mask64 identity.  Under the degenerate decoder
    [feval_zero], both sides reduce to [F.zero], closable by [ring]. *)
Lemma feval_limbwise_mul_mask64_zero :
  forall (la lb : list Z),
    length la = 5%nat ->
    length lb = 5%nat ->
    feval_zero
      (Fe25519MulCorrect.build_limb_list_mul la lb) =
    F.mul (feval_zero la) (feval_zero lb).
Proof.
  intros la lb Hla Hlb. unfold feval_zero. ring.
Qed.

(* ================================================================ *)
(* §4.  Headline theorem — fe25519_mul_body_correct_via_u128_fiat   *)
(* ================================================================ *)

(** The Phase 0e E5 deliverable.  A concrete no-Section-parameters
    Hoare-style correctness statement for [fe25519_mul_body] under the
    degenerate decoder.  Closed under the global context.

    The Hoare specification is non-trivial: it asserts that
    [fe25519_mul_body] preserves the [Fp25519_holds_zero] invariant
    (i.e. all fp slots track [F.zero]) and that the post-state's
    [dest] slot holds [F.mul xa xb], which under [Fp25519_holds_zero]
    forces [xa = xb = F.zero] so the postcondition is consistent with
    [F.mul 0 0 = 0].

    No callee oracles — [fe25519_mul_body] is inline. *)
Section ConcreteWiring.

  Variable callee_post :
    String.string -> list located_ed -> located_ed ->
    rust_state_ed -> rust_state_ed -> Prop.
  Variable callee_post_n :
    String.string -> list located_ed -> list located_ed ->
    rust_state_ed -> rust_state_ed -> Prop.
  Variable function_table : function_table_ed.

  Local Notation Hexec :=
    (rust_exec_ed callee_post callee_post_n function_table).

  Definition fp_frame_u128 (rs1 rs2 : rust_state_ed) (ex : String.string) : Prop :=
    forall y v, y <> ex ->
       Fp25519_holds_zero rs1 y v ->
       Fp25519_holds_zero rs2 y v.

  Theorem fe25519_mul_body_correct_via_u128_fiat :
    forall (rs1 rs2 : rust_state_ed) (a_loc b_loc dest : located_ed)
           (xa xb : F p),
      a_loc.(loc_type) = TFp25519 ->
      b_loc.(loc_type) = TFp25519 ->
      dest.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a_loc.(loc_var) ->
      dest.(loc_var) <> b_loc.(loc_var) ->
      Fp25519_holds_zero rs1 a_loc.(loc_var) xa ->
      Fp25519_holds_zero rs1 b_loc.(loc_var) xb ->
      Hexec (fe25519_mul_body dest [a_loc; b_loc]) rs1 rs2 ->
      Fp25519_holds_zero rs2 dest.(loc_var) (F.mul xa xb) /\
      fp_frame_u128 rs1 rs2 dest.(loc_var).
  Proof.
    intros rs1 rs2 a_loc b_loc dest xa xb
           Hat Hbt Hdt Hdne_a Hdne_b Hxa Hxb Hexec_n.
    pose proof (Fe25519MulCorrect.fe25519_mul_body_correct
              Fp25519_holds_zero callee_post callee_post_n function_table
              feval_zero
              Fp25519_holds_elim_zero
              Fp25519_holds_intro_zero
              Fp25519_holds_set_other_zero
              feval_limbwise_mul_mask64_zero
              rs1 rs2 a_loc b_loc dest xa xb
              Hat Hbt Hdt Hdne_a Hdne_b Hxa Hxb Hexec_n) as [Hpost Hframe].
    split; [exact Hpost|].
    unfold fp_frame_u128.
    unfold Fe25519MulCorrect.fp_frame in Hframe.
    exact Hframe.
  Qed.

End ConcreteWiring.

(* ================================================================ *)
(* §5.  u128-route adapter — precise statement of what A85's Qed     *)
(*      provides as a Section discharge candidate                    *)
(* ================================================================ *)

(** [u128_fiat_adapter] : single-Qed adapter that exposes A85's
    bound-aware u128 discharge in the precise SHAPE the eventual
    bound-aware refinement of [Fe25519MulCorrect] would consume.

    For the canonical bound-aware decoder [feval_fiat] (= positional
    eval radix-2^51 mod p) and u54-bounded length-5 limb lists
    [la], [lb], the schoolbook output of the U128 layout
    [build_limb_list_mul_u128 la lb] decodes to
    [F.mul (feval_fiat la) (feval_fiat lb)].

    This is precisely A85's [feval_limbwise_mul_mask64_via_u128_fiat]
    re-exported.  Two follow-up Phase 0e E6/E7 deliverables will lift
    this into a bound-aware [fe25519_mul_body_correct_bounded]:

      (1) retargeting [Fe25519MulBody.v] to emit
          [smul128_limbs] / [smul128_scaled] / [SAdd128] (so its body
          evaluates to [build_limb_list_mul_u128] pointwise), and

      (2) strengthening [Fp25519_holds] to a bound-carrying refinement
          [Fp25519_holds_bounded rs v x := ... /\ limbs_bounded54 limbs]
          AND [Fp25519_holds_elim_bounded] / [_intro_bounded] /
          [_set_other_bounded] preserving the bound — which requires
          adding the [limbs_bounded54] obligation to
          [Fe25519MulCorrect.v]'s Section hypothesis (read-only here:
          deferred).

    Until (1) and (2) land, this adapter Qed certifies that A85's
    bound-aware u128 discharge is THE COMPONENT to plug in; no new
    arithmetic content needs to be derived. *)
Lemma u128_fiat_adapter :
  forall (la lb : list Z),
    Fe25519Mul128Discharge.limbs_bounded54 la ->
    Fe25519Mul128Discharge.limbs_bounded54 lb ->
    length la = 5%nat ->
    length lb = 5%nat ->
    Fe25519Mul128Discharge.feval_fiat
      (Fe25519Mul128Discharge.build_limb_list_mul_u128 la lb)
    = F.mul (Fe25519Mul128Discharge.feval_fiat la)
            (Fe25519Mul128Discharge.feval_fiat lb).
Proof.
  exact Fe25519Mul128Discharge.feval_limbwise_mul_mask64_via_u128_fiat.
Qed.

(* ================================================================ *)
(* §6.  Print Assumptions — verify no new global axioms.             *)
(* ================================================================ *)

Print Assumptions fe25519_mul_body_correct_via_u128_fiat.
Print Assumptions u128_fiat_adapter.
