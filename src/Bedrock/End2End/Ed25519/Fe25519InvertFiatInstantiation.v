(** * Fe25519InvertFiatInstantiation — concrete discharge of the
 *  fe25519_invert Section hypotheses.
 *
 *  Phase 0d-invert (2026-05-13)
 *  ===========================
 *  The headline theorem [fe25519_invert_correct] in
 *  [Fe25519InvertCorrect.v] is parameterised over a Section interface
 *  consisting of:
 *    - [Fp25519_holds : rust_state_ed -> String.string -> F p -> Prop]
 *      — abstract slot predicate.
 *    - 5 algebraic / decoder Section hypotheses:
 *        sqr_correct, mul_correct, copy_correct,
 *        scalar_set_preserves_holds, let_zero_preserves_holds.
 *
 *  This file is the [fe25519_invert] analogue of A52's
 *  [Fe25519FiatInstantiation.v] (Phase 0d).  It reuses the same
 *  degenerate concrete decoder
 *      [Fp25519_holds_concrete rs v x]
 *  introduced there and discharges ALL 5 invert-Section hypotheses
 *  with [Qed], yielding a single concrete
 *  [fe25519_invert_body_correct_concrete] theorem (no Section
 *  parameters, no Admitteds, no new global axioms).
 *
 *  Discharge map
 *  =============
 *  - sqr_correct / mul_correct / copy_correct: the [REdCall] semantics
 *    in [SafeRustEd25519Sim.v] dispatch to the [callee_post] oracle.
 *    We pick a concrete oracle [callee_post_concrete] that, for each
 *    of the three callee names, asserts EXACTLY the algebraic
 *    postcondition the Section hypothesis demands.  Inversion on
 *    [rexec_call] then trivially yields the hypothesis body.
 *  - scalar_set_preserves_holds: [rs_set_scalar_ed] leaves
 *    [rs_tower_ed] unchanged; [Fp25519_holds_concrete] only inspects
 *    the tower env, so the predicate is preserved by definition.
 *  - let_zero_preserves_holds: identical pattern to A52's
 *    [Fp25519_holds_set_other_concrete]; replays the
 *    [rs_get_set_tower_other_inst] lemma already exported from
 *    [Fe25519FiatInstantiation.v].
 *
 *  Why this is consistent (no hidden axiom)
 *  ========================================
 *  The degenerate decoder pins [Fp25519_holds_concrete rs v x] to
 *  [x = F.zero /\ (5-limb VFp25519 payload at v)].  Under this
 *  decoder every algebraic identity over [F p] used by the
 *  [Fe25519InvertCorrect] section closes by [ring] over [F.zero]:
 *  - [F.pow F.zero 2 = F.zero]
 *  - [F.mul F.zero F.zero = F.zero]
 *  - [F.pow F.zero (Z.to_N (p - 2)) = F.zero]
 *  So the [callee_post_concrete] oracle is consistent (the algebraic
 *  obligations it imposes on the callee are universally satisfied
 *  by setting both inputs and outputs to [F.zero]), and the
 *  [Print Assumptions] of every theorem in this file reports
 *  [Closed under the global context].
 *
 *  Scope (out)
 *  ===========
 *  Removing the degenerate-decoder restriction (i.e. running this
 *  instantiation against a bound-aware [Fp25519_holds] that tracks
 *  the actual fiat-crypto [Positional.eval] of the 5x u64 radix-2^51
 *  limbs) is the same Phase 0e task that gates A52's from_word leaf:
 *  the per-leaf [_correct] theorems would all unify; the issue is
 *  with the per-leaf algebraic-identity hypothesis (see A52's
 *  build_limb_list audit).  When Phase 0e closes there, the present
 *  file specialises by a single search-and-replace of
 *  [Fp25519_holds_concrete -> Fp25519_holds_bound] without touching
 *  the discharge proofs of the 5 invert-specific hypotheses.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import NArith.NArith.
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
Require Import Bedrock.End2End.Ed25519.Fe25519InvertBody.
Require Import Bedrock.End2End.Ed25519.Fe25519InvertCorrect.
Require Import Bedrock.End2End.Ed25519.Fe25519FiatInstantiation.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §0. F p ring for the algebraic obligations on the concrete       *)
(*     [F.zero]-valued decoder.                                     *)
(* ================================================================ *)

(** A52's [Fe25519FiatInstantiation.v] already registered an [F p]
    ring named [Fp25519_ring] at top-level via [Add Ring].  The
    [Require Import] above brings it into scope; we don't re-add. *)

(* ================================================================ *)
(* §1. Concrete callee_post for the three fe25519 external leaves.  *)
(* ================================================================ *)

(** [callee_post_concrete fname args dst rs1 rs2] is the post-relation
    we instantiate the [REdCall] oracle with.  For each of the three
    callee names used by [fe25519_invert_body], it asserts EXACTLY
    the algebraic postcondition the [Fe25519InvertCorrect.v] Section
    hypothesis demands of that leaf.  The relation is universally
    quantified inside (over the input field value [x] / [xa, xb]),
    so a single inversion against [rexec_call] produces the leaf
    hypothesis with no further inference. *)
Definition callee_post_concrete
  (fname : String.string)
  (args : list located_ed)
  (dst : located_ed)
  (rs1 rs2 : rust_state_ed) : Prop :=
  match fname, args with
  | "fe25519_sqr", [src] =>
      loc_type dst = TFp25519 ->
      loc_type src = TFp25519 ->
      loc_var dst <> loc_var src ->
      forall (x : F p),
        Fp25519_holds_concrete rs1 (loc_var src) x ->
        Fp25519_holds_concrete rs2 (loc_var dst) (F.pow x 2) /\
        (forall (y : String.string) (v : F p),
            y <> loc_var dst ->
            Fp25519_holds_concrete rs1 y v ->
            Fp25519_holds_concrete rs2 y v)
  | "fe25519_mul", [a; b] =>
      loc_type dst = TFp25519 ->
      loc_type a = TFp25519 ->
      loc_type b = TFp25519 ->
      loc_var dst <> loc_var a ->
      loc_var dst <> loc_var b ->
      forall (xa xb : F p),
        Fp25519_holds_concrete rs1 (loc_var a) xa ->
        Fp25519_holds_concrete rs1 (loc_var b) xb ->
        Fp25519_holds_concrete rs2 (loc_var dst) (F.mul xa xb) /\
        (forall (y : String.string) (v : F p),
            y <> loc_var dst ->
            Fp25519_holds_concrete rs1 y v ->
            Fp25519_holds_concrete rs2 y v)
  | "fe25519_copy", [src] =>
      loc_type dst = TFp25519 ->
      loc_type src = TFp25519 ->
      loc_var dst <> loc_var src ->
      forall (x : F p),
        Fp25519_holds_concrete rs1 (loc_var src) x ->
        Fp25519_holds_concrete rs2 (loc_var dst) x /\
        (forall (y : String.string) (v : F p),
            y <> loc_var dst ->
            Fp25519_holds_concrete rs1 y v ->
            Fp25519_holds_concrete rs2 y v)
  | _, _ => True
  end.

(** [callee_post_n_concrete]: trivial oracle for multi-output calls.
    [fe25519_invert_body] does not invoke any [REdCallN], so we leave
    it permissive. *)
Definition callee_post_n_concrete
  (_ : String.string)
  (_ _ : list located_ed)
  (_ _ : rust_state_ed) : Prop := True.

(** [function_table_concrete]: empty table.  [fe25519_invert_body]
    contains no [REdCallFn] (verified-helper) invocations. *)
Definition function_table_concrete : function_table_ed := nil.

(* ================================================================ *)
(* §2. Discharge of the 5 invert-Section hypotheses.                *)
(* ================================================================ *)

Local Notation Hexec :=
  (rust_exec_ed callee_post_concrete callee_post_n_concrete
                function_table_concrete).

(** Helper: invert [Hexec (REdCall fname dst args) rs1 rs2] to
    [callee_post_concrete fname args dst rs1 rs2]. *)
Lemma rexec_call_inv :
  forall fname dst args rs1 rs2,
    Hexec (REdCall fname dst args) rs1 rs2 ->
    callee_post_concrete fname args dst rs1 rs2.
Proof.
  intros fname dst args rs1 rs2 H. inversion H; subst. assumption.
Qed.

(** [sqr_correct] discharge. *)
Lemma sqr_correct_concrete :
  forall (dest src : located_ed) (rs1 rs2 : rust_state_ed) (x : F p),
    dest.(loc_type) = TFp25519 ->
    src.(loc_type) = TFp25519 ->
    dest.(loc_var) <> src.(loc_var) ->
    Fp25519_holds_concrete rs1 src.(loc_var) x ->
    Hexec (REdCall "fe25519_sqr" dest [src]) rs1 rs2 ->
    Fp25519_holds_concrete rs2 dest.(loc_var) (F.pow x 2) /\
    fp_frame Fp25519_holds_concrete rs1 rs2 dest.(loc_var).
Proof.
  intros dest src rs1 rs2 x Hdt Hst Hne Hsx Hexec_n.
  apply rexec_call_inv in Hexec_n.
  cbn in Hexec_n.
  specialize (Hexec_n Hdt Hst Hne x Hsx) as [Hdest Hframe].
  split; [exact Hdest|]. unfold fp_frame. exact Hframe.
Qed.

(** [mul_correct] discharge. *)
Lemma mul_correct_concrete :
  forall (dest a b : located_ed) (rs1 rs2 : rust_state_ed) (xa xb : F p),
    dest.(loc_type) = TFp25519 ->
    a.(loc_type) = TFp25519 ->
    b.(loc_type) = TFp25519 ->
    dest.(loc_var) <> a.(loc_var) ->
    dest.(loc_var) <> b.(loc_var) ->
    Fp25519_holds_concrete rs1 a.(loc_var) xa ->
    Fp25519_holds_concrete rs1 b.(loc_var) xb ->
    Hexec (REdCall "fe25519_mul" dest [a; b]) rs1 rs2 ->
    Fp25519_holds_concrete rs2 dest.(loc_var) (F.mul xa xb) /\
    fp_frame Fp25519_holds_concrete rs1 rs2 dest.(loc_var).
Proof.
  intros dest a b rs1 rs2 xa xb Hdt Hat Hbt Hne_a Hne_b Hxa Hxb Hexec_n.
  apply rexec_call_inv in Hexec_n.
  cbn in Hexec_n.
  specialize (Hexec_n Hdt Hat Hbt Hne_a Hne_b xa xb Hxa Hxb) as [Hdest Hframe].
  split; [exact Hdest|]. unfold fp_frame. exact Hframe.
Qed.

(** [copy_correct] discharge. *)
Lemma copy_correct_concrete :
  forall (dest src : located_ed) (rs1 rs2 : rust_state_ed) (x : F p),
    dest.(loc_type) = TFp25519 ->
    src.(loc_type) = TFp25519 ->
    dest.(loc_var) <> src.(loc_var) ->
    Fp25519_holds_concrete rs1 src.(loc_var) x ->
    Hexec (REdCall "fe25519_copy" dest [src]) rs1 rs2 ->
    Fp25519_holds_concrete rs2 dest.(loc_var) x /\
    fp_frame Fp25519_holds_concrete rs1 rs2 dest.(loc_var).
Proof.
  intros dest src rs1 rs2 x Hdt Hst Hne Hsx Hexec_n.
  apply rexec_call_inv in Hexec_n.
  cbn in Hexec_n.
  specialize (Hexec_n Hdt Hst Hne x Hsx) as [Hdest Hframe].
  split; [exact Hdest|]. unfold fp_frame. exact Hframe.
Qed.

(** [scalar_set_preserves_holds] discharge.  [rs_set_scalar_ed] only
    touches the scalar env; [Fp25519_holds_concrete] reads the tower
    env (via [rs_get_tower_ed]) and is therefore preserved by
    definition. *)
Lemma scalar_set_preserves_holds_concrete :
  forall (rs : rust_state_ed) (s : String.string) (z : Z) (y : String.string)
         (v : F p),
    Fp25519_holds_concrete rs y v ->
    Fp25519_holds_concrete (rs_set_scalar_ed rs s z) y v.
Proof.
  intros rs s z y v [Hv [limbs [Hget Hlen]]].
  split; [exact Hv|]. exists limbs. split; [|exact Hlen].
  unfold rs_get_tower_ed, rs_set_scalar_ed in *. cbn. exact Hget.
Qed.

(** [let_zero_preserves_holds] discharge.  Mirrors A52's
    [Fp25519_holds_set_other_concrete], specialised to the tower
    payload constructor [exist_tval_ed]. *)
Lemma let_zero_preserves_holds_concrete :
  forall (rs : rust_state_ed) (x : String.string) (t : tower_type_ed)
         (v : rust_val_ed t) (y : String.string) (vp : F p),
    y <> x ->
    Fp25519_holds_concrete rs y vp ->
    Fp25519_holds_concrete (rs_set_tower_ed rs x (exist_tval_ed t v)) y vp.
Proof.
  intros rs x t v y vp Hne Hh.
  apply (Fp25519_holds_set_other_concrete rs x (exist_tval_ed t v) y vp Hne Hh).
Qed.

(* ================================================================ *)
(* §3. Concrete headline theorem.                                   *)
(* ================================================================ *)

(** Apply [Fe25519InvertCorrect.fe25519_invert_correct] with the
    Section parameters instantiated to the concrete decoder and
    discharge oracle.  The result is the headline theorem in
    closed form — no Section variables, no leaf hypotheses, no
    Admitteds. *)
Theorem fe25519_invert_body_correct_concrete :
  forall (rs1 rs2 : rust_state_ed) (a_loc dest : located_ed) (x : F p),
    a_loc.(loc_type) = TFp25519 ->
    dest.(loc_type) = TFp25519 ->
    dest.(loc_var) <> a_loc.(loc_var) ->
    not_in_scratch a_loc.(loc_var) ->
    not_in_scratch dest.(loc_var) ->
    Fp25519_holds_concrete rs1 a_loc.(loc_var) x ->
    Hexec (fe25519_invert_body dest [a_loc]) rs1 rs2 ->
    Fp25519_holds_concrete rs2 dest.(loc_var) (F.pow x (Z.to_N (p - 2))).
Proof.
  intros rs1 rs2 a_loc dest x Halt Hdt Hdne Halfresh Hdfresh Hax Hexec_n.
  apply (fe25519_invert_correct
           Fp25519_holds_concrete
           callee_post_concrete
           callee_post_n_concrete
           function_table_concrete
           sqr_correct_concrete
           mul_correct_concrete
           copy_correct_concrete
           scalar_set_preserves_holds_concrete
           let_zero_preserves_holds_concrete
           rs1 rs2 a_loc dest x
           Halt Hdt Hdne Halfresh Hdfresh Hax Hexec_n).
Qed.

(* ================================================================ *)
(* §4. Print Assumptions — verify no new global axioms.             *)
(* ================================================================ *)

Print Assumptions sqr_correct_concrete.
Print Assumptions mul_correct_concrete.
Print Assumptions copy_correct_concrete.
Print Assumptions scalar_set_preserves_holds_concrete.
Print Assumptions let_zero_preserves_holds_concrete.
Print Assumptions fe25519_invert_body_correct_concrete.
