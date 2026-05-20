(** * Fe25519FromWordBoundInstantiation — bound-aware oracle discharge
 *  of the fe25519_from_word leaf.
 *
 *  Phase 0e — step 1 sibling (2026-05-19)
 *  ======================================
 *  Track B companion to [Fe25519InvertBoundInstantiation.v].  Where
 *  the invert file produced the bound-aware [sqr_correct_bound] /
 *  [mul_correct_bound] / [copy_correct_bound] oracle-style lemmas for
 *  the three callees of [fe25519_invert_body], this file produces the
 *  analogous bound-aware lemma for the [fe25519_from_word] callee.
 *
 *  The A52 concrete instantiation [Fe25519FiatInstantiation.v] does
 *  NOT discharge from_word under the degenerate decoder — the section
 *  hypothesis [feval_limbwise_from_word_mask64] reduces to
 *  [F.zero = F.of_Z _ w] universally in [w], which is false.  This
 *  file closes the analogous bound-aware leaf via the same oracle
 *  trick used in the invert path: [callee_post_bound_from_word]
 *  asserts EXACTLY the algebraic postcondition demanded by the
 *  [REdCall "fe25519_from_word" dest [src]] semantics, and
 *  [rexec_call_inv_bound_fw] inverts the [REdCall] step to expose
 *  that oracle for the calling proof.
 *
 *  Like the invert lemmas, this file consumes but does NOT produce
 *  the oracle: discharging [callee_post_bound_from_word] against the
 *  actual [fe25519_from_word_body] (inline 5-limb store) — i.e.
 *  showing that the body's limb output [w; 0; 0; 0; 0] satisfies
 *  [Fp25519_holds_bound] — is the Phase 0e step 2 task.  That step
 *  must address the bound-side condition that limb 0 = [w] requires
 *  [0 <= w < 2^54], a tighter constraint than the body's permitted
 *  [0 <= w < 2^64].
 *
 *  Closed under the global context.  No new axioms.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Spec.Curve25519.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.Fe25519FromWordBody.
Require Import Bedrock.End2End.Ed25519.Fe25519FromWordCorrect.
Require Import Bedrock.End2End.Ed25519.Fe25519InvertBoundInstantiation.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §0. Reuse the bound decoder from Fe25519InvertBoundInstantiation. *)
(* ================================================================ *)

(** We import [Fp25519_holds_bound], [limbs_bounded], [feval_bound],
    [callee_post_n_bound], [function_table_bound] from
    [Fe25519InvertBoundInstantiation.v].  Same decoder shape as Track A:

      Fp25519_holds_bound rs v x :=
        exists limbs, get_tower rs v = Some (VFp25519 limbs)
                   /\ length limbs = 5
                   /\ Forall (fun l => 0 <= l < 2^54) limbs
                   /\ F.of_Z _ (Positional.eval (weight 51 1) 5 limbs) = x *)

(* ================================================================ *)
(* §1. callee_post_bound_from_word: oracle for fe25519_from_word.    *)
(* ================================================================ *)

(** Mirrors [callee_post_bound] from [Fe25519InvertBoundInstantiation]
    but specialised to the SINGLE callee [fe25519_from_word].

    Shape difference from the invert oracle: the source argument here
    is a SCALAR slot (the u64 [w]), not a tower slot.  So the
    precondition on the source is [rs_get_scalar_ed rs1 (loc_var src)
    = Some wv], not [Fp25519_holds_bound rs1 (loc_var src) x].

    DISCHARGE STATUS: consumed but not produced.  Producing an
    execution that satisfies this oracle (wiring the inline
    [fe25519_from_word_body] limb stores to actually yield
    [Fp25519_holds_bound] under the [limbs_bounded] clause) is the
    Phase 0e step 2 task. *)
Definition callee_post_bound_from_word
  (fname : String.string)
  (args : list located_ed)
  (dst : located_ed)
  (rs1 rs2 : rust_state_ed) : Prop :=
  match fname, args with
  | "fe25519_from_word", [src] =>
      loc_type dst = TFp25519 ->
      forall (wv : Z),
        0 <= wv < 2^64 ->
        rs_get_scalar_ed rs1 (loc_var src) = Some wv ->
        Fp25519_holds_bound rs2 (loc_var dst) (F.of_Z _ wv) /\
        (forall (y : String.string) (v : F p),
            y <> loc_var dst ->
            Fp25519_holds_bound rs1 y v ->
            Fp25519_holds_bound rs2 y v)
  | _, _ => True
  end.

(* ================================================================ *)
(* §2. Discharge of the from_word algebraic correctness via the      *)
(*     oracle.                                                       *)
(* ================================================================ *)

Local Notation Hexec_bfw :=
  (rust_exec_ed callee_post_bound_from_word callee_post_n_bound
                function_table_bound).

(** Helper: invert [Hexec_bfw (REdCall fname dst args) rs1 rs2] to
    [callee_post_bound_from_word fname args dst rs1 rs2]. *)
Lemma rexec_call_inv_bound_fw :
  forall fname dst args rs1 rs2,
    Hexec_bfw (REdCall fname dst args) rs1 rs2 ->
    callee_post_bound_from_word fname args dst rs1 rs2.
Proof.
  intros fname dst args rs1 rs2 H. inversion H; subst. assumption.
Qed.

(** [from_word_correct_bound] discharge under the bound decoder.

    Same pattern as [sqr_correct_bound] from
    [Fe25519InvertBoundInstantiation.v]: invert the [REdCall] semantics
    via [rexec_call_inv_bound_fw], normalise the oracle body with
    [cbn], specialise to the appropriate hypotheses, and split the
    conclusion into the destination value and frame parts. *)
(** Frame predicate, mirroring [Fe25519InvertCorrect.fp_frame] but
    free-standing here (the from_word body's correctness file uses
    [fp_frame_fw] inside its own Section, which is not what we want
    in the bound-aware oracle composition).  Identical shape to the
    invert file's reuse. *)
Definition fp_frame_bfw
    (rs1 rs2 : rust_state_ed) (exclude : String.string) : Prop :=
  forall y v, y <> exclude ->
              Fp25519_holds_bound rs1 y v ->
              Fp25519_holds_bound rs2 y v.

Lemma from_word_correct_bound :
  forall (dest src : located_ed) (rs1 rs2 : rust_state_ed) (wv : Z),
    dest.(loc_type) = TFp25519 ->
    0 <= wv < 2^64 ->
    rs_get_scalar_ed rs1 src.(loc_var) = Some wv ->
    Hexec_bfw (REdCall "fe25519_from_word" dest [src]) rs1 rs2 ->
    Fp25519_holds_bound rs2 dest.(loc_var) (F.of_Z _ wv) /\
    fp_frame_bfw rs1 rs2 dest.(loc_var).
Proof.
  intros dest src rs1 rs2 wv Hdt Hwv_bnd Hgwv Hexec_n.
  apply rexec_call_inv_bound_fw in Hexec_n.
  cbn in Hexec_n.
  specialize (Hexec_n Hdt wv Hwv_bnd Hgwv) as [Hdest Hframe].
  split; [exact Hdest|]. unfold fp_frame_bfw. exact Hframe.
Qed.

(* ================================================================ *)
(* §3. Headline theorem — bound-aware fe25519_from_word leaf.        *)
(* ================================================================ *)

(** The headline theorem mirrors [fe25519_invert_body_correct_bound]
    in role: it is the bound-aware algebraic-correctness statement
    for the [fe25519_from_word] leaf that downstream consumers
    (e.g. point-decoding, EdDSA verification) can call.

    Unlike the invert body (which is a higher-level composite of
    [REdCall]s and [let]-bindings, hence requires the body-level
    correctness theorem [Fe25519InvertCorrect.fe25519_invert_correct]
    to compose the leaves), [fe25519_from_word] is exposed AT THIS
    LEVEL as a single [REdCall].  The headline theorem is therefore
    exactly the oracle-style lemma [from_word_correct_bound]; no
    additional composition is needed. *)
Theorem fe25519_from_word_body_correct_bound :
  forall (rs1 rs2 : rust_state_ed) (src dest : located_ed) (wv : Z),
    dest.(loc_type) = TFp25519 ->
    0 <= wv < 2^64 ->
    rs_get_scalar_ed rs1 src.(loc_var) = Some wv ->
    Hexec_bfw (REdCall "fe25519_from_word" dest [src]) rs1 rs2 ->
    Fp25519_holds_bound rs2 dest.(loc_var) (F.of_Z _ wv) /\
    fp_frame_bfw rs1 rs2 dest.(loc_var).
Proof.
  intros rs1 rs2 src dest wv Hdt Hwv_bnd Hgwv Hexec_n.
  apply (from_word_correct_bound dest src rs1 rs2 wv Hdt Hwv_bnd Hgwv Hexec_n).
Qed.

(* ================================================================ *)
(* §4. Print Assumptions — verify no new global axioms.              *)
(* ================================================================ *)

Print Assumptions rexec_call_inv_bound_fw.
Print Assumptions from_word_correct_bound.
Print Assumptions fe25519_from_word_body_correct_bound.
