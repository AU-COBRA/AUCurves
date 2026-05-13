(** * Fe25519CarryCorrect — functional correctness of [fe25519_carry_body].
 *
 *  Companion to [Fe25519CarryBody.v].  Mirrors the section-parameterised
 *  pattern used by [Fe25519AddSubCorrect] / [Fe25519InvertCorrect]:
 *  abstract over the [Fp25519_holds] slot predicate plus a single
 *  per-call oracle hypothesis [carry_inline_correct] on the body,
 *  then derive algebraic correctness of the wrapped function
 *  ([F.eq a (feval dest)], or equivalently in [F p] terms: the
 *  pre/post values are equal, since [chained_carries] is identity
 *  modulo [p]).
 *
 *  Status (Phase 0c, 2026-05-13)
 *  =============================
 *  - [fe25519_carry_body_correct] : Qed via the
 *    [carry_inline_correct] Section hypothesis (scaffold).  Three-line
 *    delegation, same shape as Phase 0a's [REdCall]-style proofs for
 *    [add] / [sub].
 *  - Discharging [carry_inline_correct] mechanically is the Phase 0d
 *    follow-up: peel the 12 [REdLimbStore]s through
 *    [rexec_limb_store_inv] (12 inversions instead of 5 vs add/sub),
 *    track the limb-list state through the chain, then close by
 *    invoking fiat-crypto's [eval_chained_carries] at
 *    [idxs = [0;1;2;3;4;0]] / [n=5] / [s=2^255] / [c=[(1,19)]].
 *    Estimated ~400 LoC (linear in the 12 stores, vs ~200 LoC for
 *    the 5-store add chain in [Fe25519AddSubCorrect]).
 *
 *  History
 *  =======
 *  Phase 0c (this file): scaffold with single [carry_inline_correct]
 *    section hypothesis.  No global axioms.  Acceptable partial per
 *    Phase 0c plan: body + correctness statement + hypothesis is
 *    "success" with full discharge as bonus.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import micromega.Lia.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Spec.Curve25519.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.Fe25519CarryBody.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. Section parameters: abstract field-slot predicate + carry-    *)
(*     inline oracle.                                                *)
(* ================================================================ *)

Section Fe25519CarryCorrect.

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

  (** Frame: non-[exclude] variables keep their Fp values. *)
  Definition fp_frame (rs1 rs2 : rust_state_ed) (exclude : String.string) :
      Prop :=
    forall y v, y <> exclude -> Fp25519_holds rs1 y v -> Fp25519_holds rs2 y v.

  (** Carry-inline oracle.  Mirrors [add_inline_correct] in
      [Fe25519AddSubCorrect.v]: the 12-step [REdLimbStore] chain
      that constitutes [fe25519_carry_body] takes a state in which
      [a] holds a field value [xa], and produces a state in which
      [dest] holds the *same* field value [xa] (since the chain is
      [chained_carries] which is identity modulo [p]).

      Phase 0c keeps this as a single section [Hypothesis]; Phase 0d
      replaces it with a mechanical proof factored through fiat-crypto's
      [eval_chained_carries] over [idxs = [0;1;2;3;4;0]]. *)
  Hypothesis carry_inline_correct :
    forall (dest a : located_ed) (rs1 rs2 : rust_state_ed) (xa : F p),
      dest.(loc_type) = TFp25519 ->
      a.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a.(loc_var) ->
      Fp25519_holds rs1 a.(loc_var) xa ->
      Hexec
        (REdSeq
          (REdLimbStore dest 0%nat (sMask51 (SLimb a.(loc_var) 0%nat)))
        (REdSeq
          (REdLimbStore dest 1%nat
             (SAdd (SLimb a.(loc_var) 1%nat) (sShr51 (SLimb a.(loc_var) 0%nat))))
        (REdSeq
          (REdLimbStore dest 2%nat
             (SAdd (SLimb a.(loc_var) 2%nat) (sShr51 (SLimb dest.(loc_var) 1%nat))))
        (REdSeq
          (REdLimbStore dest 1%nat (sMask51 (SLimb dest.(loc_var) 1%nat)))
        (REdSeq
          (REdLimbStore dest 3%nat
             (SAdd (SLimb a.(loc_var) 3%nat) (sShr51 (SLimb dest.(loc_var) 2%nat))))
        (REdSeq
          (REdLimbStore dest 2%nat (sMask51 (SLimb dest.(loc_var) 2%nat)))
        (REdSeq
          (REdLimbStore dest 4%nat
             (SAdd (SLimb a.(loc_var) 4%nat) (sShr51 (SLimb dest.(loc_var) 3%nat))))
        (REdSeq
          (REdLimbStore dest 3%nat (sMask51 (SLimb dest.(loc_var) 3%nat)))
        (REdSeq
          (REdLimbStore dest 0%nat
             (SAdd (SLimb dest.(loc_var) 0%nat)
                   (sWrap19 (SLimb dest.(loc_var) 4%nat))))
        (REdSeq
          (REdLimbStore dest 4%nat (sMask51 (SLimb dest.(loc_var) 4%nat)))
        (REdSeq
          (REdLimbStore dest 1%nat
             (SAdd (SLimb dest.(loc_var) 1%nat) (sShr51 (SLimb dest.(loc_var) 0%nat))))
          (REdLimbStore dest 0%nat (sMask51 (SLimb dest.(loc_var) 0%nat)))
        ))))))))))) rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) xa /\
      fp_frame rs1 rs2 dest.(loc_var).

(* ================================================================ *)
(* §2. Headline theorem                                              *)
(* ================================================================ *)

  Theorem fe25519_carry_body_correct :
    forall (rs1 rs2 : rust_state_ed) (a_loc dest : located_ed) (xa : F p),
      a_loc.(loc_type) = TFp25519 ->
      dest.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a_loc.(loc_var) ->
      Fp25519_holds rs1 a_loc.(loc_var) xa ->
      Hexec (fe25519_carry_body dest [a_loc]) rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) xa /\
      fp_frame rs1 rs2 dest.(loc_var).
  Proof.
    intros rs1 rs2 a_loc dest xa Hat Hdt Hdne Hxa Hexec_n.
    cbn [fe25519_carry_body] in Hexec_n.
    apply (carry_inline_correct dest a_loc rs1 rs2 xa); assumption.
  Qed.

End Fe25519CarryCorrect.

(** Sanity check: list assumptions of the headline theorem.  Inside
    the Section, the [Variable]/[Hypothesis] parameters appear as
    parameters of the abstracted definition; once the Section closes
    they are universally quantified at the surface.  No new global
    axioms are introduced. *)
Print Assumptions fe25519_carry_body_correct.
