(** * Fe25519SquareCorrect — functional correctness of
 *  [fe25519_square_body].
 *
 *  Companion to [Fe25519SquareBody.v].  Mirrors the section-parameterised
 *  pattern used by [Fe25519MulCorrect.v] and [Fe25519CarryCorrect.v]:
 *  abstract over the [Fp25519_holds] slot predicate plus a per-call
 *  algebraic oracle on the inline body, then derive functional
 *  correctness of the wrapped function.
 *
 *  Status (Phase 0c, 2026-05-13)
 *  =============================
 *  - [fe25519_square_body_correct] :  Qed (three-line delegation to
 *      [square_inline_correct]).
 *  - [square_inline_correct] :  Section [Hypothesis] — captures the
 *      radix-2^51 schoolbook + reduce algebra specialised to a = b.
 *      Discharge is the substantive Phase 0d/0e task; deferred per the
 *      [Fe25519SquareBody.v] header FOLLOW-UP.
 *
 *  The Section hypothesis surface mirrors the Phase 0d
 *  [mul_inline_correct] shape (single coarse-grained oracle on the
 *  full sum-of-products tree).  The argument count is reduced from
 *  three locators [{dest; a; b}] to two [{dest; a}] reflecting the
 *  unary signature of [fe25519_square]; the postcondition is
 *  [F.mul xa xa] (squaring as [F.mul] of the same operand).
 *  No new global axioms.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Spec.Curve25519.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.Fe25519SquareBody.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. Section parameters: abstract field-slot predicate + the       *)
(*     square-body algebraic hypothesis.                             *)
(* ================================================================ *)

Section Fe25519SquareCorrect.

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

  (** Inline-body correctness for [fe25519_square_body].  The body
      executes five [REdLimbStore]s whose RHS expressions encode the
      symmetric 5×5 radix-2^51 schoolbook (see [Fe25519SquareBody.v] §2
      for the precise sums).  The algebraic fact that this matches
      [F.mul xa xa] (i.e. squaring) mirrors fiat-crypto's
      [Positional.eval_squaremod] + the radix-2^51 carry chain
      ([fiat_25519_carry_square] in the extracted C).  Mechanical port
      through the [Fp25519_holds] interface — which requires u128 /
      partial-product modelling beyond the current [SMul] semantics —
      is the Phase 0d / 0e follow-up. *)
  Hypothesis square_inline_correct :
    forall (dest a : located_ed) (rs1 rs2 : rust_state_ed) (xa : F p),
      dest.(loc_type) = TFp25519 ->
      a.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a.(loc_var) ->
      Fp25519_holds rs1 a.(loc_var) xa ->
      Hexec
        (REdSeq
           (REdLimbStore dest 0%nat
              (SAdd (ssq_diag a.(loc_var) 0)
                (SAdd (ssq_cross_scaled a.(loc_var) 1 4 38)
                      (ssq_cross_scaled a.(loc_var) 2 3 38))))
           (REdSeq
             (REdLimbStore dest 1%nat
                (SAdd (ssq_cross_scaled a.(loc_var) 0 1 2)
                  (SAdd (ssq_cross_scaled a.(loc_var) 2 4 38)
                        (ssq_diag_scaled a.(loc_var) 3 19))))
             (REdSeq
               (REdLimbStore dest 2%nat
                  (SAdd (ssq_cross_scaled a.(loc_var) 0 2 2)
                    (SAdd (ssq_diag a.(loc_var) 1)
                          (ssq_cross_scaled a.(loc_var) 3 4 38))))
               (REdSeq
                 (REdLimbStore dest 3%nat
                    (SAdd (ssq_cross_scaled a.(loc_var) 0 3 2)
                      (SAdd (ssq_cross_scaled a.(loc_var) 1 2 2)
                            (ssq_diag_scaled a.(loc_var) 4 19))))
                 (REdLimbStore dest 4%nat
                    (SAdd (ssq_cross_scaled a.(loc_var) 0 4 2)
                      (SAdd (ssq_cross_scaled a.(loc_var) 1 3 2)
                            (ssq_diag a.(loc_var) 2))))))))
        rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) (F.mul xa xa) /\
      fp_frame rs1 rs2 dest.(loc_var).

(* ================================================================ *)
(* §2. Headline theorem                                              *)
(* ================================================================ *)

  Theorem fe25519_square_body_correct :
    forall (rs1 rs2 : rust_state_ed) (a_loc dest : located_ed) (xa : F p),
      a_loc.(loc_type) = TFp25519 ->
      dest.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a_loc.(loc_var) ->
      Fp25519_holds rs1 a_loc.(loc_var) xa ->
      Hexec (fe25519_square_body dest [a_loc]) rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) (F.mul xa xa) /\
      fp_frame rs1 rs2 dest.(loc_var).
  Proof.
    intros rs1 rs2 a_loc dest xa Hat Hdt Hdne Hxa Hexec_n.
    cbn [fe25519_square_body] in Hexec_n.
    apply (square_inline_correct dest a_loc rs1 rs2 xa); assumption.
  Qed.

End Fe25519SquareCorrect.

(** Sanity check: list assumptions of the headline theorem.  Inside
    the Section, the [Variable] / [Hypothesis] parameters appear as
    parameters of the abstracted definition; once the Section closes
    they are universally quantified at the surface.  No new global
    axioms are introduced. *)
Print Assumptions fe25519_square_body_correct.
