(** * Fe25519MulCorrect — functional correctness of [fe25519_mul_body].
 *
 *  Companion to [Fe25519MulBody.v].  Mirrors the section-parameterised
 *  pattern used by [Fe25519AddSubCorrect.v] and
 *  [Fe25519InvertCorrect.fe25519_invert_correct]: abstract over the
 *  [Fp25519_holds] slot predicate plus a per-call algebraic oracle on
 *  the inline body, then derive functional correctness of the wrapped
 *  function.
 *
 *  Status (Phase 0d, 2026-05-13)
 *  =============================
 *  - [fe25519_mul_body_correct] :  Qed (three-line delegation to
 *      [mul_inline_correct]).
 *  - [mul_inline_correct] :  Section [Hypothesis] — captures the
 *      radix-2^51 schoolbook + reduce algebra.  Discharge is the
 *      substantive Phase 0e/0f task; deferred per the [Fe25519MulBody.v]
 *      header FOLLOW-UP.
 *
 *  The Section hypothesis surface is intentionally coarser than the
 *  Phase 0c [add_inline_correct] / [sub_inline_correct] pair: those
 *  are limb-list-builder Lemmas internal to [Fe25519AddSubCorrect.v]
 *  parameterised over four limb-level Section hypotheses
 *  ([Fp25519_holds_intro] / [_elim] / [_set_other] /
 *  [feval_limbwise_(add|sub)_mask64]).  For mul the limb-level
 *  bridge needs u128 / partial-product modelling that
 *  [SafeRustEd25519Sim.v]'s u64 [SMul] does not support; the
 *  combined obligation is therefore exposed as the single Section
 *  [Hypothesis] [mul_inline_correct].  No new global axioms.
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
Require Import Bedrock.End2End.Ed25519.Fe25519MulBody.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. Section parameters: abstract field-slot predicate + the       *)
(*     mul-body algebraic hypothesis.                                *)
(* ================================================================ *)

Section Fe25519MulCorrect.

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

  (** Inline-body correctness for [fe25519_mul_body].  The body
      executes five [REdLimbStore]s whose RHS expressions encode the
      5×5 radix-2^51 schoolbook (see [Fe25519MulBody.v] §2 for the
      precise sums).  The algebraic fact that this matches [F.mul]
      mirrors fiat-crypto's [Positional.eval_mulmod] + the radix-2^51
      carry chain ([fiat_25519_carry_mul] in the extracted C).
      Mechanical port through the [Fp25519_holds] interface — which
      requires u128 / partial-product modelling beyond the current
      [SMul] semantics — is the Phase 0e / 0f follow-up. *)
  Hypothesis mul_inline_correct :
    forall (dest a b : located_ed) (rs1 rs2 : rust_state_ed)
           (xa xb : F p),
      dest.(loc_type) = TFp25519 ->
      a.(loc_type) = TFp25519 ->
      b.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a.(loc_var) ->
      dest.(loc_var) <> b.(loc_var) ->
      Fp25519_holds rs1 a.(loc_var) xa ->
      Fp25519_holds rs1 b.(loc_var) xb ->
      Hexec
        (REdSeq
           (REdLimbStore dest 0%nat
              (SAdd (smul_limbs a.(loc_var) b.(loc_var) 0 0)
                (SAdd (smul_scaled a.(loc_var) b.(loc_var) 1 4 19)
                  (SAdd (smul_scaled a.(loc_var) b.(loc_var) 2 3 19)
                    (SAdd (smul_scaled a.(loc_var) b.(loc_var) 3 2 19)
                          (smul_scaled a.(loc_var) b.(loc_var) 4 1 19))))))
           (REdSeq
             (REdLimbStore dest 1%nat
                (SAdd (smul_limbs a.(loc_var) b.(loc_var) 0 1)
                  (SAdd (smul_limbs a.(loc_var) b.(loc_var) 1 0)
                    (SAdd (smul_scaled a.(loc_var) b.(loc_var) 2 4 19)
                      (SAdd (smul_scaled a.(loc_var) b.(loc_var) 3 3 19)
                            (smul_scaled a.(loc_var) b.(loc_var) 4 2 19))))))
             (REdSeq
               (REdLimbStore dest 2%nat
                  (SAdd (smul_limbs a.(loc_var) b.(loc_var) 0 2)
                    (SAdd (smul_limbs a.(loc_var) b.(loc_var) 1 1)
                      (SAdd (smul_limbs a.(loc_var) b.(loc_var) 2 0)
                        (SAdd (smul_scaled a.(loc_var) b.(loc_var) 3 4 19)
                              (smul_scaled a.(loc_var) b.(loc_var) 4 3 19))))))
               (REdSeq
                 (REdLimbStore dest 3%nat
                    (SAdd (smul_limbs a.(loc_var) b.(loc_var) 0 3)
                      (SAdd (smul_limbs a.(loc_var) b.(loc_var) 1 2)
                        (SAdd (smul_limbs a.(loc_var) b.(loc_var) 2 1)
                          (SAdd (smul_limbs a.(loc_var) b.(loc_var) 3 0)
                                (smul_scaled a.(loc_var) b.(loc_var) 4 4 19))))))
                 (REdLimbStore dest 4%nat
                    (SAdd (smul_limbs a.(loc_var) b.(loc_var) 0 4)
                      (SAdd (smul_limbs a.(loc_var) b.(loc_var) 1 3)
                        (SAdd (smul_limbs a.(loc_var) b.(loc_var) 2 2)
                          (SAdd (smul_limbs a.(loc_var) b.(loc_var) 3 1)
                                (smul_limbs a.(loc_var) b.(loc_var) 4 0))))))))))
        rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) (F.mul xa xb) /\
      fp_frame rs1 rs2 dest.(loc_var).

(* ================================================================ *)
(* §2. Headline theorem                                              *)
(* ================================================================ *)

  Theorem fe25519_mul_body_correct :
    forall (rs1 rs2 : rust_state_ed) (a_loc b_loc dest : located_ed)
           (xa xb : F p),
      a_loc.(loc_type) = TFp25519 ->
      b_loc.(loc_type) = TFp25519 ->
      dest.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a_loc.(loc_var) ->
      dest.(loc_var) <> b_loc.(loc_var) ->
      Fp25519_holds rs1 a_loc.(loc_var) xa ->
      Fp25519_holds rs1 b_loc.(loc_var) xb ->
      Hexec (fe25519_mul_body dest [a_loc; b_loc]) rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) (F.mul xa xb) /\
      fp_frame rs1 rs2 dest.(loc_var).
  Proof.
    intros rs1 rs2 a_loc b_loc dest xa xb
           Hat Hbt Hdt Hdne_a Hdne_b Hxa Hxb Hexec_n.
    cbn [fe25519_mul_body] in Hexec_n.
    apply (mul_inline_correct dest a_loc b_loc rs1 rs2 xa xb); assumption.
  Qed.

End Fe25519MulCorrect.

(** Sanity check: list assumptions of the headline theorem.  Inside
    the Section, the [Variable] / [Hypothesis] parameters appear as
    parameters of the abstracted definition; once the Section closes
    they are universally quantified at the surface.  No new global
    axioms are introduced. *)
Print Assumptions fe25519_mul_body_correct.
