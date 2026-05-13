(** * Fe25519Scmula24Correct — functional correctness of
 *  [fe25519_scmula24_body].
 *
 *  Companion to [Fe25519Scmula24Body.v].  Mirrors the
 *  section-parameterised pattern used by [Fe25519CarryCorrect] /
 *  [Fe25519AddSubCorrect]: abstract over the [Fp25519_holds] slot
 *  predicate plus a single per-call oracle hypothesis
 *  [scmula24_inline_correct] on the body, then derive algebraic
 *  correctness of the wrapped function ([F.eq (F.mul a24 xa)
 *  (feval dest)], i.e. the post-state's [dest] holds the
 *  pre-state's [a]-value scaled by the curve constant [a24 =
 *  121665]).
 *
 *  Status (Phase 0c, 2026-05-13)
 *  =============================
 *  - [fe25519_scmula24_body_correct] : Qed via the
 *    [scmula24_inline_correct] Section hypothesis (scaffold).
 *    Three-line delegation, same shape as Phase 0c carry/add proofs.
 *  - Discharging [scmula24_inline_correct] mechanically is the
 *    Phase 0d follow-up: peel the 17 [REdLimbStore]s through
 *    [rexec_limb_store_inv] (5 multiply inversions, then 12 carry
 *    inversions identical to [fe25519_carry]), track the limb-list
 *    state, then close by invoking fiat-crypto's
 *    [UnsaturatedSolinas.carry_scmul_const_correct] at the chosen
 *    radix-2^51 parameters / [a24 = 121665].  Estimated ~500 LoC
 *    (linear in the 17 stores, vs ~400 LoC for the 12-store carry
 *    chain in [Fe25519CarryCorrect]).
 *
 *  History
 *  =======
 *  Phase 0c (this file): scaffold with single
 *    [scmula24_inline_correct] section hypothesis.  No global
 *    axioms.  Acceptable partial per Phase 0c plan: body +
 *    correctness statement + hypothesis is "success" with full
 *    discharge as bonus.
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
Require Import Bedrock.End2End.Ed25519.Fe25519Scmula24Body.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. Section parameters: abstract field-slot predicate + scmula24- *)
(*     inline oracle.                                                *)
(* ================================================================ *)

Section Fe25519Scmula24Correct.

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

  (** The scalar constant [a24] in [F p], as an [F]-element.  Equals
      [F.of_Z _ 121665] (this is the literal value of [(A - 2) / 4]
      in [F p] where [A = 486662]). *)
  Definition fe25519_a24 : F p := F.of_Z _ fe25519_a24_z.

  (** Scmula24-inline oracle.  Mirrors [carry_inline_correct] in
      [Fe25519CarryCorrect.v] but with the post-state value
      [F.mul fe25519_a24 xa] instead of [xa].

      Phase 0c keeps this as a single section [Hypothesis]; Phase 0d
      replaces it with a mechanical proof factored through
      fiat-crypto's [carry_scmul_const_correct] +
      [Positional.eval_carry_scmul_const].  Both halves of the
      conjunction (post-value + frame) are needed at downstream
      composition sites. *)
  Hypothesis scmula24_inline_correct :
    forall (dest a : located_ed) (rs1 rs2 : rust_state_ed) (xa : F p),
      dest.(loc_type) = TFp25519 ->
      a.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a.(loc_var) ->
      Fp25519_holds rs1 a.(loc_var) xa ->
      Hexec
        (* ---- Phase A: 5 limbwise multiplies ---- *)
        (REdSeq
          (REdLimbStore dest 0%nat (sScmulA24 a.(loc_var) 0%nat))
        (REdSeq
          (REdLimbStore dest 1%nat (sScmulA24 a.(loc_var) 1%nat))
        (REdSeq
          (REdLimbStore dest 2%nat (sScmulA24 a.(loc_var) 2%nat))
        (REdSeq
          (REdLimbStore dest 3%nat (sScmulA24 a.(loc_var) 3%nat))
        (REdSeq
          (REdLimbStore dest 4%nat (sScmulA24 a.(loc_var) 4%nat))
        (* ---- Phase B: 12-store carry chain ---- *)
        (REdSeq
          (REdLimbStore dest 1%nat
             (SAdd (SLimb dest.(loc_var) 1%nat)
                   (sShr51 (SLimb dest.(loc_var) 0%nat))))
        (REdSeq
          (REdLimbStore dest 0%nat (sMask51 (SLimb dest.(loc_var) 0%nat)))
        (REdSeq
          (REdLimbStore dest 2%nat
             (SAdd (SLimb dest.(loc_var) 2%nat)
                   (sShr51 (SLimb dest.(loc_var) 1%nat))))
        (REdSeq
          (REdLimbStore dest 1%nat (sMask51 (SLimb dest.(loc_var) 1%nat)))
        (REdSeq
          (REdLimbStore dest 3%nat
             (SAdd (SLimb dest.(loc_var) 3%nat)
                   (sShr51 (SLimb dest.(loc_var) 2%nat))))
        (REdSeq
          (REdLimbStore dest 2%nat (sMask51 (SLimb dest.(loc_var) 2%nat)))
        (REdSeq
          (REdLimbStore dest 4%nat
             (SAdd (SLimb dest.(loc_var) 4%nat)
                   (sShr51 (SLimb dest.(loc_var) 3%nat))))
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
             (SAdd (SLimb dest.(loc_var) 1%nat)
                   (sShr51 (SLimb dest.(loc_var) 0%nat))))
          (REdLimbStore dest 0%nat (sMask51 (SLimb dest.(loc_var) 0%nat)))
        )))))))))))))))) rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) (F.mul fe25519_a24 xa) /\
      fp_frame rs1 rs2 dest.(loc_var).

(* ================================================================ *)
(* §2. Headline theorem                                              *)
(* ================================================================ *)

  Theorem fe25519_scmula24_body_correct :
    forall (rs1 rs2 : rust_state_ed) (a_loc dest : located_ed) (xa : F p),
      a_loc.(loc_type) = TFp25519 ->
      dest.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a_loc.(loc_var) ->
      Fp25519_holds rs1 a_loc.(loc_var) xa ->
      Hexec (fe25519_scmula24_body dest [a_loc]) rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) (F.mul fe25519_a24 xa) /\
      fp_frame rs1 rs2 dest.(loc_var).
  Proof.
    intros rs1 rs2 a_loc dest xa Hat Hdt Hdne Hxa Hexec_n.
    cbn [fe25519_scmula24_body] in Hexec_n.
    apply (scmula24_inline_correct dest a_loc rs1 rs2 xa); assumption.
  Qed.

End Fe25519Scmula24Correct.

(** Sanity check: list assumptions of the headline theorem.  Inside
    the Section, the [Variable]/[Hypothesis] parameters appear as
    parameters of the abstracted definition; once the Section closes
    they are universally quantified at the surface.  No new global
    axioms are introduced. *)
Print Assumptions fe25519_scmula24_body_correct.
