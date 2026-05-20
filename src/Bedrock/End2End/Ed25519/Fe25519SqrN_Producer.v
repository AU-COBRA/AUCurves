(** * Fe25519SqrN_Producer — producer-side analog of [sqrN_correct].
 *
 *  [Fe25519InvertCorrect.sqrN_correct] is the CONSUMER side: given a
 *  full execution of [sqrN n acc scratch] from [rs1] to [rs2] and a
 *  starting witness [Fp25519_holds rs1 acc x], it proves the resulting
 *  [Fp25519_holds rs2 acc (F.pow x (2^n))] together with frame.
 *
 *  This file provides the PRODUCER side: given just the input witness
 *  [Fp25519_holds_bound rs1 acc x] and a name-disequation, it produces
 *  a fresh [rs2] together with an execution and the same final-state
 *  conclusion.
 *
 *  Construction: induct on [n], composing [rexec_for_zero] /
 *  [rexec_for_succ] with [sqr_producer_bound] / [copy_producer_bound]
 *  one iteration at a time.  Mirrors the proof of [sqrN_correct] step
 *  for step but in the existential direction.
 *
 *  Status: Qed, modulo the two acceptable-shortcut Admits inherited
 *  from [OracleLeafTemplate.v] via the per-leaf producers
 *  ([encode_target_decodes], [encode_target_bounded]).
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Spec.Curve25519.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.Fe25519InvertBody.
Require Import Bedrock.End2End.Ed25519.Fe25519InvertCorrect.
Require Import Bedrock.End2End.Ed25519.Fe25519InvertBoundInstantiation.
Require Import Bedrock.End2End.Ed25519.Fe25519BoundLeafProducers.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Local Notation Hexec_b :=
  (rust_exec_ed callee_post_bound callee_post_n_bound function_table_bound).

(** Producer for [sqrN n acc scratch]: given a starting state in which
    [acc] holds [x : F p], produce a successor state in which [acc]
    holds [x^(2^n)], together with the execution witness and a frame
    on all slots distinct from both [acc] and [scratch]. *)
Lemma sqrN_producer_bound :
  forall (n : nat) (acc scratch : String.string) (rs1 : rust_state_ed)
         (x : F p),
    acc <> scratch ->
    Fp25519_holds_bound rs1 acc x ->
    exists rs2 : rust_state_ed,
      Hexec_b (sqrN n acc scratch) rs1 rs2 /\
      Fp25519_holds_bound rs2 acc (F.pow x (N.pow 2 (N.of_nat n))) /\
      (forall y v,
          y <> acc ->
          y <> scratch ->
          Fp25519_holds_bound rs1 y v ->
          Fp25519_holds_bound rs2 y v).
Proof.
  intros n acc scratch rs1 x Hne Hacc.
  unfold sqrN.
  revert rs1 x Hacc.
  induction n as [|n IH]; intros rs1 x Hacc.
  - (* Base: REdFor _i 0 body — pick rs2 := rs1. *)
    exists rs1.
    split; [|split].
    + apply (rexec_for_zero callee_post_bound callee_post_n_bound
                            function_table_bound).
    + (* x^(2^0) = x^1 = x. *)
      cbn [N.of_nat N.pow Pos.iter Pos.of_nat].
      rewrite F.pow_1_r.
      exact Hacc.
    + intros y v _ _ Hy. exact Hy.
  - (* Step. *)
    (* Thread Hacc through the scalar-set [rs1 := rs_set_scalar_ed rs1 "_i" (Z.of_nat n)]. *)
    set (rs_aft := rs_set_scalar_ed rs1 "_i" (Z.of_nat n)).
    assert (Hacc_aft : Fp25519_holds_bound rs_aft acc x)
      by (unfold rs_aft;
          apply scalar_set_preserves_holds_bound; exact Hacc).
    (* Sqr: scratch := acc^2. *)
    pose proof (sqr_producer_bound rs_aft (LFp scratch) (LFp acc) x
                  (@eq_refl tower_type_ed TFp25519)
                  (@eq_refl tower_type_ed TFp25519)
                  (fun H => Hne (eq_sym H)) Hacc_aft) as Hprod_sqr.
    destruct Hprod_sqr as [rs_sqr [Hexec_sqr [Hscratch_v Hframe_sqr]]].
    cbn [LFp loc_var loc_type] in Hscratch_v, Hframe_sqr.
    (* acc unchanged through sqr. *)
    assert (Hacc_sqr : Fp25519_holds_bound rs_sqr acc x).
    { apply Hframe_sqr; [exact Hne | exact Hacc_aft]. }
    (* Copy: acc := scratch (= x^2). *)
    pose proof (copy_producer_bound rs_sqr (LFp acc) (LFp scratch) (F.pow x 2)
                  (@eq_refl tower_type_ed TFp25519)
                  (@eq_refl tower_type_ed TFp25519)
                  Hne Hscratch_v) as Hprod_copy.
    destruct Hprod_copy as [rs_cp [Hexec_cp [Hacc_v Hframe_cp]]].
    cbn [LFp loc_var loc_type] in Hacc_v, Hframe_cp.
    (* IH on rs_cp → rs2 with new value x^2. *)
    specialize (IH rs_cp (F.pow x 2) Hacc_v).
    destruct IH as [rs2 [Hexec_iter [Hacc_final Hframe_iter]]].
    exists rs2. split; [|split].
    + (* Compose into REdFor (S n). *)
      eapply (rexec_for_succ callee_post_bound callee_post_n_bound
                             function_table_bound).
      * (* body: REdSeq (sqr_call scratch acc) (copy_call acc scratch).
           Runs from rs_aft to rs_cp. *)
        eapply (rexec_seq callee_post_bound callee_post_n_bound
                          function_table_bound).
        -- unfold sqr_call. exact Hexec_sqr.
        -- unfold copy_call. exact Hexec_cp.
      * exact Hexec_iter.
    + (* (x^2)^(2^n) = x^(2^(S n)). *)
      replace ((F.pow x 2) ^ N.pow 2 (N.of_nat n))%F
         with (F.pow x (N.pow 2 (N.of_nat (S n)))) in Hacc_final.
      * exact Hacc_final.
      * rewrite F.pow_pow_l.
        f_equal.
        rewrite Nnat.Nat2N.inj_succ.
        rewrite N.pow_succ_r by lia.
        lia.
    + (* Frame: rs1 → rs_aft (scalar set) → rs_sqr (sqr, exclude scratch)
                 → rs_cp (copy, exclude acc) → rs2 (IH, exclude acc/scratch). *)
      intros y v Hne_acc Hne_scratch Hy.
      assert (Hy_aft : Fp25519_holds_bound rs_aft y v).
      { unfold rs_aft. apply scalar_set_preserves_holds_bound. exact Hy. }
      assert (Hy_sqr : Fp25519_holds_bound rs_sqr y v).
      { apply Hframe_sqr; [exact Hne_scratch | exact Hy_aft]. }
      assert (Hy_cp : Fp25519_holds_bound rs_cp y v).
      { apply Hframe_cp; [exact Hne_acc | exact Hy_sqr]. }
      apply Hframe_iter; [exact Hne_acc | exact Hne_scratch | exact Hy_cp].
Qed.

Print Assumptions sqrN_producer_bound.
