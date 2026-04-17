(** * BLS12-377 GLV Shamir scalar multiplication.

    Proves the GLV main theorem for BLS12-377 parameters:
      [k]P = [k1]P + [k2]phi(P)
    where (k1, k2) = glv_decompose_377(k), with 128 iterations.

    Reuses the generic shamir_mult and its correctness proof
    from BLS12_GLV_ScalarMult.v. *)

From Stdlib Require Import ZArith Lia.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.Group.
Require Import Crypto.Algebra.Monoid.
Require Import Crypto.Algebra.ScalarMult.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_377_ScalarReduce.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_377_GLV_Decompose.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_GLV_ScalarMult.
Local Open Scope Z_scope.

Section GLV377.
  Context {G eq add zero opp} `{groupG : @group G eq add zero opp}.
  Context {mul : Z -> G -> G} `{mul_is_sm : @is_scalarmult G eq add zero opp mul}.
  Context {add_comm : @is_commutative G eq add}.
  Local Infix "=" := eq : type_scope.
  Local Infix "+" := add.
  Local Infix "*" := mul.

  Context {phi : G -> G}.
  Context {phi_hom : @Monoid.is_homomorphism G eq add G eq add phi}.

  (** GLV main theorem for BLS12-377: 128 iterations *)
  Theorem glv377_scalarmult_correct : forall k P,
    0 <= k < bls377_r ->
    bls377_r * P = zero ->
    bls377_lambda * P = phi P ->
    let '(k1, k2) := glv_decompose_377 k in
    @shamir_mult G add mul 128 k1 k2 P (phi P) zero = k * P.
  Proof.
    intros k P0 Hk Horder Hphi.
    unfold glv_decompose_377.
    set (k1 := k mod bls377_lambda).
    set (k2 := k / bls377_lambda).
    pose proof (glv_decompose_377_correct k ltac:(lia)) as Hdecomp.
    unfold glv_decompose_377 in Hdecomp. fold k1 k2 in Hdecomp.
    pose proof (glv377_k1_bound k ltac:(lia)) as Hk1.
    unfold glv_decompose_377 in Hk1. fold k1 in Hk1.
    pose proof (glv377_k2_bound k Hk) as Hk2.
    unfold glv_decompose_377 in Hk2. fold k2 in Hk2.
    pose proof bls377_lambda_127bits as Hlam127.
    assert (Hk1_128 : 0 <= k1 < 2 ^ 128) by lia.
    assert (Hk2_128 : 0 <= k2 < 2 ^ 128) by lia.
    rewrite (@shamir_mult_correct G eq add zero opp groupG mul mul_is_sm add_comm)
      by (change (Z.of_nat 128) with 128; lia).
    rewrite <- Hphi.
    rewrite scalarmult_assoc.
    rewrite <- scalarmult_add_l.
    replace (k1 + bls377_lambda * k2)%Z with k by lia.
    reflexivity.
  Qed.

End GLV377.
