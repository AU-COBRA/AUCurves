(** * BLS12-381: the G1, G2 and GT theorems without leaf premises.

    [msm_bls12_closed], [g1_scalar_mul_closed] ([BLS12_MSM_Closed]), [g2_scalar_mul_closed]
    ([BLS12_G2_ScalarMul]) and [bls12_Fp12_pow_ok] ([BLS12_Fp12Pow]) take the bodies of the
    callees and the contracts of the field leaves as premises.  Here they are instantiated at
    [BLS12_ConcreteEnv.bls12_concrete_env], the environment of the functional pairing theorem
    extended by the group functions, where every premise is a lemma of [BLS12_ConcreteEnv]:

    - [msm_bls12_unconditional], [g1_scalar_mul_unconditional]: the conclusions of the closed
      G1 theorems for [bls12_concrete_env];
    - [g2_scalar_mul_unconditional]: the conclusion of [g2_scalar_mul_closed];
    - [bls12_Fp12_pow_unconditional]: [spec_of_bls12_Fp12_pow bls12_concrete_env];
    - [bls12_pairing_concrete]: [spec_of_bls12_pairing_functional bls12_concrete_env], from
      [bls12_pairing_functional_unconditional] and [bls12_concrete_extends] (a call in an
      environment is a call in every environment that extends it, [Semantics.extend_env_call]).

    The leaf bodies are the verified ones: fiat-crypto's [bls12_mul] / [bls12_add] /
    [bls12_sub] / [bls12_square] / [bls12_to_mont], [bls12_from_word] and [bls12_opp]
    ([BLS12_FpExtra]), the Fp2 tower functions ([BLS12_PairingLeavesFp2]), the Fp6/Fp12 tower
    of [BLS12_Pairing], the Fermat inverse ([BLS12_FpInvFermat]) and the constant stores
    [bls12_zero] / [bls12_one] of [ExtractBLS12GroupJasmin].  No Admitted, no Axiom. *)

Require Import Rupicola.Lib.Api.
From Stdlib Require Import ZArith List Lia.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Group.CurveAdd.PointDoubleA0.
Require Import Bedrock.Group.CurveAdd.RcbProjectiveLaws.
Require Import Bedrock.BLS12_MSM_Functional.
Require Import Bedrock.BLS12_MSM.
Require Import Bedrock.BLS12_MSM_Wrappers.
Require Import Bedrock.BLS12_G1ArenaRust.
Require Import Bedrock.BLS12_MSM_Closed.
Require Bedrock.Specs.AbstractField.
Require Bedrock.Specs.PrimeField.
Require Bedrock.Field.FieldExtensions.Compilation2_Fp2.
Require Bedrock.Field.Synthesis.Examples.bls12_Fp2.
Require Bedrock.Group.CurveAdd.RcbLawsAF.
Require Bedrock.BLS12_G2_ThreeB.
Require Bedrock.BLS12_G2_Closed.
Require Bedrock.BLS12_G2_ScalarMul.
Require Bedrock.Field.Synthesis.Examples.BLS12_CycExp.
Require Bedrock.Field.Synthesis.Examples.BLS12_Fp12Pow.
Require Bedrock.Field.Synthesis.Examples.BLS12_PairingFunctional.
Require Bedrock.Field.Synthesis.Examples.BLS12_PairingFunctionalLeaves.
Require Import Bedrock.BLS12_ConcreteEnv.
Import ListNotations.
Local Open Scope Z_scope.

Local Notation env := bls12_concrete_env.

(** ** G1 *)

Section G1.
  Existing Instances Bitwidth64.BW64 bls12_field_parameters bls12_frep
    bls12_field_parameters_ok bls12_frep_ok.

  Local Notation F := (F M_pos).
  Local Notation FElem := (Compilation2.FElem).
  Local Notation add_raw := (ladderstep_triple tb).

  Theorem msm_bls12_unconditional :
    forall (outx outy outz scalars_p ppx ppy ppz n_w : word)
           (outx0 outy0 outz0 : F) (scalars : list (list word))
           (px py pz : list F) (R : mem -> Prop) (tr : Semantics.trace) (m : mem),
      word.unsigned n_w = Z.of_nat (length scalars) ->
      length scalars = length px ->
      length px = length py ->
      length py = length pz ->
      Forall (fun s => length s = 4%nat) scalars ->
      Forall bls12_oncurve (points_of px py pz) ->
      (FElem None outx outx0 * FElem None outy outy0 * FElem None outz outz0
       * ScalarsArray scalars_p scalars
       * G1Array3 ppx ppy ppz px py pz * R)%sep m ->
      Semantics.call env "msm_bls12" tr m
        [outx; outy; outz; scalars_p; ppx; ppy; ppz; n_w]
        (fun tr' m' rets =>
           rets = [] /\ tr = tr' /\
           exists ox oy oz : F,
             pt_eq (ox, oy, oz)
                   (msm_sum (List.map scalar_value scalars) (points_of px py pz))
             /\ (FElem (Some tight_bounds) outx ox
                 * FElem (Some tight_bounds) outy oy
                 * FElem (Some tight_bounds) outz oz
                 * ScalarsArray scalars_p scalars
                 * G1Array3 ppx ppy ppz px py pz * R)%sep m').
  Proof.
    exact (msm_bls12_closed env cenv_msm_bls12 cenv_msm_curve_add cenv_msm_curve_double
             cenv_curve_add cenv_curve_double_a0 cenv_store_zero cenv_three_b
             cenv_g1_felem_copy cenv_spec_mul cenv_spec_add cenv_spec_sub
             cenv_spec_zero cenv_spec_one).
  Qed.

  Theorem g1_scalar_mul_unconditional :
    forall (outx outy outz sp px py pz : word) (outx0 outy0 outz0 X Y Z : F)
           (s : list word) (R : mem -> Prop) (tr : Semantics.trace) (m : mem),
      length s = 4%nat ->
      bls12_oncurve (X, Y, Z) ->
      (FElem None outx outx0 * FElem None outy outy0 * FElem None outz outz0
       * ScalarsArray sp [s]
       * FElem (Some tight_bounds) px X * FElem (Some tight_bounds) py Y
       * FElem (Some tight_bounds) pz Z * R)%sep m ->
      Semantics.call env "g1_scalar_mul" tr m [outx; outy; outz; sp; px; py; pz]
        (fun tr' m' rets =>
           rets = [] /\ tr = tr' /\
           exists ox oy oz : F,
             pt_eq (ox, oy, oz) (smul id_pt add_raw (scalar_value s) (X, Y, Z))
             /\ (FElem (Some tight_bounds) outx ox
                 * FElem (Some tight_bounds) outy oy
                 * FElem (Some tight_bounds) outz oz
                 * ScalarsArray sp [s]
                 * FElem (Some tight_bounds) px X * FElem (Some tight_bounds) py Y
                 * FElem (Some tight_bounds) pz Z * R)%sep m').
  Proof.
    exact (g1_scalar_mul_closed env cenv_g1_scalar_mul cenv_msm_curve_add cenv_msm_curve_double
             cenv_curve_add cenv_curve_double_a0 cenv_store_zero cenv_three_b
             cenv_g1_felem_copy cenv_spec_mul cenv_spec_add cenv_spec_sub
             cenv_spec_zero cenv_spec_one).
  Qed.
End G1.

(** ** G2 *)

Section G2.
  Existing Instances Bitwidth64.BW64
    Defaults64.default_parameters Defaults64.default_parameters_ok
    bls12_Fp2.bls12_prime_parameters bls12_Fp2.bls12_field_representation
    bls12_Fp2.bls12_Fp2_field_parameters bls12_Fp2.bls12_Fp2_field_representation
    bls12_Fp2.bls12_prime_parameters_ok bls12_Fp2.bls12_field_representation_ok.
  Existing Instance PrimeField.prime_field_parameters.

  Local Notation Fp := (F PrimeField.M_pos).
  Local Notation Fp2 := (Fp * Fp)%type.
  Local Notation AFElem := Compilation2_Fp2.AFElem.
  Local Notation cadd :=
    (@RcbLawsAF.cadd Fp2 bls12_Fp2.bls12_Fp2_field_parameters BLS12_G2_ThreeB.g2_tb).
  Local Notation pt_eq :=
    (@RcbLawsAF.pt_eq Fp2 bls12_Fp2.bls12_Fp2_field_parameters BLS12_G2_Closed.g2_dec).
  Local Notation id_pt := (@RcbLawsAF.id_pt Fp2 bls12_Fp2.bls12_Fp2_field_parameters).
  Local Notation tight :=
    (@AbstractField.tight_bounds Fp2 _ _ _ _ _ bls12_Fp2.bls12_Fp2_field_representation).
  Local Notation FElemT := (AFElem (Some tight)).

  Theorem g2_scalar_mul_unconditional :
    forall (outx outy outz sp px py pz : word) (ox0 oy0 oz0 X Y Z : Fp2)
           (s : list word) (R : mem -> Prop) (tr : Semantics.trace) (m : mem),
      length s = 4%nat ->
      BLS12_G2_Closed.g2_oncurve (X, Y, Z) ->
      (AFElem None outx ox0 * AFElem None outy oy0 * AFElem None outz oz0
       * BLS12_MSM.ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z * R)%sep m ->
      Semantics.call env "g2_scalar_mul" tr m [outx; outy; outz; sp; px; py; pz]
        (fun tr' m' rets =>
           rets = [] /\ tr = tr' /\
           exists ox oy oz : Fp2,
             pt_eq (ox, oy, oz) (smul id_pt cadd (BLS12_MSM_Closed.scalar_value s) (X, Y, Z))
             /\ (FElemT outx ox * FElemT outy oy * FElemT outz oz
                 * BLS12_MSM.ScalarsArray sp [s] * FElemT px X * FElemT py Y * FElemT pz Z
                 * R)%sep m').
  Proof.
    exact (BLS12_G2_ScalarMul.g2_scalar_mul_closed env cenv_g2_scalar_mul
             cenv_g2_curve_add_ip cenv_g2_curve_double_ip cenv_g2_three_b
             cenv_spec_Fp2_mul cenv_spec_Fp2_add cenv_spec_Fp2_sub).
  Qed.
End G2.

(** ** GT *)

Theorem bls12_Fp12_pow_unconditional : BLS12_Fp12Pow.spec_of_bls12_Fp12_pow env.
Proof.
  exact (BLS12_Fp12Pow.bls12_Fp12_pow_ok env cenv_Fp12_pow cenv_Fp12_mul_leaf
           cenv_Fp12_sqr_leaf cenv_Fp_from_word_leaf).
Qed.

(** ** The pairing, in the same environment *)

Theorem bls12_pairing_concrete :
  BLS12_PairingFunctional.spec_of_bls12_pairing_functional env.
Proof.
  pose proof BLS12_PairingFunctionalLeaves.bls12_pairing_functional_unconditional as H.
  cbv [BLS12_PairingFunctional.spec_of_bls12_pairing_functional] in H |- *.
  intros. eapply Semantics.extend_env_call; [ exact bls12_concrete_extends | ].
  eapply H; eassumption.
Qed.

Optimize Heap.
Print Assumptions msm_bls12_unconditional.
Optimize Heap.
Print Assumptions g1_scalar_mul_unconditional.
Optimize Heap.
Print Assumptions g2_scalar_mul_unconditional.
Optimize Heap.
Print Assumptions bls12_Fp12_pow_unconditional.
Optimize Heap.
Print Assumptions bls12_pairing_concrete.
