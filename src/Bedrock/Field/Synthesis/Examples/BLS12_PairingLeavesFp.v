(** * BLS12-381: the base-field leaf specs of the functional pairing theorem, from fiat-crypto.

    The AbstractField specs of [bls12_mul], [bls12_add], [bls12_sub], [bls12_square],
    [bls12_felem_copy] (functions of the extraction's list) and of [bls12_opp],
    [bls12_from_word] ([BLS12_FpExtra]) hold by the fiat-crypto correctness lemmas and the
    bridge lemmas of [FiatAbstractFieldBridge].  They are stated at the instances of
    [BLS12_MillerStepFunctional] (MS) and, for the leaves used by the final exponentiation, of
    [BLS12_CycExp] (CE).
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Crypto.Bedrock.Specs.Field.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_felem_copy.
Require Import Bedrock.Field.Synthesis.Examples.FiatAbstractFieldBridge.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_FpExtra.
Require Bedrock.Field.Synthesis.Examples.BLS12_MillerStepFunctional.
Require Bedrock.Field.Synthesis.Examples.BLS12_CycExp.
Module MS := Bedrock.Field.Synthesis.Examples.BLS12_MillerStepFunctional.
Module CE := Bedrock.Field.Synthesis.Examples.BLS12_CycExp.

Local Open Scope string_scope.

Existing Instances
  Defaults64.default_parameters
  Defaults64.default_parameters_ok.

Local Notation env := (Interface.map.rep (map:=Semantics.env)).

Lemma bls12_Fp_mul_leaf (functions : env) :
  map.get functions "bls12_mul" = Some (snd bls12_mul) ->
  MS.spec_of_Fp_mul functions.
Proof.
  intros E.
  exact (binop_spec_of_fiat (frep:=bls12_frep) (frep_ok:=bls12_frep_ok)
           (aparams:=@prime_field_parameters MS.bls12_pf_params)
           Field.bin_mul AbstractField.bin_mul functions
           eq_refl (fun _ _ => eq_refl) eq_refl eq_refl eq_refl
           (bls12_mul_correct functions E)).
Qed.

Lemma bls12_Fp_add_leaf (functions : env) :
  map.get functions "bls12_add" = Some (snd bls12_add) ->
  CE.spec_of_Fp_add functions.
Proof.
  intros E.
  exact (binop_spec_of_fiat (frep:=bls12_frep) (frep_ok:=bls12_frep_ok)
           (aparams:=@prime_field_parameters CE.bls12_pf_params)
           Field.bin_add AbstractField.bin_add functions
           eq_refl (fun _ _ => eq_refl) eq_refl eq_refl eq_refl
           (bls12_add_correct functions E)).
Qed.

Lemma bls12_Fp_felem_copy_leaf (functions : env) :
  map.get functions "bls12_felem_copy" = Some bls12_felem_copy ->
  MS.spec_of_Fp_felem_copy functions.
Proof.
  intros E.
  exact (felem_copy_spec_of_fiat (frep:=bls12_frep) (frep_ok:=bls12_frep_ok)
           (aparams:=@prime_field_parameters MS.bls12_pf_params) functions eq_refl
           (felem_copy_ok functions E)).
Qed.

Lemma bls12_Fp_from_word_leaf_MS (functions : env) :
  map.get functions "bls12_from_word" = Some (snd bls12_from_word) ->
  map.get functions "bls12_to_mont" = Some (snd bls12_to_mont) ->
  MS.spec_of_Fp_from_word functions.
Proof.
  intros E1 E2.
  exact (from_word_spec_of_fiat (frep:=bls12_frep) (frep_ok:=bls12_frep_ok)
           (aparams:=@prime_field_parameters MS.bls12_pf_params) "bls12_from_word" functions
           eq_refl (bls12_from_word_correct functions E1 E2)).
Qed.

Lemma bls12_Fp_from_word_leaf_CE (functions : env) :
  map.get functions "bls12_from_word" = Some (snd bls12_from_word) ->
  map.get functions "bls12_to_mont" = Some (snd bls12_to_mont) ->
  CE.spec_of_Fp_from_word functions.
Proof.
  intros E1 E2.
  exact (from_word_spec_of_fiat (frep:=bls12_frep) (frep_ok:=bls12_frep_ok)
           (aparams:=@prime_field_parameters CE.bls12_pf_params) "bls12_from_word" functions
           eq_refl (bls12_from_word_correct functions E1 E2)).
Qed.

(** The remaining fiat-crypto base-field functions, at the instances of
    [BLS12_MillerStepFunctional] (the specs of the tower library at these instances are the
    same terms). *)
Lemma bls12_Fp_sub_leaf (functions : env) :
  map.get functions "bls12_sub" = Some (snd bls12_sub) ->
  AbstractField.binop_spec (F:=F (@PrimeField.M_pos MS.bls12_pf_params))
    (field_representation:=MS.bls12_Fp_rep) AbstractField.bin_sub functions.
Proof.
  intros E.
  exact (binop_spec_of_fiat (frep:=bls12_frep) (frep_ok:=bls12_frep_ok)
           (aparams:=@prime_field_parameters MS.bls12_pf_params)
           Field.bin_sub AbstractField.bin_sub functions
           eq_refl (fun _ _ => eq_refl) eq_refl eq_refl eq_refl
           (bls12_sub_correct functions E)).
Qed.

Lemma bls12_Fp_add_leaf_MS (functions : env) :
  map.get functions "bls12_add" = Some (snd bls12_add) ->
  AbstractField.binop_spec (F:=F (@PrimeField.M_pos MS.bls12_pf_params))
    (field_representation:=MS.bls12_Fp_rep) AbstractField.bin_add functions.
Proof. exact (bls12_Fp_add_leaf functions). Qed.

Lemma bls12_Fp_opp_leaf (functions : env) :
  map.get functions "bls12_opp" = Some (snd bls12_opp) ->
  AbstractField.unop_spec (F:=F (@PrimeField.M_pos MS.bls12_pf_params))
    (field_representation:=MS.bls12_Fp_rep) AbstractField.un_opp functions.
Proof.
  intros E.
  exact (unop_spec_of_fiat (frep:=bls12_frep) (frep_ok:=bls12_frep_ok)
           (aparams:=@prime_field_parameters MS.bls12_pf_params)
           Field.un_opp AbstractField.un_opp functions
           eq_refl (fun _ => eq_refl) eq_refl eq_refl
           (bls12_opp_correct functions E)).
Qed.

Lemma bls12_Fp_square_leaf (functions : env) :
  map.get functions "bls12_square" = Some (snd bls12_square) ->
  AbstractField.unop_spec (F:=F (@PrimeField.M_pos MS.bls12_pf_params))
    (field_representation:=MS.bls12_Fp_rep) AbstractField.un_square functions.
Proof.
  intros E.
  refine (unop_spec_of_fiat (frep:=bls12_frep) (frep_ok:=bls12_frep_ok)
           (aparams:=@prime_field_parameters MS.bls12_pf_params)
           Field.un_square AbstractField.un_square functions
           eq_refl _ eq_refl eq_refl
           (bls12_square_correct functions E)).
  intros a. cbn [AbstractField.un_model AbstractField.un_square Field.un_model Field.un_square].
  cbv [AbstractField.Fsquare AbstractField.Fmul prime_field_parameters].
  rewrite F.pow_2_r. reflexivity.
Qed.
