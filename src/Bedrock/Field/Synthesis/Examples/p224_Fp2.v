Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Bedrock.Field.Synthesis.Examples.p224_64_new.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Coq.Strings.String.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.


Section p224_Fp2.

    Existing Instances Defaults32.default_parameters Defaults32.default_parameters_ok.

    Existing Instance field_parameters.

    Definition p224_Fp2_add := (@Fp2_add _ _ _ _ p224_64_new.field_parameters (field_representation_raw m) (snd p224_sub) (snd p224_sub)).


    Require Import bedrock2.NotationsCustomEntry.
    Require Import bedrock2.WeakestPrecondition.
    Import Syntax BinInt String List.ListNotations.
    Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
    Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
    Require Import Rupicola.Lib.Api.
    Require Import Bedrock.Specs.AbstractField.
    Require Import Bedrock.Specs.PrimeField.
    Require Import Bedrock.Field.FieldExtensions.Theory.QuadraticExtensions.
    Require Import Crypto.Bedrock.Field.Interface.Compilation2.


Instance spec_of_p224_Fp2_add : spec_of (fst p224_Fp2_add).
Proof.
    exact (@spec_of_Fp2_add _ _ _ _ _ _ p224_64_new.field_parameters (field_representation_raw m)).
Defined.

Instance spec_of_p224_felem_copy : spec_of (fst p224_felem_copy).

  Lemma p224_Fp2_add_ok : program_logic_goal_for_function! p224_Fp2_add.
  


    From bedrock2 Require Import ToCString Bytedump.
    Definition c_mod := (c_module (p224_Fp2_add :: nil)).

    Eval cbv in c_mod.
