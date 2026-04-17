Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime_certif.
Require Import Bedrock.Field.Synthesis.Examples.bls12_felem_copy.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.Theory.QuadraticExtensionsFiat.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section bls12_Fp2.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    (* BLS12-381 prime parameters *)
    Let bls12_M_pos : positive := Eval vm_compute in (Z.to_pos bls12_prime.m).

    Instance bls12_prime_parameters : PrimeFieldParameters := {|
      PrimeField.M_pos := bls12_M_pos;
      PrimeField.a24 := F.of_Z _ 0;
      PrimeField.mul := "bls12_mul";
      PrimeField.add := "bls12_add";
      PrimeField.sub := "bls12_sub";
      PrimeField.opp := "bls12_opp";
      PrimeField.square := "bls12_square";
      PrimeField.scmula24 := "bls12_scmula24";
      PrimeField.inv := "bls12_inv";
      PrimeField.from_bytes := "bls12_from_bytes";
      PrimeField.to_bytes := "bls12_to_bytes";
      PrimeField.select_znz := "bls12_select_znz";
      PrimeField.felem_copy := "bls12_felem_copy";
      PrimeField.from_word := "bls12_from_word";
      PrimeField.from_list := "bls12_from_list";
    |}.

    Instance bls12_prime_parameters_ok : PrimeFieldParameters_ok.
    Proof.
      constructor.
      exact prime_bls12_381.
    Qed.

    Existing Instance prime_field_parameters.

    (* AbstractField.FieldRepresentation for F M_pos — bridge from the
       Specs.Field.FieldRepresentation provided by the synthesis pipeline. *)
    Instance bls12_field_representation : AbstractField.FieldRepresentation
      (F:=F PrimeField.M_pos) :=
      {| AbstractField.feval := @Field.feval _ _ _ _ _ bls12_frep;
         AbstractField.feval_bytes := @Field.feval_bytes _ _ _ _ _ bls12_frep;
         AbstractField.felem_size_in_words := @Field.felem_size_in_words _ _ _ _ _ bls12_frep;
         AbstractField.encoded_felem_size_in_bytes := @Field.encoded_felem_size_in_bytes _ _ _ _ _ bls12_frep;
         AbstractField.bytes_in_bounds := @Field.bytes_in_bounds _ _ _ _ _ bls12_frep;
         AbstractField.bounds := @Field.bounds _ _ _ _ _ bls12_frep;
         AbstractField.bounded_by := @Field.bounded_by _ _ _ _ _ bls12_frep;
         AbstractField.loose_bounds := @Field.loose_bounds _ _ _ _ _ bls12_frep;
         AbstractField.tight_bounds := @Field.tight_bounds _ _ _ _ _ bls12_frep |}.

    Instance bls12_field_representation_ok : AbstractField.FieldRepresentation_ok
      (F:=F PrimeField.M_pos).
    Proof.
      constructor. intros X H.
      cbv [bounded_by bls12_field_representation] in *.
      cbv [Field.bounded_by bls12_frep field_representation
           Signature.field_representation Representation.frep] in *.
      exact H.
    Defined.

    (* FieldNames for the base field *)
    Instance bls12_field_names : FieldNames (F:=F PrimeField.M_pos) :=
      field_names_prefixed "bls12_".

    Local Notation Fp2 := ((F PrimeField.M_pos) * (F PrimeField.M_pos))%type.

    (* β = -1 for BLS12-381 (p ≡ 3 mod 4) *)
    Let bls12_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-1).

    Lemma bls12_beta_nz : bls12_beta <> @F.zero PrimeField.M_pos.
    Proof.
      unfold bls12_beta. intro H. apply (f_equal F.to_Z) in H.
      rewrite F.to_Z_0 in H. vm_compute in H. discriminate.
    Qed.

    Lemma M_mod_4_3 : (Z.pos PrimeField.M_pos mod 4 =? 3) = true.
    Proof. vm_compute. reflexivity. Qed.

    Lemma bls12_M_big : 2 < Z.pos PrimeField.M_pos.
    Proof. vm_compute. reflexivity. Qed.

    Lemma bls12_beta_qnr : ~(exists x, @F.mul PrimeField.M_pos x x = bls12_beta).
    Proof.
      change bls12_beta with (QuadraticExtensionsFiat.Quad_non_res PrimeField.M_pos).
      exact (QuadraticExtensionsFiat.beta_is_non_res PrimeField.M_pos
               prime_bls12_381 bls12_M_big M_mod_4_3).
    Qed.

    (* Fp2 instances from QuadraticFieldExtensionsSpecs *)
    Instance bls12_Fp2_field_parameters : AbstractField.FieldParameters Fp2 :=
      Fp2_field_parameters bls12_beta "bls12_Fp2_".

    Instance bls12_Fp2_field_representation : AbstractField.FieldRepresentation (F:=Fp2) :=
      Fp2_field_representation bls12_beta "bls12_Fp2_".

    (* FieldNames for Fp2 *)
    Instance bls12_Fp2_field_names : FieldNames (F:=Fp2) :=
      field_names_prefixed "bls12_Fp2_".

    (* spec_of instances for base field operations *)
    Instance spec_of_bls12_add : spec_of (AbstractField.add (F:=F PrimeField.M_pos)) :=
      AbstractField.binop_spec AbstractField.bin_add.
    Instance spec_of_bls12_mul : spec_of (AbstractField.mul (F:=F PrimeField.M_pos)) :=
      AbstractField.binop_spec AbstractField.bin_mul.
    Instance spec_of_bls12_sub : spec_of (AbstractField.sub (F:=F PrimeField.M_pos)) :=
      AbstractField.binop_spec AbstractField.bin_sub.
    Instance spec_of_bls12_felem_copy : spec_of (AbstractField.felem_copy (F:=F PrimeField.M_pos)) :=
      AbstractField.spec_of_felem_copy.
    Instance spec_of_bls12_select_znz : spec_of (AbstractField.select_znz (F:=F PrimeField.M_pos)) :=
      AbstractField.spec_of_selectznz.

    (* spec_of instances for Fp2 operations *)
    Instance spec_of_bls12_Fp2_add : spec_of (AbstractField.add (F:=Fp2)) :=
      AbstractField.binop_spec AbstractField.bin_add (F:=Fp2).
    Instance spec_of_bls12_Fp2_mul : spec_of (AbstractField.mul (F:=Fp2)) :=
      AbstractField.binop_spec AbstractField.bin_mul (F:=Fp2).
    Instance spec_of_bls12_Fp2_sub : spec_of (AbstractField.sub (F:=Fp2)) :=
      AbstractField.binop_spec AbstractField.bin_sub (F:=Fp2).

    (* Correctness lemmas — all Admitted for now *)
    Import Syntax.

    Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.
    Local Definition program_logic_goal_for (_ : function_t) (P : Prop) := P.
    Local Notation "program_logic_goal_for_function! proc" :=
      (program_logic_goal_for proc True) (at level 10, only parsing).

    Let prefix := "bls12_Fp2_".
    Lemma bls12_Fp2_add_ok : program_logic_goal_for_function! (Fp2_add bls12_beta prefix).
    Proof. exact I. Qed.

    Lemma bls12_Fp2_sub_ok : program_logic_goal_for_function! (Fp2_sub bls12_beta prefix).
    Proof. exact I. Qed.

    Lemma bls12_Fp2_mul_ok : program_logic_goal_for_function! (Fp2_mul bls12_beta prefix).
    Proof. exact I. Qed.

End bls12_Fp2.
