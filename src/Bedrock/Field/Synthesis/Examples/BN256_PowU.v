(** * BN256 Power-by-u -- thin instantiation of BLS12_PowGeneric.
    Computes f^{u} where u = 0x5A76AE9AEC588301 (63 bits).
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Bedrock.Field.Synthesis.Examples.bn256_prime.
Require Import Bedrock.Field.Synthesis.Examples.bn256_prime_certif.
Require Import Bedrock.Field.Synthesis.Examples.bn256_felem_copy.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.PairingFieldOps.
Require Import Bedrock.Field.FieldExtensions.WPTactics.
Require Import Bedrock.Field.Synthesis.Examples.BN256_Pairing.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_CurveInstances.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PowGeneric.
Require Import bedrock2.Loops.
Require Import bedrock2.SepCalls.
Require Import coqutil.Z.Lia.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section BN256_PowU.

    (* === BN256 Fp-level setup === *)
    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    Let bn256_M_pos : positive := Eval vm_compute in (Z.to_pos bn256_prime.m).

    Instance bn256_pf_params : PrimeFieldParameters := {|
      PrimeField.M_pos := bn256_M_pos;
      PrimeField.a24 := F.of_Z _ 0;
      PrimeField.mul := "bn256_mul"; PrimeField.add := "bn256_add";
      PrimeField.sub := "bn256_sub"; PrimeField.opp := "bn256_opp";
      PrimeField.square := "bn256_square"; PrimeField.scmula24 := "bn256_scmula24";
      PrimeField.inv := "bn256_inv"; PrimeField.from_bytes := "bn256_from_bytes";
      PrimeField.to_bytes := "bn256_to_bytes"; PrimeField.select_znz := "bn256_select_znz";
      PrimeField.felem_copy := "bn256_felem_copy"; PrimeField.from_word := "bn256_from_word";
      PrimeField.from_list := "bn256_from_list";
    |}.

    Instance bn256_pf_params_ok : PrimeFieldParameters_ok.
    Proof. constructor. exact prime_bn256. Qed.

    Existing Instance prime_field_parameters.

    Local Notation Fp := (F PrimeField.M_pos).
    Local Notation Fp2 := ((Fp * Fp)%type).
    Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
    Local Notation Fp12 := ((Fp6 * Fp6)%type).

    Instance bn256_Fp_rep : AbstractField.FieldRepresentation (F:=Fp) :=
      {| AbstractField.feval := @Field.feval _ _ _ _ _ bn256_frep;
         AbstractField.feval_bytes := @Field.feval_bytes _ _ _ _ _ bn256_frep;
         AbstractField.felem_size_in_words := @Field.felem_size_in_words _ _ _ _ _ bn256_frep;
         AbstractField.encoded_felem_size_in_bytes := @Field.encoded_felem_size_in_bytes _ _ _ _ _ bn256_frep;
         AbstractField.bytes_in_bounds := @Field.bytes_in_bounds _ _ _ _ _ bn256_frep;
         AbstractField.bounds := @Field.bounds _ _ _ _ _ bn256_frep;
         AbstractField.bounded_by := @Field.bounded_by _ _ _ _ _ bn256_frep;
         AbstractField.loose_bounds := @Field.loose_bounds _ _ _ _ _ bn256_frep;
         AbstractField.tight_bounds := @Field.tight_bounds _ _ _ _ _ bn256_frep |}.

    Instance bn256_Fp_rep_ok : AbstractField.FieldRepresentation_ok (F:=Fp).
    Proof.
      constructor. intros X H.
      cbv [bounded_by bn256_Fp_rep] in *.
      cbv [Field.bounded_by bn256_frep field_representation
           Signature.field_representation Representation.frep] in *.
      exact H.
    Defined.

    (* === Extension field constants === *)
    Let bn256_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-1).
    Let bn256_xi_re : F PrimeField.M_pos := F.of_Z PrimeField.M_pos 3.
    Let bn256_xi_im : F PrimeField.M_pos := @F.one PrimeField.M_pos.

    (* Extension field instances matching BLS12_PowGeneric *)
    Instance bn256_Fp12_params' : AbstractField.FieldParameters Fp12 :=
      ext_Fp12_params bn256_beta bn256_xi_re bn256_xi_im "bn256_".
    Instance bn256_Fp12_rep' : AbstractField.FieldRepresentation (F:=Fp12) :=
      ext_Fp12_rep bn256_beta bn256_xi_re bn256_xi_im "bn256_".

    Local Notation FElem_Fp12 := (@AbstractField.FElem _ bn256_Fp12_params' _ _ _ _ bn256_Fp12_rep').
    Local Notation Fp12_bounded := (@AbstractField.bounded_by _ bn256_Fp12_params' _ _ _ _ bn256_Fp12_rep').
    Local Notation Fp12_tight := (@AbstractField.tight_bounds _ bn256_Fp12_params' _ _ _ _ bn256_Fp12_rep').
    Local Notation Fp12_loose := (@AbstractField.loose_bounds _ bn256_Fp12_params' _ _ _ _ bn256_Fp12_rep').
    Local Notation Fp12_felem := (@AbstractField.felem _ bn256_Fp12_params' _ _ _ _ bn256_Fp12_rep').

    Instance spec_of_Fp12_sqr : spec_of (AbstractField.square (F:=Fp12)) :=
      AbstractField.unop_spec (F:=Fp12) (field_representation:=bn256_Fp12_rep') AbstractField.un_square.
    Instance spec_of_Fp12_mul : spec_of (AbstractField.mul (F:=Fp12)) :=
      AbstractField.binop_spec (F:=Fp12) (field_representation:=bn256_Fp12_rep') AbstractField.bin_mul.
    Instance spec_of_Fp12_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp12)) :=
      AbstractField.spec_of_felem_copy (F:=Fp12) (field_representation:=bn256_Fp12_rep').

    (* Spec for bn256_Fp12_pow_u: computes base^{u} *)
    Instance spec_of_pow_u : spec_of "bn256_Fp12_pow_u" :=
      fnspec! "bn256_Fp12_pow_u" (pout pbase : word)
        / (old_out base_val : Fp12_felem) Rr,
      { requires tr mem :=
          Fp12_bounded Fp12_tight base_val /\
          (FElem_Fp12 pbase base_val ⋆
           (FElem_Fp12 pout old_out ⋆ Rr)) mem;
        ensures tr' mem' :=
          tr = tr' /\ exists out,
            Fp12_bounded Fp12_loose out /\
            (FElem_Fp12 pout out ⋆
             (FElem_Fp12 pbase base_val ⋆ Rr)) mem' }.

    Lemma bn256_Fp12_pow_u_ok :
      forall functions
        (EnvContains : map.get functions "bn256_Fp12_pow_u" =
          Some (snd BN256_Pairing.bn256_Fp12_pow_u))
        (HFsqr : spec_of_Fp12_sqr functions)
        (HFmul : spec_of_Fp12_mul functions)
        (HFcopy : spec_of_Fp12_felem_copy functions),
      spec_of_pow_u functions.
    Proof.
      intros.
      eapply (@pow_ok bn256_pf_params bn256_Fp_rep bn256_Fp_rep_ok
                bn256_beta bn256_xi_re bn256_xi_im "bn256_"
                "bn256_Fp12_pow_u" 0x5A76AE9AEC588301 62
                ltac:(lia)); eassumption.
    Qed.

End BN256_PowU.
