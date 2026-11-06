(** * BLS12-381: the Fp12 mul leaf specs of the functional pairing theorem.

    The tower library's [DodecicFieldExtensionsMul.Fp12_mul_ok] and
    [CubicFieldExtensions.Fp6_{sub,sqr,inv}_ok], instantiated as in [BLS12_PairingLeavesTower],
    with the Fp2 specs of [BLS12_PairingLeavesFp2] and the in-place spec of
    [BLS12_Pairing.bls12_Fp2_mul_xi] of [BLS12_PairingLeavesTower].
    The Fp6 square and inverse specs are proved here for the Fp12 square and inverse, whose
    library lemmas ([DodecicFieldExtensionsSqr.Fp12_sqr_ok], [DodecicFieldExtensionsInv.Fp12_inv_ok])
    state the Fp6 square spec with the model [Fmul x x] instead of [fp6_sqr]; that bridge is
    in [BLS12_PairingLeavesFp12SqrInv].
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensions.
Require Bedrock.Field.FieldExtensions.DodecicFieldExtensionsMul.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingFunctionalEnv.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingLeavesFp2.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingLeavesTower.
Require Bedrock.Field.Synthesis.Examples.BLS12_Fp2InvBridge.
Require Theory.BLS12Pairing.Pairing.
Require Bedrock.Field.Synthesis.Examples.BLS12_MillerStepFunctional.
Require Bedrock.Field.Synthesis.Examples.BLS12_FinalExp.
Module MS := Bedrock.Field.Synthesis.Examples.BLS12_MillerStepFunctional.
Module FE := Bedrock.Field.Synthesis.Examples.BLS12_FinalExp.
Module DM := Bedrock.Field.FieldExtensions.DodecicFieldExtensionsMul.

Import List.ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

Existing Instances
  Bitwidth64.BW64
  Defaults64.default_parameters
  Defaults64.default_parameters_ok.

Local Notation function_t := (String.string * Syntax.func)%type.
Local Notation Fp := (F (@PrimeField.M_pos MS.bls12_pf_params)).
Local Notation pp := MS.bls12_pf_params.
Local Notation frep := MS.bls12_Fp_rep.

Add Ring bls12_Fp_ring_fp12 : (@F.ring_theory (@PrimeField.M_pos pp)).

Lemma bls12_invp2_eq_fp6_fp2_inv : forall x : Fp * Fp,
  QuadraticExtensions.invp2 _ bls12_beta x =
  CubicFieldExtensionsSpecs.BLS12Fp6Spec.fp2_inv _ bls12_beta x.
Proof.
  intros x.
  transitivity (Pairing.fp2_inv (@PrimeField.M_pos pp) x);
    [ exact (BLS12_Fp2InvBridge.bls12_381_invp2_eq_fp2_inv x) | ].
  destruct x as [a0 a1].
  cbv [Pairing.fp2_inv CubicFieldExtensionsSpecs.BLS12Fp6Spec.fp2_inv fst snd bls12_beta].
  change (F.of_Z _ (-1)) with (F.opp (@F.one (@PrimeField.M_pos pp))).
  assert (E : F.add (F.mul a0 a0) (F.mul a1 a1)
              = F.sub (F.mul a0 a0) (F.mul (F.mul (F.opp F.one) a1) a1)) by ring.
  rewrite E. reflexivity.
Qed.

Section Fp12.
  Variable extra : list function_t.
  Local Notation functions := (map.of_list (bls12_pairing_funcs ++ extra) : env).

  Local Ltac env_main := rewrite get_of_list_find; apply first_binding_app; exact eq_refl.

  Local Notation Fp6_args := (bls12_beta, bls12_xi_re, bls12_xi_im).

  Lemma env_Fp6_sub :
    map.get functions (fst (Fp6_sub (prime_parameters:=pp) (F_representation:=frep)
                 bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix)) =
    Some (snd (Fp6_sub (prime_parameters:=pp) (F_representation:=frep)
                 bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix)).
  Proof. env_main. Qed.
  Lemma env_Fp6_sqr :
    map.get functions (fst (Fp6_sqr (prime_parameters:=pp) (F_representation:=frep)
                 bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix)) =
    Some (snd (Fp6_sqr (prime_parameters:=pp) (F_representation:=frep)
                 bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix)).
  Proof. env_main. Qed.
  Lemma env_Fp6_inv :
    map.get functions (fst (Fp6_inv (prime_parameters:=pp) (F_representation:=frep)
                 bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix)) =
    Some (snd (Fp6_inv (prime_parameters:=pp) (F_representation:=frep)
                 bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix)).
  Proof. env_main. Qed.
  Lemma env_Fp12_mul :
    map.get functions (fst (Fp12_mul (prime_parameters:=pp) (F_representation:=frep)
                 bls12_beta bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix)) =
    Some (snd (Fp12_mul (prime_parameters:=pp) (F_representation:=frep)
                 bls12_beta bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix)).
  Proof. env_main. Qed.

  Hypothesis HFp2copy : MS.spec_of_Fp2_felem_copy functions.
  Hypothesis HFp2add : MS.spec_of_Fp2_add functions.
  Hypothesis HFp2sub : MS.spec_of_Fp2_sub functions.
  Hypothesis HFp2mul : MS.spec_of_Fp2_mul functions.
  Hypothesis HFp2sqr : MS.spec_of_Fp2_sqr functions.
  Hypothesis HFp2inv : MS.spec_of_Fp2_inv functions.
  Hypothesis HFp2opp : MS.spec_of_Fp2_opp functions.
  Hypothesis HFpcopy : MS.spec_of_Fp_felem_copy functions.
  Hypothesis HFpsub :
    AbstractField.binop_spec (F:=Fp) (field_representation:=frep) AbstractField.bin_sub functions.
  Hypothesis HFpadd :
    AbstractField.binop_spec (F:=Fp) (field_representation:=frep) AbstractField.bin_add functions.

  Let Hxi := bls12_Fp2_mul_xi_flat functions (env_Fp2_mul_xi extra) HFpcopy HFpsub HFpadd.
  Let Hc6 := bls12_Fp6_felem_copy_spec extra HFp2copy.
  Let Ha6 := bls12_Fp6_add_leaf extra HFp2copy HFp2add.
  Let Hm6 := bls12_Fp6_mul_leaf extra HFp2copy HFp2add HFpcopy HFp2mul HFp2sub HFpsub HFpadd.
  Let Hv6 := bls12_Fp6_mul_by_v_leaf extra HFp2copy HFpcopy HFpsub HFpadd.
  Let Ho6 := bls12_Fp6_opp_spec extra HFp2copy HFp2opp.
  Let Hc12 := bls12_Fp12_felem_copy_leaf extra HFp2copy.

  Lemma bls12_Fp6_sub_spec :
    CubicFieldExtensions.spec_of_Fp6_sub (prime_parameters:=pp) (F_representation:=frep)
      bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix functions.
  Proof.
    exact (Fp6_sub_ok (prime_parameters:=pp) (F_representation:=frep)
             bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix functions
             env_Fp6_sub Hc6 Hc6 HFp2sub HFp2sub HFp2sub).
  Qed.
  Let Hs6 := bls12_Fp6_sub_spec.

  Local Ltac specs :=
    lazymatch goal with
    | |- context [CubicFieldExtensions.spec_of_Fp2_mul_xi] => exact Hxi
    | |- context [CubicFieldExtensions.spec_of_Fp2_felem_copy] => exact HFp2copy
    | |- context [CubicFieldExtensions.spec_of_Fp2_add] => exact HFp2add
    | |- context [CubicFieldExtensions.spec_of_Fp2_sub] => exact HFp2sub
    | |- context [CubicFieldExtensions.spec_of_Fp2_mul] => exact HFp2mul
    | |- context [CubicFieldExtensions.spec_of_Fp2_square] => exact HFp2sqr
    | |- context [CubicFieldExtensions.spec_of_Fp2_inv] => exact HFp2inv
    | |- context [CubicFieldExtensions.spec_of_Fp2_opp] => exact HFp2opp
    | |- context [QuadraticFieldExtensions.spec_of_Fp2_add] => exact HFp2add
    | |- context [QuadraticFieldExtensions.spec_of_Fp2_sub] => exact HFp2sub
    | |- context [CubicFieldExtensions.spec_of_Fp6_copy] => exact Hc6
    | |- context [CubicFieldExtensions.spec_of_Fp6_add] => exact Ha6
    | |- context [CubicFieldExtensions.spec_of_Fp6_sub] => exact Hs6
    | |- context [CubicFieldExtensions.spec_of_Fp6_mul] => exact Hm6
    | |- context [CubicFieldExtensions.spec_of_Fp6_opp] => exact Ho6
    | |- context [DodecicFieldExtensions.spec_of_Fp6_felem_copy] => exact Hc6
    | |- context [DodecicFieldExtensions.spec_of_Fp6_opp] => exact Ho6
    | |- context [DodecicFieldExtensions.spec_of_Fp6_mul_by_v] => exact Hv6
    | |- context [DodecicFieldExtensions.spec_of_Fp12_copy] => exact Hc12
    | |- context [DM.spec_of_Fp6_felem_copy] => exact Hc6
    | |- context [DM.spec_of_Fp6_add] => exact Ha6
    | |- context [DM.spec_of_Fp6_mul] => exact Hm6
    | |- context [DM.spec_of_Fp6_sub] => exact Hs6
    | |- context [DM.spec_of_Fp6_mul_by_v] => exact Hv6
    | |- context [DM.spec_of_Fp12_copy] => exact Hc12
    | |- ?g => idtac "UNMATCHED" g; fail
    end.

  Lemma bls12_Fp6_sqr_spec :
    CubicFieldExtensions.spec_of_Fp6_sqr (prime_parameters:=pp) (F_representation:=frep)
      bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix functions.
  Proof.
    eapply (Fp6_sqr_ok (prime_parameters:=pp) (F_representation:=frep)
              (bounds_equiv:=bls12_Fp_bounds_equiv)
              bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix
              (fun a b => eq_refl) functions env_Fp6_sqr).
    all: specs.
  Qed.
  Let Hq6 := bls12_Fp6_sqr_spec.


  Lemma bls12_Fp6_inv_spec :
    CubicFieldExtensions.spec_of_Fp6_inv (prime_parameters:=pp) (F_representation:=frep)
      bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix functions.
  Proof.
    eapply (Fp6_inv_ok (prime_parameters:=pp) (F_representation:=frep)
              (F_representation_ok:=MS.bls12_Fp_rep_ok)
              (bounds_equiv:=bls12_Fp_bounds_equiv)
              bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix
              (fun a b => eq_refl) bls12_invp2_eq_fp6_fp2_inv functions env_Fp6_inv).
    all: specs.
  Qed.
  Let Hi6 := bls12_Fp6_inv_spec.

  Local Ltac specs12 :=
    lazymatch goal with
    | |- _ => specs
    end.

  Lemma bls12_Fp12_mul_spec :
    DM.spec_of_Fp12_mul (prime_parameters:=pp) (F_representation:=frep)
      bls12_beta bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix functions.
  Proof.
    eapply (DM.Fp12_mul_ok (prime_parameters:=pp) (F_representation:=frep)
              (bounds_equiv:=bls12_Fp_bounds_equiv)
              bls12_beta bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix
              functions env_Fp12_mul).
    all: specs12.
  Qed.

  Lemma bls12_Fp12_mul_leaf_MS : MS.spec_of_Fp12_mul functions.
  Proof. exact bls12_Fp12_mul_spec. Qed.
  Lemma bls12_Fp12_mul_leaf_FE : FE.spec_of_Fp12_mul functions.
  Proof. exact bls12_Fp12_mul_spec. Qed.

End Fp12.
