(** * BLS12-381 final exponentiation: composition of the functional proofs

    Instantiates the callee hypotheses of
      BLS12_FinalExpHardDSDFunctional.bls12_final_exp_hard_dsd_functional_ok
      BLS12_FinalExpFunctional.bls12_final_exp_functional_ok
    with the proved functional lemmas:
      cyclotomic exponentiations   BLS12_CycExpFunctional (feval = conj (pw B e))
      Frobenius-p constant loaders BLS12_LoadersFeval
      Frobenius / Frobenius-p^2    PairingFieldOps.spec_of_Fp12_frobenius(_p2) (library specs,
                                   proved by PairingFieldOps.Fp12_frobenius(_p2)_ok)
    [bls12_final_exp_functional_closed] then assumes only the environment facts and
    the specs of the arithmetic leaves (Fp/Fp6/Fp12 field ops, from_word, the library
    Frobenius specs).
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Bedrock.Field.Synthesis.Examples.BN_StraightlineFast.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime_certif.
Require Import Bedrock.Field.Synthesis.Examples.bls12_felem_copy.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.PairingFieldOps.
Require Import Bedrock.Field.FieldExtensions.WPTactics.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_Pairing.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingHelpers.
Require Import bedrock2.Loops.
Require Import bedrock2.SepCalls.
Require Import coqutil.Z.Lia.
Require Import bedrock2.SepAutoArray.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_CurveInstances.

Require Import Bedrock.Field.Synthesis.Examples.BLS12_CycExp.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_FinalExpHardDSD.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_FinalExp.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_CycExpFunctional.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_FinalExpHardDSDFunctional.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_FinalExpFunctional.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_LoadersFeval.
Require Import Theory.BLS12Pairing.Fp12Ring.
Require Import Theory.BLS12Pairing.Cyclotomic.
Require Import Theory.BLS12Pairing.CycExpModel.
Require Bedrock.Field.Synthesis.Examples.BLS12_Fp2Feval.
Require Theory.BLS12Pairing.Pairing.
Module P := Theory.BLS12Pairing.Pairing.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Existing Instances
  Defaults64.default_parameters
  Defaults64.default_parameters_ok.

(** ** The cyclotomic exponentiations *)

Lemma glue_cyc_exp_x_neg : forall functions,
  BLS12_CycExpFunctional.spec_of_cyc_exp_neg_functional "bls12_Fp12_cyc_exp_x_neg" P.bls_x functions ->
  BLS12_FinalExpHardDSDFunctional.spec_of_cyc_exp_x_neg_functional functions.
Proof.
  intros functions H.
  intros pout pbase old_out base_val Rr tr mem Hpre.
  eapply Semantics.weaken_call; [exact (H pout pbase old_out base_val Rr tr mem Hpre) |].
  intros tr' mem' rets [Hr [Ht [out [Hf Hrest]]]].
  split; [exact Hr |]. split; [exact Ht |]. exists out. split; [| exact Hrest].
  intros HB. etransitivity; [exact (Hf HB) |].
  rewrite pow_bls_x_signed_pw. reflexivity.
Qed.

Lemma glue_cyc_exp_c_neg : forall functions,
  BLS12_CycExpFunctional.spec_of_cyc_exp_neg_functional "bls12_Fp12_cyc_exp_c_neg" P.bls_c functions ->
  BLS12_FinalExpHardDSDFunctional.spec_of_cyc_exp_c_neg_functional functions.
Proof.
  intros functions H.
  intros pout pbase old_out base_val Rr tr mem Hpre.
  eapply Semantics.weaken_call; [exact (H pout pbase old_out base_val Rr tr mem Hpre) |].
  intros tr' mem' rets [Hr [Ht [out [Hf Hrest]]]].
  split; [exact Hr |]. split; [exact Ht |]. exists out. split; [| exact Hrest].
  intros HB. etransitivity; [exact (Hf HB) |].
  rewrite pow_bls_c_signed_pw. reflexivity.
Qed.

(** ** The loaders *)

Lemma glue_load_gamma1 : forall functions,
  map.get functions "bls12_load_gamma1" = Some (snd BLS12_Pairing.bls12_load_gamma1) ->
  BLS12_FinalExpHardDSDFunctional.spec_of_bls12_load_gamma1_functional functions.
Proof.
  intros functions E pout old_out Rr tr mem H.
  exact (BLS12_LoadersFeval.bls12_load_gamma1_feval_ok functions E pout old_out Rr tr mem H).
Qed.

Lemma glue_load_gamma2 : forall functions,
  map.get functions "bls12_load_gamma2" = Some (snd BLS12_Pairing.bls12_load_gamma2) ->
  BLS12_FinalExpHardDSDFunctional.spec_of_bls12_load_gamma2_functional functions.
Proof.
  intros functions E pout old_out Rr tr mem H.
  exact (BLS12_LoadersFeval.bls12_load_gamma2_feval_ok functions E pout old_out Rr tr mem H).
Qed.

Lemma glue_load_w_frob_c1 : forall functions,
  map.get functions "bls12_load_w_frob_c1" = Some (snd BLS12_Pairing.bls12_load_w_frob_c1) ->
  BLS12_FinalExpHardDSDFunctional.spec_of_bls12_load_w_frob_c1_functional functions.
Proof.
  intros functions E pout old_out Rr tr mem H.
  exact (BLS12_LoadersFeval.bls12_load_w_frob_c1_feval_ok functions E pout old_out Rr tr mem H).
Qed.

(** ** The Frobenius maps: library specs -> Pairing.v models *)

Section Frob.
  Existing Instance BLS12_FinalExpHardDSD.bls12_pf_params.
  Existing Instance prime_field_parameters.
  Existing Instance BLS12_FinalExpHardDSD.bls12_Fp_rep.

  Let fp2_prefix := "bls12_Fp2_".
  Let fp6_prefix := "bls12_Fp6_".
  Let fp12_prefix := "bls12_Fp12_".
  Let bls12_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-1).
  Let bls12_xi_re : F PrimeField.M_pos := @F.one PrimeField.M_pos.
  Let bls12_xi_im : F PrimeField.M_pos := @F.one PrimeField.M_pos.

  Lemma frob_model_eq g1 g2 w x :
    PairingFieldOps.fp12_frobenius_model bls12_beta fp2_prefix g1 g2 w x =
    P.fp12_frobenius PrimeField.M_pos g1 g2 w x.
  Proof.
    destruct x as [[[x0 x1] x2] [[y0 y1] y2]].
    cbv [PairingFieldOps.fp12_frobenius_model PairingFieldOps.fp6_frobenius_model
         PairingFieldOps.fp6_mul_fp2_model PairingFieldOps.fp2_conj
         P.fp12_frobenius P.fp6_frobenius P.fp6_mul_fp2 P.fp12_build P.fp12_c0 P.fp12_c1
         P.fp6_build P.fp6_c0 P.fp6_c1 P.fp6_c2 P.fp2_conjugate fst snd].
    rewrite <- !(BLS12_Fp2Feval.mulp2_eq_fp2_mul PrimeField.M_pos).
    reflexivity.
  Qed.

  Lemma frob_p2_model_eq g1 g2 w x :
    PairingFieldOps.fp12_frobenius_p2_model bls12_beta fp2_prefix g1 g2 w x =
    P.fp12_frobenius_p2 PrimeField.M_pos g1 g2 w x.
  Proof.
    destruct x as [[[x0 x1] x2] [[y0 y1] y2]].
    cbv [PairingFieldOps.fp12_frobenius_p2_model PairingFieldOps.fp6_frobenius_p2_model
         PairingFieldOps.fp6_mul_fp2_model
         P.fp12_frobenius_p2 P.fp6_frobenius_p2 P.fp6_mul_fp2 P.fp12_build P.fp12_c0 P.fp12_c1
         P.fp6_build P.fp6_c0 P.fp6_c1 P.fp6_c2 fst snd].
    rewrite <- !(BLS12_Fp2Feval.mulp2_eq_fp2_mul PrimeField.M_pos).
    reflexivity.
  Qed.

  Lemma glue_frobenius : forall functions,
    PairingFieldOps.spec_of_Fp12_frobenius bls12_beta bls12_xi_re bls12_xi_im
      fp12_prefix fp6_prefix fp2_prefix functions ->
    BLS12_FinalExpHardDSDFunctional.spec_of_Fp12_frobenius_functional functions.
  Proof.
    intros functions H.
    intros pout px pg1 pg2 pw old_out x g1 g2 w Rr tr mem Hpre.
    eapply Semantics.weaken_call; [exact (H pout px pg1 pg2 pw old_out x g1 g2 w Rr tr mem Hpre) |].
    intros tr' mem' rets [Hr [Ht [out [Hf [Hb Hs]]]]].
    split; [exact Hr |]. split; [exact Ht |]. exists out. split; [| split; [exact Hb | exact Hs]].
    etransitivity; [exact Hf |]. apply frob_model_eq.
  Qed.

  Lemma glue_frobenius_p2 : forall functions,
    PairingFieldOps.spec_of_Fp12_frobenius_p2 bls12_beta bls12_xi_re bls12_xi_im
      fp12_prefix fp6_prefix fp2_prefix functions ->
    BLS12_FinalExpHardDSDFunctional.spec_of_Fp12_frobenius_p2_functional functions.
  Proof.
    intros functions H.
    intros pout px pg1 pg2 pw old_out x g1 g2 w Rr tr mem Hpre.
    eapply Semantics.weaken_call; [exact (H pout px pg1 pg2 pw old_out x g1 g2 w Rr tr mem Hpre) |].
    intros tr' mem' rets [Hr [Ht [out [Hf [Hb Hs]]]]].
    split; [exact Hr |]. split; [exact Ht |]. exists out. split; [| split; [exact Hb | exact Hs]].
    etransitivity; [exact Hf |]. apply frob_p2_model_eq.
  Qed.

  Lemma glue_frobenius_p2' : forall functions,
    PairingFieldOps.spec_of_Fp12_frobenius_p2 bls12_beta bls12_xi_re bls12_xi_im
      fp12_prefix fp6_prefix fp2_prefix functions ->
    BLS12_FinalExpFunctional.spec_of_Fp12_frobenius_p2_functional functions.
  Proof.
    intros functions H. exact (glue_frobenius_p2 functions H).
  Qed.

  (** ** The hard part, in the instance context of BLS12_FinalExp.v *)

  Lemma glue_hard : forall functions,
    BLS12_FinalExpHardDSDFunctional.spec_of_bls12_final_exp_hard_dsd_functional functions ->
    BLS12_FinalExpFunctional.spec_of_bls12_final_exp_hard_dsd_functional functions.
  Proof. intros functions H. exact H. Qed.

  (** ** The final exponentiation, from the function bodies and the arithmetic leaves *)

  Theorem bls12_final_exp_functional_closed :
    forall functions
      (E_fe : map.get functions "bls12_final_exp" = Some (snd BLS12_Pairing.bls12_final_exp))
      (E_hard : map.get functions "bls12_final_exp_hard_dsd" =
                Some (snd BLS12_Pairing.bls12_final_exp_hard_dsd))
      (E_x : map.get functions "bls12_Fp12_cyc_exp_x_neg" =
             Some (snd BLS12_Pairing.bls12_Fp12_cyc_exp_x_neg))
      (E_c : map.get functions "bls12_Fp12_cyc_exp_c_neg" =
             Some (snd BLS12_Pairing.bls12_Fp12_cyc_exp_c_neg))
      (E_g1 : map.get functions "bls12_load_gamma1" = Some (snd BLS12_Pairing.bls12_load_gamma1))
      (E_g2 : map.get functions "bls12_load_gamma2" = Some (snd BLS12_Pairing.bls12_load_gamma2))
      (E_w : map.get functions "bls12_load_w_frob_c1" = Some (snd BLS12_Pairing.bls12_load_w_frob_c1))
      (HFp12mul : BLS12_FinalExp.spec_of_Fp12_mul functions)
      (HFp12inv : BLS12_FinalExp.spec_of_Fp12_inv functions)
      (HFp12conj : BLS12_FinalExp.spec_of_Fp12_conjugate functions)
      (HFp6mul : BLS12_CycExp.spec_of_Fp6_mul functions)
      (HFp6add : BLS12_CycExp.spec_of_Fp6_add functions)
      (HFp6mulv : BLS12_CycExp.spec_of_Fp6_mul_by_v functions)
      (HFpadd : BLS12_CycExp.spec_of_Fp_add functions)
      (HFfromword : BLS12_CycExp.spec_of_Fp_from_word functions)
      (HFfrob : PairingFieldOps.spec_of_Fp12_frobenius bls12_beta bls12_xi_re bls12_xi_im
                  fp12_prefix fp6_prefix fp2_prefix functions)
      (HFfrobp2 : PairingFieldOps.spec_of_Fp12_frobenius_p2 bls12_beta bls12_xi_re bls12_xi_im
                  fp12_prefix fp6_prefix fp2_prefix functions),
    BLS12_FinalExpFunctional.spec_of_bls12_final_exp_functional functions.
  Proof.
    intros.
    pose proof (BLS12_CycExpFunctional.bls12_Fp12_cyc_exp_x_neg_functional_ok functions E_x
      HFp12mul HFp12conj HFp6mul HFp6add HFp6mulv HFpadd HFfromword) as Hx.
    pose proof (BLS12_CycExpFunctional.bls12_Fp12_cyc_exp_c_neg_functional_ok functions E_c
      HFp12mul HFp12conj HFp6mul HFp6add HFp6mulv HFpadd HFfromword) as Hc.
    pose proof (BLS12_FinalExpHardDSDFunctional.bls12_final_exp_hard_dsd_functional_ok functions E_hard
      HFp12mul HFp12conj (glue_frobenius functions HFfrob) (glue_frobenius_p2 functions HFfrobp2)
      (glue_cyc_exp_x_neg functions Hx) (glue_cyc_exp_c_neg functions Hc)
      (glue_load_gamma1 functions E_g1) (glue_load_gamma2 functions E_g2)
      (glue_load_w_frob_c1 functions E_w)) as Hhard.
    exact (BLS12_FinalExpFunctional.bls12_final_exp_functional_ok functions E_fe
      HFp12mul HFp12inv HFp12conj (glue_frobenius_p2' functions HFfrobp2) (glue_hard functions Hhard)).
  Qed.
  Theorem bls12_final_exp_nonzero_closed :
    forall functions
      (E_fe : map.get functions "bls12_final_exp" = Some (snd BLS12_Pairing.bls12_final_exp))
      (E_hard : map.get functions "bls12_final_exp_hard_dsd" =
                Some (snd BLS12_Pairing.bls12_final_exp_hard_dsd))
      (E_x : map.get functions "bls12_Fp12_cyc_exp_x_neg" =
             Some (snd BLS12_Pairing.bls12_Fp12_cyc_exp_x_neg))
      (E_c : map.get functions "bls12_Fp12_cyc_exp_c_neg" =
             Some (snd BLS12_Pairing.bls12_Fp12_cyc_exp_c_neg))
      (E_g1 : map.get functions "bls12_load_gamma1" = Some (snd BLS12_Pairing.bls12_load_gamma1))
      (E_g2 : map.get functions "bls12_load_gamma2" = Some (snd BLS12_Pairing.bls12_load_gamma2))
      (E_w : map.get functions "bls12_load_w_frob_c1" = Some (snd BLS12_Pairing.bls12_load_w_frob_c1))
      (HFp12mul : BLS12_FinalExp.spec_of_Fp12_mul functions)
      (HFp12inv : BLS12_FinalExp.spec_of_Fp12_inv functions)
      (HFp12conj : BLS12_FinalExp.spec_of_Fp12_conjugate functions)
      (HFp6mul : BLS12_CycExp.spec_of_Fp6_mul functions)
      (HFp6add : BLS12_CycExp.spec_of_Fp6_add functions)
      (HFp6mulv : BLS12_CycExp.spec_of_Fp6_mul_by_v functions)
      (HFpadd : BLS12_CycExp.spec_of_Fp_add functions)
      (HFfromword : BLS12_CycExp.spec_of_Fp_from_word functions)
      (HFfrob : PairingFieldOps.spec_of_Fp12_frobenius bls12_beta bls12_xi_re bls12_xi_im
                  fp12_prefix fp6_prefix fp2_prefix functions)
      (HFfrobp2 : PairingFieldOps.spec_of_Fp12_frobenius_p2 bls12_beta bls12_xi_re bls12_xi_im
                  fp12_prefix fp6_prefix fp2_prefix functions),
    BLS12_FinalExpFunctional.spec_of_bls12_final_exp_nonzero functions.
  Proof.
    intros. apply BLS12_FinalExpFunctional.bls12_final_exp_nonzero_of_functional.
    exact (bls12_final_exp_functional_closed functions E_fe E_hard E_x E_c E_g1 E_g2 E_w
      HFp12mul HFp12inv HFp12conj HFp6mul HFp6add HFp6mulv HFpadd HFfromword HFfrob HFfrobp2).
  Qed.
End Frob.
