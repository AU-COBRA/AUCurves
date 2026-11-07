(** * BLS12-381: the closed functional correctness theorem of the bedrock2 [bls12_pairing].

    [bls12_pairing_functional_closed] discharges the two callee hypotheses of
    [BLS12_PairingFunctional.bls12_pairing_functional_ok]:
      - the Miller loop by [BLS12_MillerLoopPairingTransfer.bls12_miller_loop_pairing_ok_helpers];
      - the final exponentiation by [BLS12_FinalExpGlue.bls12_final_exp_nonzero_closed].
    What remains assumed are (a) the environment facts [map.get functions name = Some body] for
    the bedrock2 functions of BLS12_Pairing.v that are verified here (pairing, Miller loop,
    make_line, Fp2_mul_fp, the sparse multiplication by a line, final exp, hard part, cyclotomic
    exponentiations, the Granger-Scott squaring, the six constant loaders) and (b) the specs of the arithmetic leaves (Fp / Fp2 /
    Fp12 field operations, Fp2 multiplication by xi, copies, from_word, the library Frobenius
    specs), exactly the leaf hypotheses of the two
    closed callee theorems.  [BLS12_PairingTop.bls12_pairing_ok] takes the Miller loop and the
    final exponentiation as hypotheses, so this goes further than the existing chain.
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
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
Require Import Bedrock.Field.FieldExtensions.PairingFieldOps.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_Pairing.
Require Bedrock.Field.Synthesis.Examples.BLS12_PairingHelpers.
Require Bedrock.Field.Synthesis.Examples.BLS12_MillerStepFunctional.
Require Bedrock.Field.Synthesis.Examples.BLS12_MillerLoopPairingTransfer.
Require Bedrock.Field.Synthesis.Examples.BLS12_FinalExp.
Require Bedrock.Field.Synthesis.Examples.BLS12_CycExp.
Require Bedrock.Field.Synthesis.Examples.BLS12_FinalExpHardDSD.
Require Bedrock.Field.Synthesis.Examples.BLS12_FinalExpGlue.
Require Bedrock.Field.Synthesis.Examples.BLS12_CycSqrGS.
Require Bedrock.Field.Synthesis.Examples.BLS12_MulByLine.
Require Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingFunctional.
Module MS := Bedrock.Field.Synthesis.Examples.BLS12_MillerStepFunctional.
Module FE := Bedrock.Field.Synthesis.Examples.BLS12_FinalExp.
Module CE := Bedrock.Field.Synthesis.Examples.BLS12_CycExp.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Existing Instances
  Defaults64.default_parameters
  Defaults64.default_parameters_ok.

(** The library Frobenius specs, elaborated in the context of BLS12_FinalExpGlue (instances of
    BLS12_FinalExpHardDSD). *)
Section FrobSpecs.
  Existing Instance BLS12_FinalExpHardDSD.bls12_pf_params.
  Existing Instance prime_field_parameters.
  Existing Instance BLS12_FinalExpHardDSD.bls12_Fp_rep.
  Let fp2_prefix := "bls12_Fp2_".
  Let fp6_prefix := "bls12_Fp6_".
  Let fp12_prefix := "bls12_Fp12_".
  Let bls12_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-1).
  Let bls12_xi_re : F PrimeField.M_pos := @F.one PrimeField.M_pos.
  Let bls12_xi_im : F PrimeField.M_pos := @F.one PrimeField.M_pos.

  Definition spec_of_Fp12_frobenius_381 functions : Prop :=
    PairingFieldOps.spec_of_Fp12_frobenius bls12_beta bls12_xi_re bls12_xi_im
      fp12_prefix fp6_prefix fp2_prefix functions.
  Definition spec_of_Fp12_frobenius_p2_381 functions : Prop :=
    PairingFieldOps.spec_of_Fp12_frobenius_p2 bls12_beta bls12_xi_re bls12_xi_im
      fp12_prefix fp6_prefix fp2_prefix functions.
  (** Multiplication by xi = 1 + u in Fp2 (a callee of the Granger-Scott squaring). *)
  Definition spec_of_Fp2_mul_xi_381 functions : Prop :=
    CubicFieldExtensions.spec_of_Fp2_mul_xi bls12_beta bls12_xi_re bls12_xi_im fp2_prefix functions.
End FrobSpecs.

Theorem bls12_pairing_functional_closed :
  forall functions
    (* environment: the verified bedrock2 functions of BLS12_Pairing.v *)
    (E_pairing : map.get functions "bls12_pairing" = Some (snd bls12_pairing))
    (E_lg1p2 : map.get functions "bls12_load_gamma1_p2" = Some (snd bls12_load_gamma1_p2))
    (E_lg2p2 : map.get functions "bls12_load_gamma2_p2" = Some (snd bls12_load_gamma2_p2))
    (E_lwp2 : map.get functions "bls12_load_w_frob_p2_c1" = Some (snd bls12_load_w_frob_p2_c1))
    (E_ml : map.get functions "bls12_miller_loop" = Some (snd bls12_miller_loop))
    (E_line : map.get functions "bls12_make_line" = Some (snd bls12_make_line))
    (E_mulfp : map.get functions "bls12_Fp2_mul_fp" = Some (snd bls12_Fp2_mul_fp))
    (E_fe : map.get functions "bls12_final_exp" = Some (snd bls12_final_exp))
    (E_hard : map.get functions "bls12_final_exp_hard_dsd" = Some (snd bls12_final_exp_hard_dsd))
    (E_x : map.get functions "bls12_Fp12_cyc_exp_x_neg" = Some (snd bls12_Fp12_cyc_exp_x_neg))
    (E_c : map.get functions "bls12_Fp12_cyc_exp_c_neg" = Some (snd bls12_Fp12_cyc_exp_c_neg))
    (E_g1 : map.get functions "bls12_load_gamma1" = Some (snd bls12_load_gamma1))
    (E_g2 : map.get functions "bls12_load_gamma2" = Some (snd bls12_load_gamma2))
    (E_w : map.get functions "bls12_load_w_frob_c1" = Some (snd bls12_load_w_frob_c1))
    (E_gs : map.get functions "bls12_Fp12_cyclotomic_square"
            = Some (snd bls12_Fp12_cyclotomic_square))
    (E_mbl : map.get functions "bls12_Fp12_mul_by_line"
            = Some (snd bls12_Fp12_mul_by_line))
    (* arithmetic leaves used by the Miller loop *)
    (HFp2mul : MS.spec_of_Fp2_mul functions)
    (HFp2add : MS.spec_of_Fp2_add functions)
    (HFp2sub : MS.spec_of_Fp2_sub functions)
    (HFp2sqr : MS.spec_of_Fp2_sqr functions)
    (HFp2inv : MS.spec_of_Fp2_inv functions)
    (HFp2opp : MS.spec_of_Fp2_opp functions)
    (HFp2copy : MS.spec_of_Fp2_felem_copy functions)
    (HFp12sqr : MS.spec_of_Fp12_sqr functions)
    (HFp12copy : MS.spec_of_Fp12_felem_copy functions)
    (HFpmul : MS.spec_of_Fp_mul functions)
    (HFpcopy : MS.spec_of_Fp_felem_copy functions)
    (HFfromword_ml : MS.spec_of_Fp_from_word functions)
    (* arithmetic leaves used by the final exponentiation *)
    (HFp12mul : FE.spec_of_Fp12_mul functions)
    (HFp12inv : FE.spec_of_Fp12_inv functions)
    (HFp12conj : FE.spec_of_Fp12_conjugate functions)
    (HFp2mulxi : spec_of_Fp2_mul_xi_381 functions)
    (HFfromword : CE.spec_of_Fp_from_word functions)
    (HFfrob : spec_of_Fp12_frobenius_381 functions)
    (HFfrobp2 : spec_of_Fp12_frobenius_p2_381 functions),
  spec_of_bls12_pairing_functional functions.
Proof.
  intros.
  apply bls12_pairing_functional_ok; [exact E_pairing | exact E_lg1p2 | exact E_lg2p2 | exact E_lwp2 | |].
  - pose proof (BLS12_MulByLine.mul_by_line_ok functions E_mbl HFp2mul HFp2add HFp2sub HFp2mulxi)
      as HMBL.
    exact (BLS12_MillerLoopPairingTransfer.bls12_miller_loop_pairing_ok_helpers functions E_ml
             HFp2mul HFp2add HFp2sub HFp2sqr HFp2inv HFp2opp HFp2copy
             HMBL HFp12sqr HFp12copy HFpmul HFpcopy HFfromword_ml E_line E_mulfp).
  - apply final_exp_nonzero_H.
    pose proof (BLS12_CycSqrGS.cyc_sqr_gs_ok functions E_gs HFp2mul HFp2add HFp2sub HFp2sqr
                  HFp2mulxi) as HGS.
    exact (BLS12_FinalExpGlue.bls12_final_exp_nonzero_closed functions E_fe E_hard E_x E_c E_g1 E_g2 E_w
             HFp12mul HFp12inv HFp12conj HGS HFfromword HFfrob HFfrobp2).
Qed.

Print Assumptions bls12_pairing_functional_closed.

(** All the hypotheses of [bls12_pairing_functional_closed] as one predicate on the function
    environment (for downstream statements). *)
Definition bls12_pairing_leaves functions : Prop :=
  (map.get functions "bls12_pairing" = Some (snd bls12_pairing)) /\
  (map.get functions "bls12_load_gamma1_p2" = Some (snd bls12_load_gamma1_p2)) /\
  (map.get functions "bls12_load_gamma2_p2" = Some (snd bls12_load_gamma2_p2)) /\
  (map.get functions "bls12_load_w_frob_p2_c1" = Some (snd bls12_load_w_frob_p2_c1)) /\
  (map.get functions "bls12_miller_loop" = Some (snd bls12_miller_loop)) /\
  (map.get functions "bls12_make_line" = Some (snd bls12_make_line)) /\
  (map.get functions "bls12_Fp2_mul_fp" = Some (snd bls12_Fp2_mul_fp)) /\
  (map.get functions "bls12_final_exp" = Some (snd bls12_final_exp)) /\
  (map.get functions "bls12_final_exp_hard_dsd" = Some (snd bls12_final_exp_hard_dsd)) /\
  (map.get functions "bls12_Fp12_cyc_exp_x_neg" = Some (snd bls12_Fp12_cyc_exp_x_neg)) /\
  (map.get functions "bls12_Fp12_cyc_exp_c_neg" = Some (snd bls12_Fp12_cyc_exp_c_neg)) /\
  (map.get functions "bls12_load_gamma1" = Some (snd bls12_load_gamma1)) /\
  (map.get functions "bls12_load_gamma2" = Some (snd bls12_load_gamma2)) /\
  (map.get functions "bls12_load_w_frob_c1" = Some (snd bls12_load_w_frob_c1)) /\
  (map.get functions "bls12_Fp12_cyclotomic_square" = Some (snd bls12_Fp12_cyclotomic_square)) /\
  (map.get functions "bls12_Fp12_mul_by_line" = Some (snd bls12_Fp12_mul_by_line)) /\
  MS.spec_of_Fp2_mul functions /\ MS.spec_of_Fp2_add functions /\ MS.spec_of_Fp2_sub functions /\
  MS.spec_of_Fp2_sqr functions /\ MS.spec_of_Fp2_inv functions /\ MS.spec_of_Fp2_opp functions /\
  MS.spec_of_Fp2_felem_copy functions /\
  MS.spec_of_Fp12_sqr functions /\ MS.spec_of_Fp12_felem_copy functions /\
  MS.spec_of_Fp_mul functions /\ MS.spec_of_Fp_felem_copy functions /\ MS.spec_of_Fp_from_word functions /\
  FE.spec_of_Fp12_mul functions /\ FE.spec_of_Fp12_inv functions /\ FE.spec_of_Fp12_conjugate functions /\
  spec_of_Fp2_mul_xi_381 functions /\ CE.spec_of_Fp_from_word functions /\
  spec_of_Fp12_frobenius_381 functions /\ spec_of_Fp12_frobenius_p2_381 functions.

Corollary bls12_pairing_functional_of_leaves : forall functions,
  bls12_pairing_leaves functions -> spec_of_bls12_pairing_functional functions.
Proof.
  intros functions H.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & H35).
  exact (bls12_pairing_functional_closed functions H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35).
Qed.

Print Assumptions bls12_pairing_functional_of_leaves.
