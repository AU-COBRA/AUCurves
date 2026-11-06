(** * bls12_miller_loop_pairing_ok restated with the BLS12_PairingHelpers instance terms
    (the form used by the top-level bls12_pairing proof).

    BLS12_PairingTop.v, BLS12_FinalExp.v and BLS12_LoadersFeval.v state their specs with
    cbv'd copies of the ext_* instances and their own bls12_pf_params; BLS12_MillerLoopFunctional.v and
    BLS12_MillerLoopPairing.v use ext_* directly.  The two are convertible; this file checks
    that the closed functional Miller loop theorem transfers by conversion ([exact]).
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.Loops.
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
Require Import Bedrock.Field.Synthesis.Examples.BLS12_CurveInstances.
Require Bedrock.Field.Synthesis.Examples.BLS12_MillerGeneric.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_MakeLineFunctional.
Require Theory.BLS12Pairing.Pairing.
Require Theory.BLS12Pairing.Fp12.
Require Bedrock.Field.Synthesis.Examples.BLS12_Fp12Feval.
Require Bedrock.Field.Synthesis.Examples.BLS12_PairingFeval.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_MillerStepFunctional.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_MillerLoopFunctional.
Require Bedrock.Field.Synthesis.Examples.BLS12_Fp6Feval.
Require Bedrock.Field.Synthesis.Examples.BLS12_PairingFevalInst.
Require Bedrock.Field.Synthesis.Examples.BLS12_FrobConstants.
Require Bedrock.Field.FieldExtensions.Theory.QuadraticExtensions.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_Fp2InvBridge.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_MillerLoopPairing.
Module H := Bedrock.Field.Synthesis.Examples.BLS12_PairingHelpers.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section BLS12_MillerLoopPairingTransfer.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    (* BLS12-381 prime parameters *)
    Let bls12_M_pos : positive := Eval vm_compute in (Z.to_pos bls12_prime.m).

    Existing Instance BLS12_MillerStepFunctional.bls12_pf_params.

    Existing Instance BLS12_MillerStepFunctional.bls12_pf_params_ok.

    Existing Instance prime_field_parameters.

    Local Notation Fp := (F PrimeField.M_pos).
    Local Notation Fp2 := ((Fp * Fp)%type).
    Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
    Local Notation Fp12 := ((Fp6 * Fp6)%type).

    (* Fp-level representation from synthesis pipeline *)
    Existing Instance BLS12_MillerStepFunctional.bls12_Fp_rep.

    Existing Instance BLS12_MillerStepFunctional.bls12_Fp_rep_ok.

    Let fp2_prefix := "bls12_Fp2_".
    Let fp6_prefix := "bls12_Fp6_".
    Let fp12_prefix := "bls12_Fp12_".

    (* β = -1 for BLS12-381 (p ≡ 3 mod 4) *)
    Let bls12_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-1).

    (* ξ = 1+u for BLS12-381 (cubic non-residue in Fp2 for Fp6 tower) *)
    Let bls12_xi_re : F PrimeField.M_pos := @F.one PrimeField.M_pos.
    Let bls12_xi_im : F PrimeField.M_pos := @F.one PrimeField.M_pos.

    (* ============================================================ *)
    (* Field extension instances                                     *)
    (* ============================================================ *)

    Existing Instance BLS12_MillerStepFunctional.bls12_Fp2_params'.
    Existing Instance BLS12_MillerStepFunctional.bls12_Fp2_rep'.
    Existing Instance BLS12_MillerStepFunctional.bls12_Fp6_params'.
    Existing Instance BLS12_MillerStepFunctional.bls12_Fp6_rep'.
    Existing Instance BLS12_MillerStepFunctional.bls12_Fp12_params'.
    Existing Instance BLS12_MillerStepFunctional.bls12_Fp12_rep'.

    (* ============================================================ *)
    (* Local notations for FElem types                               *)
    (* ============================================================ *)

    Local Notation FElem_Fp := (@AbstractField.FElem _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation FElem_Fp2 := (@AbstractField.FElem _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation FElem_Fp6 := (@AbstractField.FElem _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep').
    Local Notation FElem_Fp12 := (@AbstractField.FElem _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp_feval := (@AbstractField.feval _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp2_feval := (@AbstractField.feval _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp12_feval := (@AbstractField.feval _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp_bounded := (@AbstractField.bounded_by _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp2_bounded := (@AbstractField.bounded_by _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp12_bounded := (@AbstractField.bounded_by _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp_tight := (@AbstractField.tight_bounds _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp_loose := (@AbstractField.loose_bounds _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp2_tight := (@AbstractField.tight_bounds _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp2_loose := (@AbstractField.loose_bounds _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp12_tight := (@AbstractField.tight_bounds _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp12_loose := (@AbstractField.loose_bounds _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp2_felem := (@AbstractField.felem _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp_felem := (@AbstractField.felem _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp12_felem := (@AbstractField.felem _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').

    Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

    Local Typeclasses Opaque bls12_Fp12_params'.
    Local Typeclasses Opaque bls12_Fp6_params'.
    Local Typeclasses Opaque bls12_Fp2_params'.

    (* ============================================================ *)
    (* Callee spec instances                                         *)
    (* ============================================================ *)

    (* Fp2 operations *)
    Existing Instance BLS12_MillerStepFunctional.spec_of_Fp2_mul.

    Existing Instance BLS12_MillerStepFunctional.spec_of_Fp2_add.

    Existing Instance BLS12_MillerStepFunctional.spec_of_Fp2_sub.

    Existing Instance BLS12_MillerStepFunctional.spec_of_Fp2_sqr.

    Existing Instance BLS12_MillerStepFunctional.spec_of_Fp2_inv.

    Existing Instance BLS12_MillerStepFunctional.spec_of_Fp2_opp.

    Existing Instance BLS12_MillerStepFunctional.spec_of_Fp2_felem_copy.

    (* Fp12 operations *)
    Existing Instance BLS12_MillerStepFunctional.spec_of_Fp12_mul.

    Existing Instance BLS12_MillerStepFunctional.spec_of_Fp12_sqr.

    Existing Instance BLS12_MillerStepFunctional.spec_of_Fp12_felem_copy.

    (* Fp operations needed by make_line *)
    Existing Instance BLS12_MillerStepFunctional.spec_of_Fp_mul.

    Existing Instance BLS12_MillerStepFunctional.spec_of_Fp_felem_copy.

    Existing Instance BLS12_MillerStepFunctional.spec_of_Fp_from_word.

    (* The instance terms of BLS12_PairingHelpers / BLS12_PairingTop / BLS12_FinalExp /
       BLS12_LoadersFeval (cbv'd ext_* instances, own bls12_pf_params). *)
    Local Notation FElem_FpH := (@AbstractField.FElem _ _ _ _ _ _ H.bls12_Fp_rep).
    Local Notation FElem_Fp2H := (@AbstractField.FElem _ H.bls12_Fp2_params' _ _ _ _ H.bls12_Fp2_rep').
    Local Notation FElem_Fp12H := (@AbstractField.FElem _ H.bls12_Fp12_params' _ _ _ _ H.bls12_Fp12_rep').
    Local Notation Fp_fevalH := (@AbstractField.feval _ _ _ _ _ _ H.bls12_Fp_rep).
    Local Notation Fp2_fevalH := (@AbstractField.feval _ H.bls12_Fp2_params' _ _ _ _ H.bls12_Fp2_rep').
    Local Notation Fp12_fevalH := (@AbstractField.feval _ H.bls12_Fp12_params' _ _ _ _ H.bls12_Fp12_rep').
    Local Notation Fp_boundedH := (@AbstractField.bounded_by _ _ _ _ _ _ H.bls12_Fp_rep).
    Local Notation Fp2_boundedH := (@AbstractField.bounded_by _ H.bls12_Fp2_params' _ _ _ _ H.bls12_Fp2_rep').
    Local Notation Fp12_boundedH := (@AbstractField.bounded_by _ H.bls12_Fp12_params' _ _ _ _ H.bls12_Fp12_rep').
    Local Notation Fp_looseH := (@AbstractField.loose_bounds _ _ _ _ _ _ H.bls12_Fp_rep).
    Local Notation Fp2_tightH := (@AbstractField.tight_bounds _ H.bls12_Fp2_params' _ _ _ _ H.bls12_Fp2_rep').
    Local Notation Fp12_looseH := (@AbstractField.loose_bounds _ H.bls12_Fp12_params' _ _ _ _ H.bls12_Fp12_rep').
    Local Notation Fp2_felemH := (@AbstractField.felem _ H.bls12_Fp2_params' _ _ _ _ H.bls12_Fp2_rep').
    Local Notation Fp_felemH := (@AbstractField.felem _ _ _ _ _ _ H.bls12_Fp_rep).
    Local Notation Fp12_felemH := (@AbstractField.felem _ H.bls12_Fp12_params' _ _ _ _ H.bls12_Fp12_rep').

    Theorem bls12_miller_loop_pairing_ok_helpers :
      forall functions
        (EnvContains : map.get functions "bls12_miller_loop" =
          Some (snd bls12_miller_loop))
        (HFp2mul : spec_of_Fp2_mul functions)
        (HFp2add : spec_of_Fp2_add functions)
        (HFp2sub : spec_of_Fp2_sub functions)
        (HFp2sqr : spec_of_Fp2_sqr functions)
        (HFp2inv : spec_of_Fp2_inv functions)
        (HFp2opp : spec_of_Fp2_opp functions)
        (HFp2copy : spec_of_Fp2_felem_copy functions)
        (HFp12mul : spec_of_Fp12_mul functions)
        (HFp12sqr : spec_of_Fp12_sqr functions)
        (HFp12copy : spec_of_Fp12_felem_copy functions)
        (HFpmul : spec_of_Fp_mul functions)
        (HFpcopy : spec_of_Fp_felem_copy functions)
        (HFfromword : spec_of_Fp_from_word functions)
        (HMakeLine : map.get functions "bls12_make_line" =
          Some (snd bls12_make_line))
        (HFp2mulfpEnv : map.get functions "bls12_Fp2_mul_fp" =
          Some (snd bls12_Fp2_mul_fp)),
      forall (pout p_px p_py p_qx p_qy : word)
        (old_out : Fp12_felemH) (p_x p_y : Fp_felemH) (q_x q_y : Fp2_felemH) Rr tr mem
        (P : Pairing.G1Affine BLS12_FrobConstants.BLS12_381_Frob.p)
        (Q : Pairing.G2Affine BLS12_FrobConstants.BLS12_381_Frob.p),
        Pairing.g1_infinity _ P = false ->
        Pairing.g2_infinity _ Q = false ->
        Fp_fevalH p_x = Pairing.g1_x _ P ->
        Fp_fevalH p_y = Pairing.g1_y _ P ->
        Fp2_fevalH q_x = Pairing.g2_x _ Q ->
        Fp2_fevalH q_y = Pairing.g2_y _ Q ->
        Fp2_boundedH Fp2_tightH q_x /\
        Fp2_boundedH Fp2_tightH q_y /\
        Fp_boundedH Fp_looseH p_x /\
        Fp_boundedH Fp_looseH p_y /\
        (FElem_Fp12H pout old_out ⋆
         (FElem_FpH p_px p_x ⋆
          (FElem_FpH p_py p_y ⋆
           (FElem_Fp2H p_qx q_x ⋆
            (FElem_Fp2H p_qy q_y ⋆ Rr))))) mem ->
        WeakestPrecondition.call functions "bls12_miller_loop" tr mem
          [pout; p_px; p_py; p_qx; p_qy]
          (fun tr' mem' rets =>
            rets = [] /\ tr = tr' /\
            exists out,
              Fp12_fevalH out = Pairing.miller_loop BLS12_FrobConstants.BLS12_381_Frob.p P Q /\
              Fp12_boundedH Fp12_looseH out /\
              (FElem_Fp12H pout out ⋆
               (FElem_FpH p_px p_x ⋆
                (FElem_FpH p_py p_y ⋆
                 (FElem_Fp2H p_qx q_x ⋆
                  (FElem_Fp2H p_qy q_y ⋆ Rr))))) mem').
    Proof.
      intros functions EnvContains HFp2mul HFp2add HFp2sub HFp2sqr HFp2inv HFp2opp HFp2copy
        HFp12mul HFp12sqr HFp12copy HFpmul HFpcopy HFfromword HMakeLine HFp2mulfpEnv
        pout p_px p_py p_qx p_qy old_out p_x p_y q_x q_y Rr tr mem0 P Q HP HQ Hpx Hpy Hqx Hqy Hpre.
      exact (bls12_miller_loop_pairing_ok functions EnvContains HFp2mul HFp2add HFp2sub HFp2sqr
               HFp2inv HFp2opp HFp2copy HFp12mul HFp12sqr HFp12copy HFpmul HFpcopy HFfromword
               HMakeLine HFp2mulfpEnv pout p_px p_py p_qx p_qy old_out p_x p_y q_x q_y Rr tr mem0
               P Q HP HQ Hpx Hpy Hqx Hqy Hpre).
    Qed.

    Local Notation Fp12_tightH := (@AbstractField.tight_bounds _ H.bls12_Fp12_params' _ _ _ _ H.bls12_Fp12_rep').

    (** The Miller loop output is loose, [bls12_final_exp] needs a tight input; for the
        Montgomery representation loose and tight bounds coincide (fiat's loose_bounds_eq /
        tight_bounds_eq), so this is conversion. *)
    Lemma Fp12_loose_to_tight_H (x : Fp12_felemH) :
      Fp12_boundedH Fp12_looseH x -> Fp12_boundedH Fp12_tightH x.
    Proof. intros Hx. exact Hx. Qed.

End BLS12_MillerLoopPairingTransfer.

Print Assumptions bls12_miller_loop_pairing_ok_helpers.
Print Assumptions Fp12_loose_to_tight_H.
