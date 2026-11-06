(** * The bedrock2 BLS12-381 Miller loop computes Pairing.miller_loop.

    Closes the hypotheses of [BLS12_MillerLoopFunctional.miller_fold_model_eq_miller_loop]:
      - the Fp2 inverse bridge (Finv of the bedrock2 Fp2 instance = Pairing.fp2_inv),
        from BLS12_Fp2InvBridge.v;
      - the six Fp6 bridges, from BLS12_Fp6Feval.v and BLS12_PairingFevalInst.v (all p);
    and composes the result with [bls12_miller_loop_functional_ok] into
    [bls12_miller_loop_pairing_ok]: for P, Q not at infinity whose coordinates are the
    fevals of the inputs, the output of the bedrock2 [bls12_miller_loop] has
    Fp12 feval [Pairing.miller_loop p P Q], p = BLS12_381_Frob.p = Z.to_pos bls_p.
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

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section BLS12_MillerLoopPairing.

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
    Local Opaque BLS12_MillerStepFunctional.bls12_Fp_rep.

    (* ============================================================ *)
    (* (a) Fp2 inverse bridge, (b) Fp6 bridges                       *)
    (* ============================================================ *)

    Lemma bls12_Fp2_Finv_eq_fp2_inv :
      forall a : Fp2, @AbstractField.Finv _ bls12_Fp2_params' a =
                      Pairing.fp2_inv PrimeField.M_pos a.
    Proof.
      intros a.
      change (@AbstractField.Finv _ bls12_Fp2_params' a)
        with (QuadraticExtensions.invp2 PrimeField.M_pos (F.of_Z PrimeField.M_pos (-1)) a).
      exact (bls12_381_invp2_eq_fp2_inv a).
    Qed.

    Theorem bls12_381_miller_fold_model_eq_miller_loop :
      forall (P : Pairing.G1Affine PrimeField.M_pos) (Q : Pairing.G2Affine PrimeField.M_pos),
        Pairing.g1_infinity PrimeField.M_pos P = false ->
        Pairing.g2_infinity PrimeField.M_pos Q = false ->
        fst (miller_fold_model (Pairing.g2_x PrimeField.M_pos Q) (Pairing.g2_y PrimeField.M_pos Q)
               (Pairing.g1_x PrimeField.M_pos P) (Pairing.g1_y PrimeField.M_pos P)
               Pairing.bls_x_bits) =
        Pairing.miller_loop PrimeField.M_pos P Q.
    Proof.
      exact (miller_fold_model_eq_miller_loop
               bls12_Fp2_Finv_eq_fp2_inv
               (BLS12_Fp6Feval.fp6_add_eq PrimeField.M_pos)
               (BLS12_Fp6Feval.fp6_sub_eq PrimeField.M_pos)
               (BLS12_Fp6Feval.fp6_mul_eq PrimeField.M_pos)
               (BLS12_Fp6Feval.fp6_mul_by_v_eq PrimeField.M_pos)
               (BLS12_PairingFevalInst.pairing_fp6_mul_self_eq_sqr PrimeField.M_pos)
               (BLS12_PairingFevalInst.pairing_fp6_karatsuba_cross_term PrimeField.M_pos)).
    Qed.

    (** The field of the bedrock2 instances is that of Commitments' BLS12_381.p. *)
    Lemma bls12_M_pos_eq_frob_p : PrimeField.M_pos = BLS12_FrobConstants.BLS12_381_Frob.p.
    Proof. vm_compute. reflexivity. Qed.

    (* ============================================================ *)
    (* (c) The closed functional Miller loop theorem                 *)
    (* ============================================================ *)

    Theorem bls12_miller_loop_pairing_ok :
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
        (old_out : Fp12_felem) (p_x p_y : Fp_felem) (q_x q_y : Fp2_felem) Rr tr mem
        (P : Pairing.G1Affine BLS12_FrobConstants.BLS12_381_Frob.p)
        (Q : Pairing.G2Affine BLS12_FrobConstants.BLS12_381_Frob.p),
        Pairing.g1_infinity _ P = false ->
        Pairing.g2_infinity _ Q = false ->
        Fp_feval p_x = Pairing.g1_x _ P ->
        Fp_feval p_y = Pairing.g1_y _ P ->
        Fp2_feval q_x = Pairing.g2_x _ Q ->
        Fp2_feval q_y = Pairing.g2_y _ Q ->
        Fp2_bounded Fp2_tight q_x /\
        Fp2_bounded Fp2_tight q_y /\
        Fp_bounded Fp_loose p_x /\
        Fp_bounded Fp_loose p_y /\
        (FElem_Fp12 pout old_out ⋆
         (FElem_Fp p_px p_x ⋆
          (FElem_Fp p_py p_y ⋆
           (FElem_Fp2 p_qx q_x ⋆
            (FElem_Fp2 p_qy q_y ⋆ Rr))))) mem ->
        WeakestPrecondition.call functions "bls12_miller_loop" tr mem
          [pout; p_px; p_py; p_qx; p_qy]
          (fun tr' mem' rets =>
            rets = [] /\ tr = tr' /\
            exists out,
              Fp12_feval out = Pairing.miller_loop BLS12_FrobConstants.BLS12_381_Frob.p P Q /\
              Fp12_bounded Fp12_loose out /\
              (FElem_Fp12 pout out ⋆
               (FElem_Fp p_px p_x ⋆
                (FElem_Fp p_py p_y ⋆
                 (FElem_Fp2 p_qx q_x ⋆
                  (FElem_Fp2 p_qy q_y ⋆ Rr))))) mem').
    Proof.
      intros functions EnvContains HFp2mul HFp2add HFp2sub HFp2sqr HFp2inv HFp2opp HFp2copy
        HFp12mul HFp12sqr HFp12copy HFpmul HFpcopy HFfromword HMakeLine HFp2mulfpEnv
        pout p_px p_py p_qx p_qy old_out p_x p_y q_x q_y Rr tr mem0 P Q HP HQ Hpx Hpy Hqx Hqy Hpre.
      pose proof (bls12_miller_loop_functional_ok functions EnvContains HFp2mul HFp2add HFp2sub
                    HFp2sqr HFp2inv HFp2opp HFp2copy HFp12mul HFp12sqr HFp12copy HFpmul HFpcopy
                    HFfromword HMakeLine HFp2mulfpEnv) as Hspec.
      cbv [spec_of_bls12_miller_loop_functional] in Hspec.
      eapply Semantics.weaken_call.
      { exact (Hspec pout p_px p_py p_qx p_qy old_out p_x p_y q_x q_y Rr tr mem0 Hpre). }
      cbv beta. intros tr' mem' rets [Hrets [Htr [out [Hfe [Hb Hs]]]]].
      split; [exact Hrets |]. split; [exact Htr |].
      exists out. split; [| split; [exact Hb | exact Hs]].
      rewrite Hfe, Hqx, Hqy, Hpx, Hpy.
      exact (bls12_381_miller_fold_model_eq_miller_loop P Q HP HQ).
    Qed.

End BLS12_MillerLoopPairing.

Print Assumptions bls12_Fp2_Finv_eq_fp2_inv.
Print Assumptions bls12_381_miller_fold_model_eq_miller_loop.
Print Assumptions bls12_miller_loop_pairing_ok.
