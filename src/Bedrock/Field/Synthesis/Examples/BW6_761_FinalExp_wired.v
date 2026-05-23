(** * BW6-761 final exponentiation — frob/conjugate wiring.

    Discharges the four BW6 Frobenius/conjugate callee specs of
    [bw6_final_exp_ok_wired] from their underlying library theorems:
      - [bw6_fp6_frob{,_p2}_ok]  <- [cubic_first_fp6_frob_ok]
      - [bw6_fp6_frob_p3_ok]      <- [cubic_first_fp6_frob_p3_ok]
      - [bw6_fp6_conjugate_ok]    <- fp3_copy + fp3_opp
    and feeds them into [bw6_final_exp_ok_wired], leaving only the Fp6
    arithmetic specs (mul/sqr/inv/felem_copy) plus the Fp/Fp3 primitive
    specs and the EnvContains facts as hypotheses.  This matches the
    granularity of [BLS12_PairingTop.bls12_pairing_ok], which likewise
    takes the major arithmetic ops as hypotheses. *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import bedrock2.Syntax.
Require Import bedrock2.Semantics.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.

Require Import Bedrock.Field.Synthesis.Examples.bw6_761_prime.
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_Instances.
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_FinalExp.
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_FinalExp_proof.
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_FrobLibBridge.
Require Import Bedrock.Field.FieldExtensions.PairingFieldOpsCubicFirst.

Import BinInt String.

Local Open Scope string_scope.

Section BW6_FinalExpWired.

  Existing Instances
    Defaults64.default_parameters
    Defaults64.default_parameters_ok.

  Existing Instances
    bw6_prime_params
    bw6_prime_params_ok
    prime_field_parameters
    bw6_Fp_repr
    bw6_Fp_repr_ok
    bw6_Fp3_params bw6_Fp3_repr bw6_Fp3_repr_ok
    bw6_Fp6_params bw6_Fp6_repr bw6_Fp6_repr_ok.

  (* The Frobenius / conjugate callee specs are discharged here; the
     Fp6 arithmetic ops (mul/sqr/inv/felem_copy) stay as hypotheses
     (proved separately in CubicFieldExtensions), per the
     BLS12_PairingTop convention. *)
  Theorem bw6_final_exp_wired_frob :
    forall functions
      (* final-exp-layer EnvContains *)
      (EnvFE : map.get functions "bw6_final_exp" =
        Some (snd bw6_final_exp))
      (EnvEasy : map.get functions "bw6_final_exp_easy" =
        Some (snd bw6_final_exp_easy))
      (EnvHard : map.get functions "bw6_final_exp_hard" =
        Some (snd bw6_final_exp_hard))
      (EnvPowU : map.get functions "bw6_fp6_pow_u" =
        Some (snd bw6_fp6_pow_u))
      (EnvPowAbsU : map.get functions "bw6_fp6_pow_abs_u" =
        Some (snd bw6_fp6_pow_abs_u))
      (* Frobenius library-function EnvContains (library bodies; equal to
         the BW6 frob bodies by construction of the function list) *)
      (EnvFrob : map.get functions "bw6_fp6_frob" =
        Some (snd (cubic_first_fp6_frob (F_representation := bw6_Fp_repr) "bw6_" "")))
      (EnvFrobP2 : map.get functions "bw6_fp6_frob_p2" =
        Some (snd (cubic_first_fp6_frob (F_representation := bw6_Fp_repr) "bw6_" "_p2")))
      (EnvFrobP3 : map.get functions "bw6_fp6_frob_p3" =
        Some (snd (cubic_first_fp6_frob_p3 (F_representation := bw6_Fp_repr) "bw6_")))
      (EnvConj : map.get functions "bw6_fp6_conjugate" =
        Some (snd bw6_fp6_conjugate))
      (* Fp / Fp3 primitive specs (for the frobs and conjugate) *)
      (HFpcopy  : spec_of_Fp_felem_copy (F_representation := bw6_Fp_repr) functions)
      (HFpmul   : spec_of_Fp_mul (F_representation := bw6_Fp_repr) functions)
      (HFp3copy : spec_of_Fp3_felem_copy functions)
      (HFp3opp  : spec_of_Fp3_opp functions)
      (* Fp6 arithmetic (taken as hypotheses, BLS12_PairingTop convention) *)
      (HFp6mul  : spec_of_Fp6_mul functions)
      (HFp6sqr  : spec_of_Fp6_sqr functions)
      (HFp6inv  : spec_of_Fp6_inv functions)
      (HFp6copy : spec_of_Fp6_felem_copy functions),
    spec_of_bw6_final_exp functions.
  Proof.
    intros.
    (* Discharge the three Frobenius bridges from the cubic-first library. *)
    pose proof (bw6_fp6_frob_ok functions
                  (cubic_first_fp6_frob_ok (F_representation := bw6_Fp_repr)
                     (F_representation_ok := bw6_Fp_repr_ok)
                     "bw6_" "" functions EnvFrob HFpcopy HFpmul)) as Hfrob.
    pose proof (bw6_fp6_frob_p2_ok functions
                  (cubic_first_fp6_frob_ok (F_representation := bw6_Fp_repr)
                     (F_representation_ok := bw6_Fp_repr_ok)
                     "bw6_" "_p2" functions EnvFrobP2 HFpcopy HFpmul)) as Hfrob_p2.
    pose proof (bw6_fp6_frob_p3_ok functions
                  (cubic_first_fp6_frob_p3_ok (F_representation := bw6_Fp_repr)
                     (F_representation_ok := bw6_Fp_repr_ok)
                     "bw6_" functions EnvFrobP3 HFpcopy HFpmul)) as Hfrob_p3.
    (* Discharge conjugate. *)
    pose proof (bw6_fp6_conjugate_ok functions EnvConj HFp3copy HFp3opp) as Hconj.
    (* Feed everything into the final-exp wiring. *)
    exact (bw6_final_exp_ok_wired functions EnvFE EnvEasy EnvHard EnvPowU EnvPowAbsU
             HFp6mul HFp6sqr HFp6inv HFp6copy Hconj Hfrob Hfrob_p2 Hfrob_p3).
  Qed.

End BW6_FinalExpWired.
