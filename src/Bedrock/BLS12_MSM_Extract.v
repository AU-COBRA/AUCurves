(** * BLS12-381 MSM extraction driver.

    Once the WP proof for [msm_bls12] is complete (in BLS12_MSM.v),
    this file extracts it via:
      1. ToSafeRustBody.v → safe Rust (equivalent to msm.rs prototype)
      2. ToJasmin.v → Jasmin → jasminc → x86-64 assembly

    Location: AUCurves/src/Bedrock/ (we control this).
    Mirrors fiat-crypto's BLS12_wNAF_Extract.v structure but lives
    in AUCurves per repo-separation policy.

    The extracted Rust code calls the same verified Fp leaf functions
    (bls12_add, bls12_sub, fiat_bls12_381_p_mul, fiat_bls12_381_p_square)
    as the hand-written bls12-jasmin-rs/src/msm.rs, producing
    semantically equivalent output.

    Current status: SCAFFOLD. The WP proof is the blocking step.
    The extraction machinery (ToSafeRustBody, ToJasmin, SafeRustSimulation)
    is fully verified and ready to use — it already extracts 47 BN254
    tower functions and the full BLS12-381 tower.

    Plan:
      1. Write the bedrock2 ExprImp body + WP proof in BLS12_MSM.v  [TODO]
      2. Instantiate this driver with BLS12-381 parameters            [this file]
      3. Run ToSafeRustBody to get safe Rust                          [automatic]
      4. Diff against bls12-jasmin-rs/src/msm.rs                      [validation]
*)

(** Placeholder — uncomment when BLS12_MSM.v is ready:

Require Import Bedrock.BLS12_MSM.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.ToSafeRustBody.
Require Import Crypto.Bedrock.Field.FieldExtensions.ToJasmin.

(* Instantiate at BLS12-381: 6 limbs, c = 9 *)
Definition bls12_msm_func : Syntax.func :=
  msm_func bls12_field_parameters bls12_field_representation 9.

(* Extract to safe Rust *)
Definition bls12_msm_rust : string :=
  btranslate_to_string "bls12_msm" bls12_msm_func.

(* Extract to Jasmin *)
Definition bls12_msm_jasmin : string :=
  to_jasmin_string "bls12_msm" bls12_msm_func.

*)
