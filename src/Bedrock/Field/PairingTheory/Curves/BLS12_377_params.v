(** * BLS12-377 curve parameters.

    BLS12-377 is the inner curve of the Zexe / Celo / Coda zk pipeline.
      seed u  = 0x8508c00000000001  (positive, 64 bits)
      curve E :  y^2 = x^3 + 1
      tower   Fp2 = Fp[u]/(u^2 + 5),  xi = u  (so beta = -5, NOT -1)
      twist   D-twist (standard for BLS12-377 in arkworks / fiat-crypto)

    NOTE: the bedrock2 BLS12_377_Pairing.v Miller loop uses |6u+2| (66 bits)
    as the loop parameter, NOT |u|. That is unusual for a BLS12 curve --
    the standard BLS12 optimal-ate uses just |u|, which is more efficient.
    The 6u+2 choice in bedrock2 looks like a copy-paste from the BN family.
    Recording it as-is here so the params record matches reality; flagged
    as a potential optimisation/correctness target by PLAN_PAIRING_SPECS.md
    Phase 4.

    Because the loop parameter is 6u+2 instead of u, we mark this curve
    with the same Q1 / -Q2 Frobenius corrections that BN curves use, on
    the working hypothesis that the bedrock2 implementation is intentional.
    Verifying this against py_ecc.optimized_bls12_377 is on the to-do list.
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import micromega.Lia.

Require Import Bedrock.Field.Synthesis.Examples.bls12_377_prime_certif.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_377_ScalarReduce.
Require Import Bedrock.Field.PairingTheory.CurveParams.

Local Open Scope Z_scope.

Definition bls12_377_params : CurveParams := {|
  prime_p          := bls12_377_modulus;
  scalar_r         := bls377_r;

  curve_a          := 0;
  curve_b          := 1;

  embedding_degree := 12%nat;

  fp2_beta         := -5;       (* Fp2 = Fp[u] / (u^2 + 5)  *)
  xi_re            := 0;
  xi_im            := 1;        (* xi = u *)

  twist            := Dtwist;

  (* |6u+2|; hi limb 0x3, lo limb 0x1e34800000000008. *)
  loop_abs         := 0x31e34800000000008;
  loop_neg         := false;

  (* See file header: speculative; aligns with the bedrock2 IR's choice
     of 6u+2 as loop parameter (BN-style). May be empty for the standard
     BLS12-377 optimal-ate (which uses |u| and no extras). *)
  optimal_ate_extras :=
    [ {| pi_power := 1; negate := false |}
    ; {| pi_power := 2; negate := true  |}
    ];
|}.
