(** * BN254OptimalAteBridge: [BN254OptimalAte.bn254_optimal_ate] is the pairing of
    [MillerLoopWP.bn254_optimal_ate_spec] and of [BN254_PairingRustConcrete.bn254_optimal_ate_spec]
    at the Frobenius constants of [FrobConstants].  A separate file because both of those pull in
    much more than [BN254OptimalAte.v] needs.  No [Admitted], no [Axiom]. *)

From Stdlib Require Import ZArith.ZArith.

Require Import Bedrock.Field.PairingTheory.CurveParams.
Require Import Bedrock.Field.PairingTheory.Curves.BN254_params.
Require Import Bedrock.Field.PairingTheory.ZModTower.
Require Import Bedrock.Field.PairingTheory.FrobConstants.
Require Bedrock.Field.PairingTheory.MillerLoopWP.
Require Bedrock.BN254_PairingRustConcrete.
Require Import Bedrock.Field.PairingTheory.BN254OptimalAte.

Local Open Scope Z_scope.

Lemma bn254_optimal_ate_is_spec (Px Py : Z) (Qx Qy : Fp2_Z) :
  bn254_optimal_ate Px Py Qx Qy =
  MillerLoopWP.bn254_optimal_ate_spec
    (gamma1_val bn254_params) (gamma_y_val bn254_params) (gamma1_p2_val bn254_params)
    Px Py Qx Qy.
Proof.
  rewrite bn254_gamma1_eq, bn254_gamma_y_eq, bn254_gamma1_p2_eq.
  unfold bn254_optimal_ate, MillerLoopWP.bn254_optimal_ate_spec. cbv zeta. reflexivity.
Qed.

Lemma bn254_optimal_ate_is_rust_spec (Px Py : Z) (Qx Qy : Fp2_Z) :
  bn254_optimal_ate Px Py Qx Qy =
  BN254_PairingRustConcrete.bn254_optimal_ate_spec
    (gamma1_val bn254_params) (gamma_y_val bn254_params) (gamma1_p2_val bn254_params)
    Px Py Qx Qy.
Proof.
  rewrite bn254_gamma1_eq, bn254_gamma_y_eq, bn254_gamma1_p2_eq.
  unfold bn254_optimal_ate, BN254_PairingRustConcrete.bn254_optimal_ate_spec.
  (* the copy names p and xi by local constants; xi is the literal (9, 1) there *)
  assert (Hxi : BN254_PairingRustConcrete.bn254_xi_val = (xi_re bn254_params, xi_im bn254_params))
    by reflexivity.
  assert (Hp : BN254_PairingRustConcrete.bn254_p_val = prime_p bn254_params) by reflexivity.
  rewrite Hxi, Hp. reflexivity.
Qed.
