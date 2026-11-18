(** * BN446 G1/G2 instantiation of BN_GroupOps. *)

Require Import Coq.ZArith.ZArith.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Field.Synthesis.Examples.bn446_prime_certif.
Require Import Bedrock.Field.Synthesis.Examples.BN_GroupOps.

Local Open Scope Z_scope.

(* BN446 prime as positive *)
Definition bn446_p_pos : positive := bn446_prime_pos.

(* BN446 curve coefficient: y^2 = x^3 + 257 *)
Definition bn446_b : F bn446_p_pos := F.of_Z bn446_p_pos 257.

(* Subgroup order *)
Definition bn446_r : Z := bn446_prime_certif.bn446_r.

(* === G1 instantiation === *)

Definition BN446_G1_aff := G1_aff bn446_p_pos.
Definition BN446_G1_on_curve := G1_on_curve bn446_p_pos bn446_b.
Definition BN446_G1_double := G1_double bn446_p_pos.
Definition BN446_G1_add := G1_add bn446_p_pos.
Definition BN446_G1_neg := G1_neg bn446_p_pos.
Definition BN446_G1_scalar_mul := G1_scalar_mul bn446_p_pos.
Definition BN446_G1_in_subgroup := G1_in_subgroup bn446_p_pos bn446_b.

(* G1 generator (-1, 16): 16^2 = (-1)^3 + 257; checked with a G2 generator in
   PairingTheory/BN446ParamsCheck.v *)

(* === G2 instantiation === *)

(* For BN446: beta = -1, xi = (1, 9) in Fp2 (Curves/BN446_params.v).
   Twist coefficient: b' = b/xi = 257 / (1 + 9u) in Fp2.
   257 / (1+9u) = 257*(1-9u)/((1+9u)(1-9u)) = 257*(1-9u)/(1+81) = 257*(1-9u)/82
   So b'_re = 257/82, b'_im = -2313/82 in Fp.
   These are computed as F.of_Z values. *)

Definition bn446_beta : F bn446_p_pos := F.opp (F.of_Z _ 1).

(* Twist coefficient b' = (b'_re, b'_im) = (257/82, -2313/82) mod p *)
Definition BN446_b_twist_re : F bn446_p_pos :=
  F.div (F.of_Z _ 257) (F.of_Z _ 82).
Definition BN446_b_twist_im : F bn446_p_pos :=
  F.opp (F.div (F.of_Z _ 2313) (F.of_Z _ 82)).

Definition BN446_G2_aff := G2_aff bn446_p_pos.
Definition BN446_G2_on_twist :=
  G2_on_twist bn446_p_pos bn446_beta BN446_b_twist_re BN446_b_twist_im.
Definition BN446_G2_in_subgroup :=
  G2_in_subgroup bn446_p_pos bn446_beta BN446_b_twist_re BN446_b_twist_im bn446_r.
