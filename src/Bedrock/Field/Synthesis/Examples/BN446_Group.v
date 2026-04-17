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

(* G1 generator placeholder: BN446 has different generator *)
(* Generator omitted *)

(* G1 generator is on the curve: 2^2 = 1^3 + 257 mod p *)
(* BN446 generator: large coordinates, omitted here *)

(* === G2 instantiation === *)

(* For BN446: beta = -1, xi = (2, 3) in Fp2.
   Twist coefficient: b' = b/xi = 257 / (2 + 3u) in Fp2.
   257 / (2+3u) = 257*(2-3u)/((2+3u)(2-3u)) = 257*(2-3u)/(4+9) = 257*(2-3u)/13
   So b'_re = 514/13, b'_im = -771/13 in Fp.
   These are computed as F.of_Z values. *)

Definition bn446_beta : F bn446_p_pos := F.opp (F.of_Z _ 1).

(* Twist coefficient b' = (b'_re, b'_im) = (514/13, -771/13) mod p *)
(* Since beta = -1, fp2_mul (a0,a1) (9,1) = (9*a0 - a1, a0 + 9*a1)
   fp2_inv (9, 1) = ((9, -1)) / norm where norm = 4 + 9 = 13
   So (2 + 3u)^(-1) = (2/13, -3/13)
   b' = 3 * (9 + u)^(-1) = (514/13, -771/13) *)
Definition BN446_b_twist_re : F bn446_p_pos :=
  F.div (F.of_Z _ 514) (F.of_Z _ 13).
Definition BN446_b_twist_im : F bn446_p_pos :=
  F.opp (F.div (F.of_Z _ 771) (F.of_Z _ 13)).

Definition BN446_G2_aff := G2_aff bn446_p_pos.
Definition BN446_G2_on_twist :=
  G2_on_twist bn446_p_pos bn446_beta BN446_b_twist_re BN446_b_twist_im.
Definition BN446_G2_in_subgroup :=
  G2_in_subgroup bn446_p_pos bn446_beta BN446_b_twist_re BN446_b_twist_im bn446_r.
