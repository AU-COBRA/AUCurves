(** * BN254 G1/G2 instantiation of BN_GroupOps. *)

Require Import Coq.ZArith.ZArith.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Field.Synthesis.Examples.bn254_prime_certif.
Require Import Bedrock.Field.Synthesis.Examples.BN_GroupOps.

Local Open Scope Z_scope.

(* BN254 prime as positive *)
Definition bn254_p_pos : positive := bn254_prime_pos.

(* BN254 curve coefficient: y^2 = x^3 + 3 *)
Definition bn254_b : F bn254_p_pos := F.of_Z bn254_p_pos 3.

(* Subgroup order *)
Definition bn254_r : Z := bn254_prime_certif.bn254_r.

(* === G1 instantiation === *)

Definition BN254_G1_aff := G1_aff bn254_p_pos.
Definition BN254_G1_on_curve := G1_on_curve bn254_p_pos bn254_b.
Definition BN254_G1_double := G1_double bn254_p_pos.
Definition BN254_G1_add := G1_add bn254_p_pos.
Definition BN254_G1_neg := G1_neg bn254_p_pos.
Definition BN254_G1_scalar_mul := G1_scalar_mul bn254_p_pos.
Definition BN254_G1_in_subgroup := G1_in_subgroup bn254_p_pos bn254_b.

(* G1 generator: (1, 2) *)
Definition BN254_G1_gen : BN254_G1_aff :=
  G1_pt bn254_p_pos (F.of_Z _ 1) (F.of_Z _ 2).

(* G1 generator is on the curve: 2^2 = 1^3 + 3 mod p *)
Lemma BN254_G1_gen_on_curve : BN254_G1_on_curve BN254_G1_gen.
Proof.
  cbv [BN254_G1_on_curve G1_on_curve BN254_G1_gen bn254_b].
  apply F.eq_to_Z_iff. vm_compute. reflexivity.
Qed.

(* G1 generator is in the subgroup (cofactor = 1, so just on-curve) *)
Lemma BN254_G1_gen_in_subgroup : BN254_G1_in_subgroup BN254_G1_gen.
Proof. exact BN254_G1_gen_on_curve. Qed.

(* === G2 instantiation === *)

(* For BN254: beta = -1, xi = (9, 1) in Fp2.
   Twist coefficient: b' = b/xi = 3 / (9 + u) in Fp2.
   3 / (9+u) = 3*(9-u)/((9+u)(9-u)) = 3*(9-u)/(81+1) = 3*(9-u)/82
   So b'_re = 27/82, b'_im = -3/82 in Fp.
   These are computed as F.of_Z values. *)

Definition bn254_beta : F bn254_p_pos := F.opp (F.of_Z _ 1).

(* Twist coefficient b' = (b'_re, b'_im) = (27/82, -3/82) mod p *)
(* Since beta = -1, fp2_mul (a0,a1) (9,1) = (9*a0 - a1, a0 + 9*a1)
   fp2_inv (9, 1) = ((9, -1)) / norm where norm = 81 + 1 = 82
   So (9 + u)^(-1) = (9/82, -1/82)
   b' = 3 * (9 + u)^(-1) = (27/82, -3/82) *)
Definition BN254_b_twist_re : F bn254_p_pos :=
  F.div (F.of_Z _ 27) (F.of_Z _ 82).
Definition BN254_b_twist_im : F bn254_p_pos :=
  F.opp (F.div (F.of_Z _ 3) (F.of_Z _ 82)).

Definition BN254_G2_aff := G2_aff bn254_p_pos.
Definition BN254_G2_on_twist :=
  G2_on_twist bn254_p_pos bn254_beta BN254_b_twist_re BN254_b_twist_im.
Definition BN254_G2_in_subgroup :=
  G2_in_subgroup bn254_p_pos bn254_beta BN254_b_twist_re BN254_b_twist_im bn254_r.
