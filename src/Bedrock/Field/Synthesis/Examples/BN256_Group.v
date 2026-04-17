(** * BN256 G1/G2 instantiation of BN_GroupOps. *)

Require Import Coq.ZArith.ZArith.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Field.Synthesis.Examples.bn256_prime_certif.
Require Import Bedrock.Field.Synthesis.Examples.BN_GroupOps.

Local Open Scope Z_scope.

(* BN256 prime as positive *)
Definition bn256_p_pos : positive := bn256_prime_pos.

(* BN256 curve coefficient: y^2 = x^3 + 3 *)
Definition bn256_b : F bn256_p_pos := F.of_Z bn256_p_pos 3.

(* Subgroup order *)
Definition bn256_r : Z := bn256_prime_certif.bn256_r.

(* === G1 instantiation === *)

Definition BN256_G1_aff := G1_aff bn256_p_pos.
Definition BN256_G1_on_curve := G1_on_curve bn256_p_pos bn256_b.
Definition BN256_G1_double := G1_double bn256_p_pos.
Definition BN256_G1_add := G1_add bn256_p_pos.
Definition BN256_G1_neg := G1_neg bn256_p_pos.
Definition BN256_G1_scalar_mul := G1_scalar_mul bn256_p_pos.
Definition BN256_G1_in_subgroup := G1_in_subgroup bn256_p_pos bn256_b.

(* G1 generator: (1, 2) *)
Definition BN256_G1_gen : BN256_G1_aff :=
  G1_pt bn256_p_pos (F.of_Z _ 1) (F.of_Z _ 2).

(* G1 generator is on the curve: 2^2 = 1^3 + 3 mod p *)
Lemma BN256_G1_gen_on_curve : BN256_G1_on_curve BN256_G1_gen.
Proof.
  cbv [BN256_G1_on_curve G1_on_curve BN256_G1_gen bn256_b].
  apply F.eq_to_Z_iff. vm_compute. reflexivity.
Qed.

(* G1 generator is in the subgroup (cofactor = 1, so just on-curve) *)
Lemma BN256_G1_gen_in_subgroup : BN256_G1_in_subgroup BN256_G1_gen.
Proof. exact BN256_G1_gen_on_curve. Qed.

(* === G2 instantiation === *)

(* For BN256: beta = -1, xi = (3, 1) in Fp2.
   Twist coefficient: b' = b/xi = 3 / (3 + u) in Fp2.
   3 / (9+u) = 3*(3-u)/((3+u)(3-u)) = 3*(3-u)/(9+1) = 3*(3-u)/10
   So b'_re = 9/10, b'_im = -3/10 in Fp.
   These are computed as F.of_Z values. *)

Definition bn256_beta : F bn256_p_pos := F.opp (F.of_Z _ 1).

(* Twist coefficient b' = (b'_re, b'_im) = (9/10, -3/10) mod p *)
(* Since beta = -1, fp2_mul (a0,a1) (9,1) = (9*a0 - a1, a0 + 9*a1)
   fp2_inv (9, 1) = ((3, -1)) / norm where norm = 9 + 1 = 10
   So (3 + u)^(-1) = (3/10, -1/10)
   b' = 3 * (9 + u)^(-1) = (9/10, -3/10) *)
Definition BN256_b_twist_re : F bn256_p_pos :=
  F.div (F.of_Z _ 9) (F.of_Z _ 10).
Definition BN256_b_twist_im : F bn256_p_pos :=
  F.opp (F.div (F.of_Z _ 3) (F.of_Z _ 10)).

Definition BN256_G2_aff := G2_aff bn256_p_pos.
Definition BN256_G2_on_twist :=
  G2_on_twist bn256_p_pos bn256_beta BN256_b_twist_re BN256_b_twist_im.
Definition BN256_G2_in_subgroup :=
  G2_in_subgroup bn256_p_pos bn256_beta BN256_b_twist_re BN256_b_twist_im bn256_r.
