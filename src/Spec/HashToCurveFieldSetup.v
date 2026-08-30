(** * Field setup for hash-to-curve proofs.

    Connects [p_pos] from HashToCurve.v to the BLS12-381 prime
    certificate, registers [ring]/[field] tactics for [F p_pos],
    and provides basic nonzero / nonsquare lemmas needed by the
    SWU and isogeny correctness proofs.
*)

From Stdlib Require Import ZArith BinPos List Bool.
From Stdlib Require Import Znumtheory.
Import ListNotations.

Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Spec.HashToCurve.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime_certif.

From Coq Require Export Ring_theory Field_theory Field_tac.
Require Crypto.Algebra.Hierarchy Crypto.Algebra.Field.

Local Open Scope Z_scope.

(* ================================================================== *)
(** * Connecting p_pos to the prime certificate                        *)
(* ================================================================== *)

(** p_pos from HashToCurve.v equals bls12_381_modulus from the certificate. *)
Lemma p_pos_eq_modulus : Z.pos p_pos = bls12_381_modulus.
Proof. vm_compute. reflexivity. Qed.

(** p_pos is prime. *)
Lemma p_pos_prime : prime (Z.pos p_pos).
Proof. rewrite p_pos_eq_modulus. exact prime_bls12_381. Qed.

(** p = 3 (mod 4), enabling the simple sqrt formula. *)
Lemma p_pos_mod4 : Z.pos p_pos mod 4 = 3.
Proof. vm_compute. reflexivity. Qed.

(** p > 2. *)
Lemma p_pos_gt_2 : (2 < Z.pos p_pos)%Z.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(** * Field type and notations (re-exported for proof files)           *)
(* ================================================================== *)

Notation Fp := (F p_pos).
Notation "x +f y" := (@F.add p_pos x y) (at level 50, left associativity).
Notation "x *f y" := (@F.mul p_pos x y) (at level 40, left associativity).
Notation "x -f y" := (@F.sub p_pos x y) (at level 50, left associativity).
Notation "-f x"   := (@F.opp p_pos x) (at level 35, right associativity).
Notation "0f"     := (@F.zero p_pos).
Notation "1f"     := (@F.one p_pos).

(* ================================================================== *)
(** * Ring and field tactic registration                                *)
(* ================================================================== *)

(** Field instance for F p_pos. *)
#[local] Instance Fp_field : @Algebra.Hierarchy.field Fp Logic.eq 0f 1f
  F.opp F.add F.sub F.mul F.inv F.div
  := @F.field_modulo p_pos p_pos_prime.

(** Register ring tactic. *)
Add Ring Fp_ring : (F.ring_theory p_pos)
  (morphism (F.ring_morph p_pos),
   constants [F.is_constant],
   div (F.morph_div_theory p_pos),
   power_tac (F.power_theory p_pos) [F.is_pow_constant]).

(** Register field tactic. *)
Add Field Fp_field_tac :
  (Algebra.Field.field_theory_for_stdlib_tactic(T:=Fp))
  (morphism (F.ring_morph p_pos),
   constants [F.is_constant],
   div (F.morph_div_theory p_pos),
   power_tac (F.power_theory p_pos) [F.is_pow_constant]).

(* ================================================================== *)
(** * Basic field lemmas                                                *)
(* ================================================================== *)

Lemma Fp_inv_nonzero : forall x : Fp, x <> 0f -> F.inv x *f x = 1f.
Proof.
  intros x Hx. apply Algebra.Hierarchy.left_multiplicative_inverse. exact Hx.
Qed.

Lemma Fp_mul_inv_r : forall x : Fp, x <> 0f -> x *f F.inv x = 1f.
Proof.
  intros x Hx.
  replace (x *f F.inv x) with (F.inv x *f x) by ring.
  exact (Fp_inv_nonzero x Hx).
Qed.

(** Negation preserves squares: (-y)^2 = y^2. *)
Lemma opp_sqr : forall y : Fp, (-f y) *f (-f y) = y *f y.
Proof. intros. ring. Qed.

(* ================================================================== *)
(** * Nonzero constants                                                 *)
(* ================================================================== *)

(** iso_A (the A coefficient of the isogenous curve E') is nonzero. *)
Lemma iso_A_nonzero : iso_A <> 0f.
Proof.
  intro H. apply (f_equal F.to_Z) in H.
  (* Reduce to plain Z BEFORE computing.  [F p_pos] is a sigma type
     carrying a proof component, so [vm_compute in H] normalises that
     proof term as well as the value -- over a 381-bit modulus that is
     where the gigabytes go.  [F.to_Z_of_Z] rewrites
     [F.to_Z (F.of_Z m z)] to [z mod m], after which the computation is
     ordinary Z arithmetic. *)
  unfold iso_A in H.
  rewrite ModularArithmeticTheorems.F.to_Z_of_Z in H.
  vm_compute in H. discriminate.
Qed.

(** iso_B (the B coefficient of the isogenous curve E') is nonzero. *)
Lemma iso_B_nonzero : iso_B <> 0f.
Proof.
  intro H. apply (f_equal F.to_Z) in H.
  (* Reduce to plain Z BEFORE computing.  [F p_pos] is a sigma type
     carrying a proof component, so [vm_compute in H] normalises that
     proof term as well as the value -- over a 381-bit modulus that is
     where the gigabytes go.  [F.to_Z_of_Z] rewrites
     [F.to_Z (F.of_Z m z)] to [z mod m], after which the computation is
     ordinary Z arithmetic. *)
  unfold iso_B in H.
  rewrite ModularArithmeticTheorems.F.to_Z_of_Z in H.
  vm_compute in H. discriminate.
Qed.

(** swu_Z = 11 is nonzero. *)
Lemma swu_Z_nonzero : swu_Z <> 0f.
Proof.
  intro H. apply (f_equal F.to_Z) in H.
  (* Reduce to plain Z BEFORE computing.  [F p_pos] is a sigma type
     carrying a proof component, so [vm_compute in H] normalises that
     proof term as well as the value -- over a 381-bit modulus that is
     where the gigabytes go.  [F.to_Z_of_Z] rewrites
     [F.to_Z (F.of_Z m z)] to [z mod m], after which the computation is
     ordinary Z arithmetic. *)
  unfold swu_Z in H.
  rewrite ModularArithmeticTheorems.F.to_Z_of_Z in H.
  vm_compute in H. discriminate.
Qed.

(* ================================================================== *)
(** * Quadratic residuosity of constants                                *)
(* ================================================================== *)

(** Z = 11 is a quadratic non-residue mod p.
    Verified by computing 11^((p-1)/2) mod p = p-1 (i.e., -1). *)
Lemma swu_Z_nonsquare : is_square swu_Z = false.
Proof. vm_compute. reflexivity. Qed.

(** -1 is a quadratic non-residue (since p = 3 mod 4). *)
Lemma minus_one_nonsquare : is_square (-f 1f) = false.
Proof. vm_compute. reflexivity. Qed.

(** 0 is a square. *)
Lemma zero_is_square : is_square 0f = true.
Proof. vm_compute. reflexivity. Qed.
