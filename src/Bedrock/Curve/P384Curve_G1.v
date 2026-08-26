(* P-384 (NIST secp384r1) curve integration into AUCurves Montgomery framework.
   Instantiates MontgomeryCurveSpecs for y^2 = x^3 - 3x + b over Fp384.
   Port of P256Curve_G1.v: 6 limbs of 64 bits instead of 4. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Theory.WordByWordMontgomery.MontgomeryCurveSpecs.
Require Import Theory.WordByWordMontgomery.MontgomeryRingTheory.

Local Open Scope Z_scope.
Local Coercion Z.of_nat : nat >-> Z.

(* P-384 prime: p = 2^384 - 2^128 - 2^96 + 2^32 - 1 *)
Local Definition m := Eval vm_compute in (2^384 - 2^128 - 2^96 + 2^32 - 1)%Z.
Local Definition bw := 64.
Local Definition n := 6%nat.

(* Curve equation: y^2 = x^3 + a*x + b where a = -3 mod m.
   b is the FIPS 186-4 / SEC2 secp384r1 coefficient; its little-endian
   u64 limbs match B_CANON in p384-safe-rust/src/group.rs. *)
Local Definition a := Eval vm_compute in ((-3) mod m)%Z.
Local Definition b_coeff := Eval vm_compute in
  (0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef mod m)%Z.
Local Definition three_b := Eval vm_compute in (3 * b_coeff mod m)%Z.

(* Montgomery parameters — computed from fiat-crypto *)
Local Notation r := (MontgomeryRingTheory.r bw).
(* m' = modinv(-m, 2^64).  For P-384: m ≡ 2^32 - 1 mod 2^64, and
   modinv(-(2^32 - 1), 2^64) = 2^32 + 1. *)
Local Definition m' : Z := 4294967297.
(* r' = modinv(2^64, m). *)
Local Definition r' : Z :=
  9173994466096273082364193663603369469355812071275829017307008127494733112176079729898163604637719575134209.

(* Correctness lemmas for Montgomery parameters *)
Lemma a_small : a = a mod m.
Proof. vm_compute. reflexivity. Qed.

Lemma three_b_small : three_b = three_b mod m.
Proof. vm_compute. reflexivity. Qed.

Lemma r'_correct : (r * r') mod m = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma m'_correct : (m * m') mod r = (-1) mod r.
Proof. vm_compute. reflexivity. Qed.

Lemma bw_big : 0 < bw.
Proof. unfold bw. lia. Qed.

Lemma n_nz : n <> 0%nat.
Proof. cbv. discriminate. Qed.

Lemma m_small : m < r ^ (Z.of_nat n).
Proof. vm_compute. reflexivity. Qed.

Lemma m_big : 1 < m.
Proof. unfold m. vm_compute. reflexivity. Qed.

(* Instantiate Montgomery curve specs for P-384 *)
Definition p384_three_b_list := MontgomeryCurveSpecs.three_b_list bw n three_b.
Definition p384_three_b_mont := Eval vm_compute in
  (MontgomeryCurveSpecs.three_b_mont_list m bw n m' three_b).
Definition p384_a_list := MontgomeryCurveSpecs.a_list bw n a.
Definition p384_a_mont_list := Eval vm_compute in
  (MontgomeryCurveSpecs.a_mont_list m bw n m' a).

(* Validity lemmas *)
Lemma p384_three_b_list_valid : WordByWordMontgomery.valid bw n m p384_three_b_list.
Proof.
  apply three_b_list_valid; try assumption.
  - exact three_b_small.
  - exact bw_big.
  - exact n_nz.
  - exact m_small.
  - exact m_big.
Qed.

Lemma p384_three_b_mont_valid : WordByWordMontgomery.valid bw n m p384_three_b_mont.
Proof.
  unfold p384_three_b_mont. cbv; repeat split; auto; intros; discriminate.
Qed.

Lemma p384_a_list_valid : WordByWordMontgomery.valid bw n m p384_a_list.
Proof.
  apply a_list_valid; try assumption.
  - exact a_small.
  - exact bw_big.
  - exact n_nz.
  - exact m_small.
  - exact m_big.
Qed.

(* Gallina specification of P-384 point addition (projective coordinates) *)
Definition P384_add_Gallina_spec :=
  BLS12_add_Gallina_spec m bw n m' a three_b.

(* Note: P-384 has a = -3 (nonzero), so the a=0 specialization does NOT apply.
   The generic BLS12_add_Gallina_spec handles arbitrary a. *)
