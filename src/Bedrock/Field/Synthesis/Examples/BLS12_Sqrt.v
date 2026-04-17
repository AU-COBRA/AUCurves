(** * BLS12-381 square root exponent limbs for bedrock2 implementation.

    The square root in Fp uses the formula sqrt(a) = a^((p+1)/4) mod p,
    valid because p ≡ 3 (mod 4).

    This file provides the exponent (p+1)/4 as a list of 64-bit words
    for use in a bedrock2 square-and-multiply implementation. *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
Import ListNotations.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_Legendre.
Local Open Scope Z_scope.

(** The exponent (p+1)/4 as 6 × 64-bit words, least significant first. *)
Definition bls12_sqrt_exp_limbs : list Z :=
  [ 0xee7fbfffffffeaab
  ; 0x07aaffffac54ffff
  ; 0xd9cc34a83dac3d89
  ; 0xd91dd2e13ce144af
  ; 0x92c6e9ed90d2eb35
  ; 0x0680447a8e5ff9a6
  ].

(** Number of limbs *)
Definition bls12_sqrt_exp_nlimbs : nat := 6.

(** Total bit length of the exponent *)
Definition bls12_sqrt_exp_bitlen : Z := 379.

Lemma bls12_sqrt_exp_bitlen_correct :
  Z.log2 bls12_sqrt_exp + 1 = bls12_sqrt_exp_bitlen.
Proof. vm_compute. reflexivity. Qed.
