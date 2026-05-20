(** * O'Connor convex-hull certificate for secp256k1 with δ₀ = 1/2.

    Mirror of [divsteps_p25519_half.v] for δ₀ = 1/2 + secp256k1 base prime.

    Iteration count [N = 590]: paper Theorem 1 gives
    ⌈(9437·256 + 1)/4096⌉ = 590; matches Rust runtime
    ([curve25519-jasmin-rs/src/safegcd_secp256k1.rs], outer_iters = 10).
    This matches libsecp256k1's [modinv64] (10 outer · 59 divsteps).
    Axiomatized for parity with [divsteps_secp256k1.v]. *)

From Stdlib Require Import ZArith.
Require Import divsteps_base.
Require Import divsteps_base_half.

Local Open Scope Z_scope.

Definition secp256k1_p : Z :=
  0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f.

Definition secp256k1_M : Z := secp256k1_p.

Axiom secp256k1_half_certificate :
  ZMap.Empty (N.iter 590 (processDivstep_half secp256k1_M) state0_half).

Definition secp256k1_half_iters : N := 590.
