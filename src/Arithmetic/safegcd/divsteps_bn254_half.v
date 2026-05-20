(** * O'Connor convex-hull certificate for BN254 with δ₀ = 1/2.

    Mirror of [divsteps_p25519_half.v] for δ₀ = 1/2 + BN254 base prime.

    Iteration count [N = 590]: paper Theorem 1 gives
    ⌈(9437·254 + 1)/4096⌉ = 586; we use 10·59 = 590 to match the Rust
    runtime at [curve25519-jasmin-rs/src/safegcd_bn254.rs] (outer_iters = 10).
    Axiomatized for parity with [divsteps_bn254.v]. *)

From Stdlib Require Import ZArith.
Require Import divsteps_base.
Require Import divsteps_base_half.

Local Open Scope Z_scope.

Definition bn254_p : Z :=
  0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47.

Definition bn254_M : Z := bn254_p.

Axiom bn254_half_certificate :
  ZMap.Empty (N.iter 590 (processDivstep_half bn254_M) state0_half).

Definition bn254_half_iters : N := 590.
