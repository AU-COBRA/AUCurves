(** * O'Connor convex-hull certificate for BN256 with δ₀ = 1/2.

    Mirror of [divsteps_p25519_half.v] for δ₀ = 1/2 + BN256 base prime.

    Iteration count [N = 590]: paper Theorem 1 gives
    ⌈(9437·256 + 1)/4096⌉ = 590; matches Rust runtime
    ([curve25519-jasmin-rs/src/safegcd_bn256.rs], outer_iters = 10).
    Axiomatized for parity with [divsteps_bn256.v]. *)

From Stdlib Require Import ZArith.
Require Import divsteps_base.
Require Import divsteps_base_half.

Local Open Scope Z_scope.

Definition bn256_p : Z :=
  0x8fb501e34aa387f9aa6fecb86184dc21ee5b88d120b5b59e185cac6c5e089667.

Definition bn256_M : Z := bn256_p.

Axiom bn256_half_certificate :
  ZMap.Empty (N.iter 590 (processDivstep_half bn256_M) state0_half).

Definition bn256_half_iters : N := 590.
