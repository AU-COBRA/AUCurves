(** * O'Connor convex-hull certificate for NIST P-256 with δ₀ = 1/2.

    Mirror of [divsteps_p25519_half.v] for δ₀ = 1/2 + P-256 base prime.

    Iteration count [N = 590]: paper Theorem 1 gives
    ⌈(9437·256 + 1)/4096⌉ = 590; matches Rust runtime
    ([curve25519-jasmin-rs/src/safegcd_p256.rs], outer_iters = 10).
    Axiomatized for parity with [divsteps_p256.v]. *)

From Stdlib Require Import ZArith.
Require Import divsteps_base.
Require Import divsteps_base_half.

Local Open Scope Z_scope.

Definition p256_p : Z :=
  0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff.

Definition p256_M : Z := p256_p.

Axiom p256_half_certificate :
  ZMap.Empty (N.iter 590 (processDivstep_half p256_M) state0_half).

Definition p256_half_iters : N := 590.
