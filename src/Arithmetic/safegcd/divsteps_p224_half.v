(** * O'Connor convex-hull certificate for NIST P-224 with δ₀ = 1/2.

    Mirror of [divsteps_p25519_half.v] for δ₀ = 1/2 + P-224 base prime.

    Iteration count [N = 590]: paper Theorem 1 gives
    ⌈(9437·224 + 1)/4096⌉ = 517; we use 10·59 = 590 to match the Rust
    runtime at [curve25519-jasmin-rs/src/safegcd_p224.rs] (outer_iters = 10).
    Axiomatized for parity with [divsteps_p224.v]. *)

From Stdlib Require Import ZArith.
Require Import divsteps_base.
Require Import divsteps_base_half.

Local Open Scope Z_scope.

Definition p224_p : Z :=
  0xffffffffffffffffffffffffffffffff000000000000000000000001.

Definition p224_M : Z := p224_p.

Axiom p224_half_certificate :
  ZMap.Empty (N.iter 590 (processDivstep_half p224_M) state0_half).

Definition p224_half_iters : N := 590.
