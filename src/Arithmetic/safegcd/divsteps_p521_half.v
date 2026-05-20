(** * O'Connor convex-hull certificate for NIST P-521 with δ₀ = 1/2.

    Mirror of [divsteps_p25519_half.v] for δ₀ = 1/2 + P-521 base prime.

    Iteration count [N = 1239]: paper Theorem 1 gives
    ⌈(9437·521 + 1)/4096⌉ = 1201; we use 21·59 = 1239 to match the Rust
    runtime at [curve25519-jasmin-rs/src/safegcd_p521.rs] (outer_iters = 21).
    Axiomatized for parity with [divsteps_p521.v]. *)

From Stdlib Require Import ZArith.
Require Import divsteps_base.
Require Import divsteps_base_half.

Local Open Scope Z_scope.

Definition p521_p : Z :=
  0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff.

Definition p521_M : Z := p521_p.

Axiom p521_half_certificate :
  ZMap.Empty (N.iter 1239 (processDivstep_half p521_M) state0_half).

Definition p521_half_iters : N := 1239.
