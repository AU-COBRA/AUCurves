(** * O'Connor convex-hull certificate for NIST P-384 with δ₀ = 1/2.

    Mirror of [divsteps_p25519_half.v] for δ₀ = 1/2 + P-384 base prime.

    Iteration count [N = 885]: paper Theorem 1 gives
    ⌈(9437·384 + 1)/4096⌉ = 885; matches Rust runtime
    ([curve25519-jasmin-rs/src/safegcd_p384.rs], outer_iters = 15).
    Axiomatized for parity with [divsteps_p384.v]. *)

From Stdlib Require Import ZArith.
Require Import divsteps_base.
Require Import divsteps_base_half.

Local Open Scope Z_scope.

Definition p384_p : Z :=
  0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff.

Definition p384_M : Z := p384_p.

Axiom p384_half_certificate :
  ZMap.Empty (N.iter 885 (processDivstep_half p384_M) state0_half).

Definition p384_half_iters : N := 885.
