(** * O'Connor convex-hull certificate for BW6-761 with δ₀ = 1/2.

    Mirror of [divsteps_p25519_half.v] for δ₀ = 1/2 + BW6-761 base prime.

    Iteration count [N = 1770]: paper Theorem 1 gives
    ⌈(9437·761 + 1)/4096⌉ = 1754; we use 30·59 = 1770 to match the Rust
    runtime at [curve25519-jasmin-rs/src/safegcd_bw6_761.rs] (outer_iters = 30).
    Axiomatized for parity with [divsteps_bw6_761.v]. *)

From Stdlib Require Import ZArith.
Require Import divsteps_base.
Require Import divsteps_base_half.

Local Open Scope Z_scope.

Definition bw6_761_p : Z :=
  0x122e824fb83ce0ad187c94004faff3eb926186a81d14688528275ef8087be41707ba638e584e91903cebaff25b423048689c8ed12f9fd9071dcd3dc73ebff2e98a116c25667a8f8160cf8aeeaf0a437e6913e6870000082f49d00000000008b.

Definition bw6_761_M : Z := bw6_761_p.

Axiom bw6_761_half_certificate :
  ZMap.Empty (N.iter 1770 (processDivstep_half bw6_761_M) state0_half).

Definition bw6_761_half_iters : N := 1770.
