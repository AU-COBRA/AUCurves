(** * O'Connor convex-hull certificate for BN446 with δ₀ = 1/2.

    Mirror of [divsteps_p25519_half.v] for δ₀ = 1/2 + BN446 base prime.

    Iteration count [N = 1062]: paper Theorem 1 gives
    ⌈(9437·446 + 1)/4096⌉ = 1028; we use 18·59 = 1062 to match the Rust
    runtime at [curve25519-jasmin-rs/src/safegcd_bn446.rs] (outer_iters = 18).
    Axiomatized for parity with [divsteps_bn446.v]. *)

From Stdlib Require Import ZArith.
Require Import divsteps_base.
Require Import divsteps_base_half.

Local Open Scope Z_scope.

Definition bn446_p : Z :=
  0x2400000000000000002400000002d00000000d800000021c0000001800000000870000000b0400000057c00000015c000000132000000067.

Definition bn446_M : Z := bn446_p.

Axiom bn446_half_certificate :
  ZMap.Empty (N.iter 1062 (processDivstep_half bn446_M) state0_half).

Definition bn446_half_iters : N := 1062.
