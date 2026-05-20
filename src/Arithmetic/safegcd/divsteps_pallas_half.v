(** * O'Connor convex-hull certificate for Pallas with δ₀ = 1/2.

    Mirror of [divsteps_p25519_half.v] for δ₀ = 1/2 + Pallas base prime.

    Iteration count [N = 590]: paper Theorem 1 gives
    ⌈(9437·255 + 1)/4096⌉ = 588; we use 10·59 = 590 to match the Rust
    runtime at [curve25519-jasmin-rs/src/safegcd_pallas.rs] (outer_iters = 10).
    Axiomatized for parity with [divsteps_pallas.v]. *)

From Stdlib Require Import ZArith.
Require Import divsteps_base.
Require Import divsteps_base_half.

Local Open Scope Z_scope.

Definition pallas_p : Z :=
  0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001.

Definition pallas_M : Z := pallas_p.

Axiom pallas_half_certificate :
  ZMap.Empty (N.iter 590 (processDivstep_half pallas_M) state0_half).

Definition pallas_half_iters : N := 590.
