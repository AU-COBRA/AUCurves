(** * O'Connor convex-hull certificate for Vesta with δ₀ = 1/2.

    Mirror of [divsteps_p25519_half.v] for δ₀ = 1/2 + Vesta base prime.

    Iteration count [N = 590]: paper Theorem 1 gives
    ⌈(9437·255 + 1)/4096⌉ = 588; we use 10·59 = 590 to match the Rust
    runtime at [curve25519-jasmin-rs/src/safegcd_vesta.rs] (outer_iters = 10).
    Axiomatized for parity with [divsteps_vesta.v]. *)

From Stdlib Require Import ZArith.
Require Import divsteps_base.
Require Import divsteps_base_half.

Local Open Scope Z_scope.

Definition vesta_p : Z :=
  0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001.

Definition vesta_M : Z := vesta_p.

Axiom vesta_half_certificate :
  ZMap.Empty (N.iter 590 (processDivstep_half vesta_M) state0_half).

Definition vesta_half_iters : N := 590.
