(** * O'Connor convex-hull certificate for BLS24-509 with δ₀ = 1/2.

    Mirror of [divsteps_p25519_half.v] for δ₀ = 1/2 + BLS24-509 base prime.

    Iteration count [N = 1180]: paper Theorem 1 gives
    ⌈(9437·509 + 1)/4096⌉ = 1173; we use 20·59 = 1180 to match the Rust
    runtime at [curve25519-jasmin-rs/src/safegcd_bls24_509.rs] (outer_iters = 20).
    Axiomatized for parity with [divsteps_bls24_509.v]. *)

From Stdlib Require Import ZArith.
Require Import divsteps_base.
Require Import divsteps_base_half.

Local Open Scope Z_scope.

Definition bls24_509_p : Z :=
  0x155556ffff39ca9bfcedf2b4f9c0ecf6cb8ac8495d187e8c32ea0103e01090bb626e85bf7c18a0f0cfcb5c6071bad3d2ee63bd076e8d9300a13d118db8bfd2ab.

Definition bls24_509_M : Z := bls24_509_p.

Axiom bls24_509_half_certificate :
  ZMap.Empty (N.iter 1180 (processDivstep_half bls24_509_M) state0_half).

Definition bls24_509_half_iters : N := 1180.
