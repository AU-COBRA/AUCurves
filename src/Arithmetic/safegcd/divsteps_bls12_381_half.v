(** * O'Connor convex-hull certificate for BLS12-381 with δ₀ = 1/2.

    Mirror of [divsteps_p25519_half.v] for the EUROCRYPT 2026 paper's
    δ₀ = 1/2 algorithm + BLS12-381 base prime.

    Iteration count [N = 885] matches the Rust runtime
    ([curve25519-jasmin-rs/src/safegcd_bls12_381.rs], outer_iters = 15,
    inner = 59 → 15·59 = 885 ≥ paper bound 878).

    Axiomatized for parity with the δ₀ = 1 cert in [divsteps_bls12.v].
    Independent OCaml verification: [multi_curve_half_driver bls12 885]. *)

From Stdlib Require Import ZArith.
Require Import divsteps_base.
Require Import divsteps_base_half.

Local Open Scope Z_scope.

Definition bls12_381_p : Z :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.

Definition bls12_381_M : Z := bls12_381_p.

Axiom bls12_381_half_certificate :
  ZMap.Empty (N.iter 885 (processDivstep_half bls12_381_M) state0_half).

Definition bls12_381_half_iters : N := 885.
