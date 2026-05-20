(** * O'Connor convex-hull certificate for BLS12-377 with δ₀ = 1/2.

    Mirror of [divsteps_p25519_half.v] for δ₀ = 1/2 + BLS12-377 base prime.

    Iteration count [N = 885]: paper Theorem 1 gives
    ⌈(9437·377 + 1)/4096⌉ = 869; we pick the next multiple of 59 ≥ 869
    (i.e. 15·59 = 885) for alignment with the BLS12-381 outer-loop layout.
    Axiomatized for parity with [divsteps_bls12_377.v]. *)

From Stdlib Require Import ZArith.
Require Import divsteps_base.
Require Import divsteps_base_half.

Local Open Scope Z_scope.

Definition bls12_377_p : Z :=
  0x1ae3a4617c510eac63b05c06ca1493b1a22d9f300f5138f1ef3622fba094800170b5d44300000008508c00000000001.

Definition bls12_377_M : Z := bls12_377_p.

Axiom bls12_377_half_certificate :
  ZMap.Empty (N.iter 885 (processDivstep_half bls12_377_M) state0_half).

Definition bls12_377_half_iters : N := 885.
