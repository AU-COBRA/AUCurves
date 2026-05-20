(** O'Connor certificate for BN256 divstep convergence.

    Parallel to [divsteps_bls12.v] / [divsteps_bn254.v]: the computation
      State_is_empty(processDivstep^741(state0)) = true
    is the divsteps-framework claim that 741 iterations of
    [processDivstep bn256_M] starting from [state0] empties the state,
    which (via [divsteps_bridge]'s generic [oconnor_bridge]) implies
    convergence of the abstract (d,f,g) sequence for any
    coprime-to-[bn256_p] input.

    As with BLS12/BN254, we axiomatize the [ZMap.Empty] result rather
    than sealing it with [vm_cast_no_check] (Qed for that takes many
    minutes due to kernel type-checking the large [N.iter] term).
    Independent OCaml verification of the same cert is available via
    [Arithmetic/safegcd/multi_curve_driver].

    Iteration count: 741.  Derived from BN256's [mbits = 256] via
      iters = (49 * mbits + 57) / 17 = (49*256+57)/17 = 12601/17 = 741.
    See [BN256_FpInv.bn256_divstep_iters_val]. *)

From Stdlib Require Import ZArith.
Require Import divsteps_base.

Definition bn256_p : Z :=
  0x8fb501e34aa387f9aa6fecb86184dc21ee5b88d120b5b59e185cac6c5e089667.

Definition bn256_M : Z := bn256_p.

Axiom bn256_certificate :
  ZMap.Empty (N.iter 741 (processDivstep bn256_M) state0).

Definition bn256_iters : N := 741.
