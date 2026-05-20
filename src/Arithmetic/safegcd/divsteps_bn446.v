(** O'Connor certificate for BN446 divstep convergence.

    Parallel to [divsteps_bls12.v] / [divsteps_bn254.v]: the computation
      State_is_empty(processDivstep^1288(state0)) = true
    is the divsteps-framework claim that 1288 iterations of
    [processDivstep bn446_M] starting from [state0] empties the state,
    which (via [divsteps_bridge]'s generic [oconnor_bridge]) implies
    convergence of the abstract (d,f,g) sequence for any
    coprime-to-[bn446_p] input.

    As with BLS12/BN254, we axiomatize the [ZMap.Empty] result rather
    than sealing it with [vm_cast_no_check] (Qed for that takes many
    minutes due to kernel type-checking the large [N.iter] term).
    Independent OCaml verification of the same cert is available via
    [Arithmetic/safegcd/multi_curve_driver].

    Iteration count: 1288.  Derived from BN446's [mbits = 446] via
      iters = (49 * mbits + 57) / 17 = (49*446+57)/17 = 21911/17 = 1288.
    See [BN446_FpInv.bn446_divstep_iters_val]. *)

From Stdlib Require Import ZArith.
Require Import divsteps_base.

Definition bn446_p : Z :=
  0x2400000000000000002400000002d00000000d800000021c0000001800000000870000000b0400000057c00000015c000000132000000067.

Definition bn446_M : Z := bn446_p.

Axiom bn446_certificate :
  ZMap.Empty (N.iter 1288 (processDivstep bn446_M) state0).

Definition bn446_iters : N := 1288.
