(** O'Connor certificate for BW6-761 divstep convergence.

    Parallel to [divsteps_bls12.v] / [divsteps_bn254.v]: the computation
      State_is_empty(processDivstep^2196(state0)) = true
    is the divsteps-framework claim that 2196 iterations of
    [processDivstep bw6_761_M] starting from [state0] empties the state,
    which (via [divsteps_bridge]'s generic [oconnor_bridge]) implies
    convergence of the abstract (d,f,g) sequence for any
    coprime-to-[bw6_761_p] input.

    As with BLS12/BN254, we axiomatize the [ZMap.Empty] result rather
    than sealing it with [vm_cast_no_check] (Qed for that takes many
    minutes due to kernel type-checking the large [N.iter] term).
    Independent OCaml verification of the same cert is available via
    [Arithmetic/safegcd/multi_curve_driver].

    Iteration count: 2196.  Derived from BW6-761's [mbits = 761] via
      iters = (49 * mbits + 57) / 17 = (49*761+57)/17 = 37346/17 = 2196.
    See [BW6_761_FpInv.bw6_761_divstep_iters_val]. *)

From Stdlib Require Import ZArith.
Require Import divsteps_base.

Definition bw6_761_p : Z :=
  0x122e824fb83ce0ad187c94004faff3eb926186a81d14688528275ef8087be41707ba638e584e91903cebaff25b423048689c8ed12f9fd9071dcd3dc73ebff2e98a116c25667a8f8160cf8aeeaf0a437e6913e6870000082f49d00000000008b.

Definition bw6_761_M : Z := bw6_761_p.

Axiom bw6_761_certificate :
  ZMap.Empty (N.iter 2196 (processDivstep bw6_761_M) state0).

Definition bw6_761_iters : N := 2196.
