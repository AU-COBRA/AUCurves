(** O'Connor certificate for BN254 (alt_bn128) divstep convergence.

    Parallel to [divsteps_bls12.v]: the computation
      State_is_empty(processDivstep^735(state0)) = true
    is the divsteps-framework claim that 735 iterations of
    [processDivstep bn254_M] starting from [state0] empties the state,
    which (via [divsteps_bridge]'s generic [oconnor_bridge]) implies
    convergence of the abstract (d,f,g) sequence for any
    coprime-to-[bn254_p] input.

    As with BLS12, we axiomatize the [ZMap.Empty] result rather than
    sealing it with [vm_cast_no_check] (Qed for that takes many
    minutes due to kernel type-checking the large [N.iter] term).
    Independent OCaml verification of the same cert is available via
    [Arithmetic/safegcd/multi_curve_driver] (see the directory's
    [README.md]).

    Iteration count: 735.  Derived from BN254's [mbits = 254] via
      iters = (49 * mbits + 57) / 17 = (49*254+57)/17 = 12503/17 = 735.
    See [BN254_FpInv.bn254_divstep_iters_val]. *)

From Stdlib Require Import ZArith.
Require Import divsteps_base.

Definition bn254_p : Z :=
  0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47.

Definition bn254_M : Z := bn254_p.

Axiom bn254_certificate :
  ZMap.Empty (N.iter 735 (processDivstep bn254_M) state0).

Definition bn254_iters : N := 735.
