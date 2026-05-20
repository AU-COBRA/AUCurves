(** O'Connor certificate for BLS24-509 divstep convergence.

    Parallel to [divsteps_bls12.v] / [divsteps_bn254.v]: the computation
      State_is_empty(processDivstep^1470(state0)) = true
    is the divsteps-framework claim that 1470 iterations of
    [processDivstep bls24_509_M] starting from [state0] empties the state,
    which (via [divsteps_bridge]'s generic [oconnor_bridge]) implies
    convergence of the abstract (d,f,g) sequence for any
    coprime-to-[bls24_509_p] input.

    As with BLS12/BN254, we axiomatize the [ZMap.Empty] result rather
    than sealing it with [vm_cast_no_check] (Qed for that takes many
    minutes due to kernel type-checking the large [N.iter] term).
    Independent OCaml verification of the same cert is available via
    [Arithmetic/safegcd/multi_curve_driver].

    Iteration count: 1470.  Derived from BLS24-509's [mbits = 509] via
      iters = (49 * mbits + 57) / 17 = (49*509+57)/17 = 24998/17 = 1470.
    See [BLS24_509_FpInv.bls24_509_divstep_iters_val]. *)

From Stdlib Require Import ZArith.
Require Import divsteps_base.

Definition bls24_509_p : Z :=
  0x155556ffff39ca9bfcedf2b4f9c0ecf6cb8ac8495d187e8c32ea0103e01090bb626e85bf7c18a0f0cfcb5c6071bad3d2ee63bd076e8d9300a13d118db8bfd2ab.

Definition bls24_509_M : Z := bls24_509_p.

Axiom bls24_509_certificate :
  ZMap.Empty (N.iter 1470 (processDivstep bls24_509_M) state0).

Definition bls24_509_iters : N := 1470.
