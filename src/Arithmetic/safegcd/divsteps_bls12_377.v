(** O'Connor certificate for BLS12-377 divstep convergence.

    Parallel to [divsteps_bls12.v] / [divsteps_bn254.v]: the computation
      State_is_empty(processDivstep^1090(state0)) = true
    is the divsteps-framework claim that 1090 iterations of
    [processDivstep bls12_377_M] starting from [state0] empties the state,
    which (via [divsteps_bridge]'s generic [oconnor_bridge]) implies
    convergence of the abstract (d,f,g) sequence for any
    coprime-to-[bls12_377_p] input.

    As with BLS12/BN254, we axiomatize the [ZMap.Empty] result rather
    than sealing it with [vm_cast_no_check] (Qed for that takes many
    minutes due to kernel type-checking the large [N.iter] term).
    Independent OCaml verification of the same cert is available via
    [Arithmetic/safegcd/multi_curve_driver].

    Iteration count: 1090.  Derived from BLS12-377's [mbits = 377] via
      iters = (49 * mbits + 57) / 17 = (49*377+57)/17 = 18530/17 = 1090.
    See [BLS12_377_FpInv.bls12_377_divstep_iters_val]. *)

From Stdlib Require Import ZArith.
Require Import divsteps_base.

Definition bls12_377_p : Z :=
  0x1ae3a4617c510eac63b05c06ca1493b1a22d9f300f5138f1ef3622fba094800170b5d44300000008508c00000000001.

Definition bls12_377_M : Z := bls12_377_p.

Axiom bls12_377_certificate :
  ZMap.Empty (N.iter 1090 (processDivstep bls12_377_M) state0).

Definition bls12_377_iters : N := 1090.
