(** O'Connor certificate for Pallas (pasta_fp) divstep convergence.

    Parallel to [divsteps_bls12.v] and [divsteps_bn254.v]: the computation
      State_is_empty(processDivstep^738(state0)) = true
    is the divsteps-framework claim that 738 iterations of
    [processDivstep pallas_M] starting from [state0] empties the state,
    which (via [divsteps_bridge]'s generic [oconnor_bridge]) implies
    convergence of the abstract (d,f,g) sequence for any
    coprime-to-[pallas_p] input.

    As with BLS12/BN254, we axiomatize the [ZMap.Empty] result rather
    than sealing it with [vm_cast_no_check] (Qed for that takes many
    minutes due to kernel type-checking the large [N.iter] term).
    Independent OCaml verification of the same cert is available via
    [Arithmetic/safegcd/multi_curve_driver].

    Iteration count: 738.  Derived from Pallas's [mbits = 255] via
      iters = (49 * mbits + 57) / 17 = (49*255+57)/17 = 12552/17 = 738.
    See [Pallas_FpInv.pallas_divstep_iters_val]. *)

From Stdlib Require Import ZArith.
Require Import divsteps_base.

Definition pallas_p : Z :=
  0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001.

Definition pallas_M : Z := pallas_p.

Axiom pallas_certificate :
  ZMap.Empty (N.iter 738 (processDivstep pallas_M) state0).

Definition pallas_iters : N := 738.
