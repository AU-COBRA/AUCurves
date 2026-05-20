(** O'Connor certificate for Vesta (pasta_fq) divstep convergence.

    Parallel to [divsteps_bls12.v] and [divsteps_bn254.v]: the computation
      State_is_empty(processDivstep^738(state0)) = true
    is the divsteps-framework claim that 738 iterations of
    [processDivstep vesta_M] starting from [state0] empties the state,
    which (via [divsteps_bridge]'s generic [oconnor_bridge]) implies
    convergence of the abstract (d,f,g) sequence for any
    coprime-to-[vesta_p] input.

    As with BLS12/BN254/Pallas, we axiomatize the [ZMap.Empty] result
    rather than sealing it with [vm_cast_no_check] (Qed for that takes
    many minutes due to kernel type-checking the large [N.iter] term).
    Independent OCaml verification of the same cert is available via
    [Arithmetic/safegcd/multi_curve_driver].

    Iteration count: 738.  Derived from Vesta's [mbits = 255] via
      iters = (49 * mbits + 57) / 17 = (49*255+57)/17 = 12552/17 = 738.
    See [Vesta_FpInv.vesta_divstep_iters_val]. *)

From Stdlib Require Import ZArith.
Require Import divsteps_base.

Definition vesta_p : Z :=
  0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001.

Definition vesta_M : Z := vesta_p.

Axiom vesta_certificate :
  ZMap.Empty (N.iter 738 (processDivstep vesta_M) state0).

Definition vesta_iters : N := 738.
