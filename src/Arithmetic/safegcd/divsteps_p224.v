(** O'Connor certificate for NIST P-224 (secp224r1) divstep convergence.

    Parallel to [divsteps_p256.v]: the computation
      State_is_empty(processDivstep^649(state0)) = true
    is the divsteps-framework claim that 649 iterations of
    [processDivstep p224_M] starting from [state0] empties the state,
    which (via [divsteps_bridge]'s generic [oconnor_bridge]) implies
    convergence of the abstract (d,f,g) sequence for any
    coprime-to-[p224_p] input.

    As with BLS12 / P-256 / secp256k1, we axiomatize the [ZMap.Empty]
    result rather than sealing it with [vm_cast_no_check] (Qed for
    that takes many minutes due to kernel type-checking the large
    [N.iter] term).  Independent OCaml verification of the same cert
    is available via [Arithmetic/safegcd/multi_curve_driver] (see the
    directory's [README.md]).

    Iteration count: 649.  Derived from P-224's [mbits = 224] via
      iters = (49 * mbits + 57) / 17 = (49*224+57)/17 = 11033/17 = 649.
    See [P224_FpInv.p224_divstep_iters_val]. *)

From Stdlib Require Import ZArith.
Require Import divsteps_base.

Definition p224_p : Z :=
  0xffffffffffffffffffffffffffffffff000000000000000000000001.

Definition p224_M : Z := p224_p.

Axiom p224_certificate :
  ZMap.Empty (N.iter 649 (processDivstep p224_M) state0).

Definition p224_iters : N := 649.
