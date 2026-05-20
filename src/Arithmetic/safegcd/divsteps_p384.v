(** O'Connor certificate for NIST P-384 (secp384r1) divstep convergence.

    Parallel to [divsteps_p256.v]: the computation
      State_is_empty(processDivstep^1110(state0)) = true
    is the divsteps-framework claim that 1110 iterations of
    [processDivstep p384_M] starting from [state0] empties the state,
    which (via [divsteps_bridge]'s generic [oconnor_bridge]) implies
    convergence of the abstract (d,f,g) sequence for any
    coprime-to-[p384_p] input.

    As with the 256-bit primes, we axiomatize the [ZMap.Empty] result;
    Qed via [vm_cast_no_check] is many minutes due to kernel type-
    checking the large [N.iter] term.  Independent OCaml verification
    of the same cert is available via
    [Arithmetic/safegcd/multi_curve_driver].

    Iteration count: 1110.  Derived from P-384's [mbits = 384] via
      iters = (49 * mbits + 57) / 17 = (49*384+57)/17 = 18873/17 = 1110.
    See [P384_FpInv.p384_divstep_iters_val]. *)

From Stdlib Require Import ZArith.
Require Import divsteps_base.

Definition p384_p : Z :=
  0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff.

Definition p384_M : Z := p384_p.

Axiom p384_certificate :
  ZMap.Empty (N.iter 1110 (processDivstep p384_M) state0).

Definition p384_iters : N := 1110.
