(** O'Connor certificate for NIST P-521 (secp521r1) divstep convergence.

    Parallel to [divsteps_p256.v]: the computation
      State_is_empty(processDivstep^1505(state0)) = true
    is the divsteps-framework claim that 1505 iterations of
    [processDivstep p521_M] starting from [state0] empties the state,
    which (via [divsteps_bridge]'s generic [oconnor_bridge]) implies
    convergence of the abstract (d,f,g) sequence for any
    coprime-to-[p521_p] input.

    As with the 256/384-bit primes, we axiomatize the [ZMap.Empty]
    result; Qed via [vm_cast_no_check] is many minutes for the large
    [N.iter] term.  Independent OCaml verification of the same cert
    is available via [Arithmetic/safegcd/multi_curve_driver].

    Iteration count: 1505.  Derived from P-521's [mbits = 521] via
      iters = (49 * mbits + 57) / 17 = (49*521+57)/17 = 25586/17 = 1505.
    See [P521_FpInv.p521_divstep_iters_val].

    Note: p521 = 2^521 - 1 (the Mersenne prime M_521). *)

From Stdlib Require Import ZArith.
Require Import divsteps_base.

Definition p521_p : Z :=
  0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff.

Definition p521_M : Z := p521_p.

Axiom p521_certificate :
  ZMap.Empty (N.iter 1505 (processDivstep p521_M) state0).

Definition p521_iters : N := 1505.
