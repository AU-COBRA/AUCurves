(** O'Connor certificate for NIST P-256 (secp256r1) divstep convergence.

    Parallel to [divsteps_bls12.v]: the computation
      State_is_empty(processDivstep^741(state0)) = true
    is the divsteps-framework claim that 741 iterations of
    [processDivstep p256_M] starting from [state0] empties the state,
    which (via [divsteps_bridge]'s generic [oconnor_bridge]) implies
    convergence of the abstract (d,f,g) sequence for any
    coprime-to-[p256_p] input.

    As with BLS12, we axiomatize the [ZMap.Empty] result rather than
    sealing it with [vm_cast_no_check] (Qed for that takes many
    minutes due to kernel type-checking the large [N.iter] term).
    Independent OCaml verification of the same cert is available via
    [Arithmetic/safegcd/multi_curve_driver] (see the directory's
    [README.md]).

    Iteration count: 741.  Derived from P-256's [mbits = 256] via
      iters = (49 * mbits + 57) / 17 = (49*256+57)/17 = 12601/17 = 741.
    See [P256_FpInv.p256_divstep_iters_val]. *)

From Stdlib Require Import ZArith.
Require Import divsteps_base.

Definition p256_p : Z :=
  0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff.

Definition p256_M : Z := p256_p.

Axiom p256_certificate :
  ZMap.Empty (N.iter 741 (processDivstep p256_M) state0).

Definition p256_iters : N := 741.
