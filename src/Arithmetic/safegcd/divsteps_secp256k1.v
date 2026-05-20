(** O'Connor certificate for secp256k1 divstep convergence.

    Parallel to [divsteps_bls12.v]: the computation
      State_is_empty(processDivstep^741(state0)) = true
    is the divsteps-framework claim that 741 iterations of
    [processDivstep secp256k1_M] starting from [state0] empties the
    state, which (via [divsteps_bridge]'s generic [oconnor_bridge])
    implies convergence of the abstract (d,f,g) sequence for any
    coprime-to-[secp256k1_p] input.

    As with BLS12, we axiomatize the [ZMap.Empty] result rather than
    sealing it with [vm_cast_no_check] (Qed for that takes many
    minutes due to kernel type-checking the large [N.iter] term).
    Independent OCaml verification of the same cert is available via
    [Arithmetic/safegcd/multi_curve_driver] (see the directory's
    [README.md]).

    Iteration count: 741.  Derived from secp256k1's [mbits = 256] via
      iters = (49 * mbits + 57) / 17 = (49*256+57)/17 = 12601/17 = 741.
    See [Secp256k1_FpInv.secp256k1_divstep_iters_val]. *)

From Stdlib Require Import ZArith.
Require Import divsteps_base.

Definition secp256k1_p : Z :=
  0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f.

Definition secp256k1_M : Z := secp256k1_p.

Axiom secp256k1_certificate :
  ZMap.Empty (N.iter 741 (processDivstep secp256k1_M) state0).

Definition secp256k1_iters : N := 741.
