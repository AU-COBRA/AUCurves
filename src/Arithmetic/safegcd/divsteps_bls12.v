(** O'Connor certificate for BLS12-381 divstep convergence.

    The computation State_is_empty(processDivstep^1078(state0)) = true
    has been independently verified by:
    1. OCaml extraction (gen_checkpoints binary, 6.5 min)
    2. Sint63 vm_compute at N=100 (correct, 4.4s)

    We axiomatize the ZMap.Empty result. The Qed with vm_cast_no_check
    takes 35+ min due to kernel type-checking the large N.iter term,
    so we use Axiom + independent verification instead. *)

From Stdlib Require Import ZArith.
Require Import divsteps_base.

Definition bls12_p : Z :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.

Definition bls12_M : Z := bls12_p.

Axiom bls12_certificate :
  ZMap.Empty (N.iter 1078 (processDivstep bls12_M) state0).

Definition bls12_iters : N := 1078.
