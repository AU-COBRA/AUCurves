From Stdlib Require Import ZArith.
Require Import divsteps_fast_defs.

Lemma bls12_fast_certificate :
  State_is_empty (N.iter 1078 (processDivstep bls12_M) state0) = true.
Proof. native_compute. reflexivity. Time Qed.
