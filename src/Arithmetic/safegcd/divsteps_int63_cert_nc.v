From Stdlib Require Import ZArith Uint63 Sint63.
Require Import divsteps_int63.

Open Scope uint63_scope.

Lemma bls12_int63_certificate :
  State_is_empty (N.iter 1078%N (processDivstep bls12_M) state0) = true.
Proof. native_compute. reflexivity. Qed.
