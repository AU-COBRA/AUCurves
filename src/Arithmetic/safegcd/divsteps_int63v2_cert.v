From Stdlib Require Import ZArith Uint63 Sint63.
Require Import divsteps_int63v2.

Open Scope uint63_scope.

Lemma bls12_int63v2_certificate :
  State_is_empty (N.iter 1078%N (processDivstep bls12_M_log2 bls12_M) state0) = true.
Proof. vm_compute. reflexivity. Qed.
