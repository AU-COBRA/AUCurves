From Stdlib Require Import ZArith Uint63 Sint63.
Require Import divsteps_int63v3.

Open Scope uint63_scope.

Lemma bls12_int63v3_certificate :
  State_is_empty (N.iter 1078%N processDivstep state0) = true.
Proof. vm_compute. reflexivity. Qed.
