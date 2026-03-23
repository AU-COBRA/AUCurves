Require Import ZArith.
Require Import divsteps_base.

Definition bls12_p : Z :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.

(** Tight bound: N=1078, found by OCaml extraction binary search.
    BY formula gives 1101; convex hull gives 1078 (saves 23 iterations = 2.1%).
    Verified: N=1077 does NOT converge, N=1078 does. *)
Lemma bls12_certificate : ZMap.Empty (N.iter 1078 (processDivstep bls12_p) state0).
Proof. apply ZMap.is_empty_2. native_compute. reflexivity. Qed.
Definition bls12_iters : N := 1078.
