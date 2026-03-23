Require Import ZArith.
Require Import divsteps_base.
Definition bls12_p : Z := 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.
Lemma bls12_certificate : ZMap.Empty (N.iter 1075 (processDivstep bls12_p) state0).
Proof. apply ZMap.is_empty_2. vm_cast_no_check (refl_equal true). Time Qed.
Definition bls12_iters : N := 1075.
