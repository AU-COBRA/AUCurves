Require Import Bedrock.Field.Synthesis.Examples.BLS12_FpInv.

From Stdlib Require Import ZArith Lia Znumtheory.
Local Open Scope Z_scope.

Definition bls12_p' := BLS12_FpInv.bls12_p.

Lemma Zmod_sub_zero : forall a b m,
  m <> 0 -> (a - b) mod m = 0 -> a mod m = b mod m.
Proof.
  intros a b m Hm H.
  apply Zmod_divides in H; [| exact Hm].
  destruct H as [k Hk].
  assert (a = b + k * m) by lia.
  subst a. rewrite Zplus_mod, Z_mod_mult, Z.add_0_r, Zmod_mod. reflexivity.
Qed.

(* Test: can we see the goal shape? *)
Lemma test_goal : forall x,
  0 < x < bls12_p' ->
  Z.gcd x bls12_p' = 1 ->
  (BLS12_FpInv.fp_inv_spec x * x) mod bls12_p' = 1.
Proof.
  intros x Hx Hgcd.
  unfold BLS12_FpInv.fp_inv_spec.
  set (N := Z.to_nat BLS12_FpInv.bls12_divstep_iters).
  set (spec_result := BLS12_FpInv.iter_divstep_spec bls12_p' N 1 bls12_p' x 0 1).
  Redirect "/tmp/fpinv_goal" Show.
  admit.
Admitted.
