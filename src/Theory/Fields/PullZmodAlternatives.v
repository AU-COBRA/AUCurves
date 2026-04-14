(******************************************************************************)
(*                                                                            *)
(*     PullZmodAlternatives: Testing alternatives to pull_Zmod               *)
(*                                                                            *)
(*  Comparison of tactics for normalization of:                              *)
(*    ((a mod m) op (b mod m)) mod m  →  (a op b) mod m                     *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import ZArith.
Local Open Scope Z_scope.

(** Test 1: direct rewrite with Zplus_mod *)
Lemma test1_direct_rewrite_add (a b m : Z) :
  ((a mod m) + (b mod m)) mod m = (a + b) mod m.
Proof.
  rewrite <- Zplus_mod; reflexivity.
Qed.

(** Test 2: direct rewrite with Zmult_mod *)
Lemma test2_direct_rewrite_mul (a b m : Z) :
  ((a mod m) * (b mod m)) mod m = (a * b) mod m.
Proof.
  rewrite <- Zmult_mod; reflexivity.
Qed.

(** Test 3: direct rewrite with Zminus_mod *)
Lemma test3_direct_rewrite_sub (a b m : Z) :
  ((a mod m) - (b mod m)) mod m = (a - b) mod m.
Proof.
  rewrite <- Zminus_mod; reflexivity.
Qed.

(** Test 4: Using Zmod_mod for nested mods *)
Lemma test4_nested_mod (a m : Z) :
  (a mod m) mod m = a mod m.
Proof.
  rewrite Zmod_mod; reflexivity.
Qed.

(** Test 5: Complex mul then add - test if sequence matters *)
Lemma test5_complex_chain (a b c m : Z) :
  (((a mod m) + (b mod m)) mod m * (c mod m)) mod m = ((a + b) * c) mod m.
Proof.
  rewrite <- (Zplus_mod a b).
  rewrite <- Zmult_mod.
  reflexivity.
Qed.

(** Test 6: Manual beta reduction and rewrite *)
Lemma test6_beta_rewrite_add (a b m : Z) :
  ((a mod m) + (b mod m)) mod m = (a + b) mod m.
Proof.
  change ((a mod m + b mod m) mod m = (a + b) mod m).
  rewrite <- Zplus_mod; reflexivity.
Qed.

(** Test 7: Using rewrite without reflexivity *)
Lemma test7_rewrite_only_mul (a b m : Z) :
  ((a mod m) * (b mod m)) mod m = (a * b) mod m.
Proof.
  rewrite <- Zmult_mod; reflexivity.
Qed.

(** Test 8: Chained rewrites *)
Lemma test8_chained_rewrites (a b c m : Z) :
  (((a mod m) + (b mod m)) mod m * (c mod m)) mod m = ((a + b) * c) mod m.
Proof.
  rewrite <- (Zplus_mod a b).
  rewrite <- Zmult_mod.
  reflexivity.
Qed.

(** Test 9: Single rewrite pattern *)
Lemma test9_single_rewrite (a b m : Z) :
  ((a mod m) + (b mod m)) mod m = (a + b) mod m.
Proof.
  rewrite <- Zplus_mod; reflexivity.
Qed.

(** Test 10: Pattern with subtraction *)
Lemma test10_sub_pattern (a b m : Z) :
  ((a mod m) - (b mod m)) mod m = (a - b) mod m.
Proof.
  rewrite <- Zminus_mod; reflexivity.
Qed.

(** Test 11: Direct multiplication *)
Lemma test11_mul_direct (a b m : Z) :
  ((a mod m) * (b mod m)) mod m = (a * b) mod m.
Proof.
  rewrite <- Zmult_mod; reflexivity.
Qed.

(** Test 12: Nested modulo *)
Lemma test12_nested_modulo (a m : Z) :
  (a mod m) mod m = a mod m.
Proof.
  rewrite Zmod_mod; reflexivity.
Qed.

(** Test 13: Simple equality without rewrites *)
Lemma test13_reflexivity_only (a b m : Z) :
  ((a mod m) + (b mod m)) mod m = ((a mod m) + (b mod m)) mod m.
Proof.
  reflexivity.
Qed.

(** Test 14: Simple reflexivity check *)
Lemma test14_simple_check (a b m : Z) :
  ((a mod m) + (b mod m)) mod m = ((a mod m) + (b mod m)) mod m.
Proof.
  reflexivity.
Qed.

(** Test 15: Rewrite with specified args *)
Lemma test15_rewrite_with_args (a b m : Z) :
  ((a mod m) * (b mod m)) mod m = (a * b) mod m.
Proof.
  rewrite <- Zmult_mod; reflexivity.
Qed.

(** Test 16: Rewrite with Zminus_mod *)
Lemma test16_rewrite_minus (a b m : Z) :
  ((a mod m) - (b mod m)) mod m = (a - b) mod m.
Proof.
  rewrite <- Zminus_mod; reflexivity.
Qed.

(** Test 17: Multiple rewrites in sequence *)
Lemma test17_multiple_rewrites (a b m : Z) :
  ((a mod m) + (b mod m)) mod m = (a + b) mod m.
Proof.
  rewrite <- Zplus_mod; reflexivity.
Qed.

(** Test 18: Rewrite and reflexivity *)
Lemma test18_rewrite_and_refl (a b m : Z) :
  ((a mod m) + (b mod m)) mod m = (a + b) mod m.
Proof.
  rewrite <- Zplus_mod; reflexivity.
Qed.

(** Test 19: Forward rewrite then backward *)
Lemma test19_forward_rewrite (a b m : Z) :
  ((a mod m) + (b mod m)) mod m = (a + b) mod m.
Proof.
  rewrite <- Zplus_mod; reflexivity.
Qed.

(** Test 20: Simple nesting *)
Lemma test20_simple_nesting (a b c m : Z) :
  (((a mod m) + (b mod m)) mod m * (c mod m)) mod m = ((a + b) * c) mod m.
Proof.
  rewrite <- (Zplus_mod a b).
  rewrite <- Zmult_mod.
  reflexivity.
Qed.
