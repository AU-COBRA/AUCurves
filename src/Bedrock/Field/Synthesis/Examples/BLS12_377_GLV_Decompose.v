(** * BLS12-377 GLV scalar decomposition.

    For BLS12-377, the subgroup order r = lambda^2 + lambda + 1 exactly over Z,
    where lambda = u^2 - 1 = 0x452217cc900000010a11800000000000 (127 bits).

    Decomposition: k1 = k mod lambda, k2 = k div lambda.
    Then k = k1 + k2 * lambda exactly over Z. *)

From Stdlib Require Import ZArith Lia.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_377_ScalarReduce.
Local Open Scope Z_scope.

(** *** The GLV eigenvalue lambda *)

Definition bls377_lambda : Z :=
  Eval vm_compute in (bls377_u ^ 2 - 1).

(** *** Key identity: r = lambda^2 + lambda + 1 over Z *)
Lemma bls377_r_eq_lambda_poly : bls377_r = bls377_lambda ^ 2 + bls377_lambda + 1.
Proof. vm_compute. reflexivity. Qed.

Lemma bls377_lambda_root : (bls377_lambda ^ 2 + bls377_lambda + 1) mod bls377_r = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma bls377_lambda_cube : bls377_lambda ^ 3 mod bls377_r = 1 mod bls377_r.
Proof. vm_compute. reflexivity. Qed.

Lemma bls377_lambda_pos : 0 < bls377_lambda.
Proof. vm_compute. reflexivity. Qed.

Lemma bls377_lambda_127bits : bls377_lambda < 2^127.
Proof. vm_compute. reflexivity. Qed.

(** *** Scalar decomposition *)

Definition glv_decompose_377 (k : Z) : Z * Z :=
  (k mod bls377_lambda, k / bls377_lambda).

Lemma glv_decompose_377_correct : forall k,
  0 <= k ->
  let '(k1, k2) := glv_decompose_377 k in
  k = k1 + k2 * bls377_lambda.
Proof.
  intros k Hk. unfold glv_decompose_377.
  pose proof bls377_lambda_pos.
  pose proof (Z.div_mod k bls377_lambda ltac:(lia)).
  lia.
Qed.

Lemma glv377_k1_bound : forall k,
  0 <= k ->
  let '(k1, _) := glv_decompose_377 k in
  0 <= k1 < bls377_lambda.
Proof.
  intros k Hk. unfold glv_decompose_377.
  pose proof bls377_lambda_pos.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma glv377_k2_bound : forall k,
  0 <= k < bls377_r ->
  let '(_, k2) := glv_decompose_377 k in
  0 <= k2 <= bls377_lambda + 1.
Proof.
  intros k [Hk0 Hkr]. unfold glv_decompose_377.
  pose proof bls377_lambda_pos.
  split.
  - apply Z.div_pos; lia.
  - apply Z.div_le_upper_bound; [lia|].
    rewrite bls377_r_eq_lambda_poly in Hkr.
    nia.
Qed.
