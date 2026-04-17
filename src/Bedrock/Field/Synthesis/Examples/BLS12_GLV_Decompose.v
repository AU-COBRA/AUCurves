(** * BLS12-381 GLV scalar decomposition.

    For BLS12-381, the subgroup order r = λ² + λ + 1 exactly over Z,
    where λ = 0xac45a4010001a40200000000ffffffff (128 bits).

    This gives an extremely simple decomposition: for any k < r,
      k1 = k mod λ       (at most 128 bits)
      k2 = k div λ       (at most 128 bits, except k=r-1 gives 129 bits)
      k  = k1 + k2 · λ   (exact over Z, no modular reduction needed)

    Combined with the endomorphism φ(x,y) = (ω·x, y) which satisfies
    φ = [λ] on G1[r], Shamir's trick gives:
      [k]P = [k1]P + [k2]φ(P)
    using a 129-iteration loop instead of the 256-iteration simple ladder.

    Reference: Gallant, Lambert, Vanstone. "Faster point multiplication
    on elliptic curves with efficient endomorphisms." CRYPTO 2001. *)

From Stdlib Require Import ZArith Lia.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_ScalarReduce.
Local Open Scope Z_scope.

(** *** The GLV eigenvalue λ *)

(** λ is a root of T² + T + 1 in Z/rZ, and r = λ² + λ + 1 over Z. *)
Definition bls12_lambda : Z := 0xac45a4010001a40200000000ffffffff.

(** *** Key identity: r = λ² + λ + 1 over Z *)
Lemma bls12_r_eq_lambda_poly : bls12_r = bls12_lambda ^ 2 + bls12_lambda + 1.
Proof. vm_compute. reflexivity. Qed.

(** λ is a root of T² + T + 1 mod r *)
Lemma bls12_lambda_root : (bls12_lambda ^ 2 + bls12_lambda + 1) mod bls12_r = 0.
Proof. vm_compute. reflexivity. Qed.

(** λ³ = 1 mod r (λ has order 3 in the multiplicative group) *)
Lemma bls12_lambda_cube : bls12_lambda ^ 3 mod bls12_r = 1 mod bls12_r.
Proof. vm_compute. reflexivity. Qed.

Lemma bls12_lambda_pos : 0 < bls12_lambda.
Proof. vm_compute. reflexivity. Qed.

Lemma bls12_lambda_128bits : bls12_lambda < 2^128.
Proof. vm_compute. reflexivity. Qed.

(** *** Scalar decomposition *)

Definition glv_decompose (k : Z) : Z * Z :=
  (k mod bls12_lambda, k / bls12_lambda).

(** The decomposition reconstructs k exactly over Z *)
Lemma glv_decompose_correct : forall k,
  0 <= k ->
  let '(k1, k2) := glv_decompose k in
  k = k1 + k2 * bls12_lambda.
Proof.
  intros k Hk. unfold glv_decompose.
  pose proof bls12_lambda_pos.
  pose proof (Z.div_mod k bls12_lambda ltac:(lia)).
  lia.
Qed.

(** k1 is small (< λ ≈ 2^128) *)
Lemma glv_k1_bound : forall k,
  0 <= k ->
  let '(k1, _) := glv_decompose k in
  0 <= k1 < bls12_lambda.
Proof.
  intros k Hk. unfold glv_decompose.
  pose proof bls12_lambda_pos.
  apply Z.mod_pos_bound. lia.
Qed.

(** k2 is small for k < r: k2 ≤ λ + 1 < 2^129 *)
Lemma glv_k2_bound : forall k,
  0 <= k < bls12_r ->
  let '(_, k2) := glv_decompose k in
  0 <= k2 <= bls12_lambda + 1.
Proof.
  intros k [Hk0 Hkr]. unfold glv_decompose.
  pose proof bls12_lambda_pos.
  split.
  - apply Z.div_pos; lia.
  - apply Z.div_le_upper_bound; [lia|].
    rewrite bls12_r_eq_lambda_poly in Hkr.
    (* k < λ² + λ + 1, so k / λ ≤ λ + 1 *)
    nia.
Qed.

(** *** Connection to scalar multiplication *)

(** For P in G1[r] with φ(P) = [λ]P:
      [k]P = [k1]P + [k2]·[λ]P = [k1]P + [k2]·φ(P)
    This follows from glv_decompose_correct + linearity of scalar mult.

    The Shamir loop computes [k1]P + [k2]φ(P) in max(bits(k1), bits(k2))
    iterations ≈ 129 iterations, vs 256 for the simple ladder. *)
