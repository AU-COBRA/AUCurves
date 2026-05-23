(** * RistrettoSqrtDecompose — wire the verified [fe25519_pow22523]
 *    chain into [ristretto_sqrt_ratio_m1].
 *
 *  Task T6 (algebraic core).  [ristretto_sqrt_ratio_m1] (in
 *  [RistrettoHelpers.v]) computes its inner power as
 *    [pow_mod ((u*v7) mod p) ((p-5)/8) p]
 *  — an abstract modular exponentiation.  The verified addition-chain
 *  [fe25519_pow22523] (in [Fe25519Pow22523.v], Qed, 0 axioms) computes
 *  exactly that power.  This file defines [sqrt_ratio_decomposed],
 *  identical to the spec but with the abstract [pow_mod] replaced by
 *  the concrete chain, and proves the two are equal.  The decomposed
 *  form is the one the decoder/encoder ASTs target — it expresses the
 *  power as a sequence of field squarings/multiplications (the chain),
 *  carrying ZERO new trust beyond [fe25519_mul]/[fe25519_sq]. *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import micromega.Lia.
Require Import Bedrock.End2End.Ed25519.CompressVerified.
Require Import Bedrock.End2End.Lizard.RistrettoConsts.
Require Import Bedrock.End2End.Lizard.RistrettoHelpers.
Require Import Bedrock.End2End.Lizard.Fe25519Pow22523.
Local Open Scope Z_scope.

(** The power bridge: the abstract [pow_mod] used inside
    [ristretto_sqrt_ratio_m1] equals the verified chain applied to the
    same (already-reduced) base. *)
Lemma pow22523_eq_pow_mod :
  forall b,
    fe25519_pow22523 (b mod ed25519_p)
    = pow_mod ((b mod ed25519_p)) ((ed25519_p - 5) / 8) ed25519_p.
Proof.
  intros b.
  rewrite fe25519_pow22523_correct.
  rewrite Z.mod_mod by (unfold ed25519_p; lia).
  reflexivity.
Qed.

(** [sqrt_ratio_decomposed] — copy of [ristretto_sqrt_ratio_m1] with
    the inner [pow_mod] replaced by [fe25519_pow22523].  The base
    [(u * v7) mod p] is already reduced, so [pow22523_eq_pow_mod]
    applies directly. *)
Definition sqrt_ratio_decomposed (u v : Z) : bool * Z :=
  let v3   := (v * v * v) mod ed25519_p in
  let v7   := (v3 * v3 * v) mod ed25519_p in
  let pow_val := fe25519_pow22523 ((u * v7) mod ed25519_p) in
  let r0   := (u * v3 * pow_val) mod ed25519_p in
  let check := (v * r0 * r0) mod ed25519_p in
  let u_mod := u mod ed25519_p in
  let neg_u := ristretto_canonical_negate u in
  let neg_iu := ristretto_canonical_negate
                  ((ristretto_SQRT_M1 * u) mod ed25519_p) in
  let correct_sign_sqrt    := Z.eqb check u_mod in
  let flipped_sign_sqrt    := Z.eqb check neg_u in
  let flipped_sign_sqrt_i  := Z.eqb check neg_iu in
  let r1 :=
    if correct_sign_sqrt then r0
    else if flipped_sign_sqrt then
      (r0 * ristretto_SQRT_M1) mod ed25519_p
    else if flipped_sign_sqrt_i then
      (r0 * ristretto_SQRT_M1) mod ed25519_p
    else
      r0 in
  let r := if ristretto_is_negative r1
           then ristretto_canonical_negate r1
           else r1 in
  let was_square := orb correct_sign_sqrt flipped_sign_sqrt in
  (was_square, r).

(** The decomposed form equals the spec.  The two definitions differ
    only in the [pow_val] let-binding; [pow22523_eq_pow_mod] reconciles
    them and the remaining structure is identical. *)
Theorem sqrt_ratio_decomposed_correct :
  forall u v, sqrt_ratio_decomposed u v = ristretto_sqrt_ratio_m1 u v.
Proof.
  intros u v.
  unfold sqrt_ratio_decomposed, ristretto_sqrt_ratio_m1.
  rewrite pow22523_eq_pow_mod.
  reflexivity.
Qed.
