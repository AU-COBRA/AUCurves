(** * SafeRustBLS12TowerHelpers.v
 *
 * BLS12-381 tower helpers, parallel to the BN254 helpers in
 * [SafeRustLeafRefinement.v] §10b–§10d.
 *
 * Key difference: BLS12-381 uses ξ = 1 + u for the Fp6 quadratic non-
 * residue, so [mul_xi] is just  (a, b) ↦ (a - b, a + b) — there is no
 * [fp_mul9] auxiliary. Everything else (Fp6 projection, mul_by_v, fp6
 * negation, fp12 conjugate) keeps the same structural shape.
 *
 * Trust footprint: same Section [Variable]s + [Hypothesis]es as the
 * BN254 helpers. After [End BLS12TowerHelpers], all lemmas carry their
 * impls + correctness hypotheses as parameters; instantiated by
 * [SafeRustBLS12Concrete.v].
 *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
Import ListNotations.
Local Open Scope Z_scope.

Require Import Bedrock.SafeRustSimulation.
Require Import Bedrock.SafeRustLeafRefinement.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime_certif.

(* ================================================================ *)
(* §1. BLS12 modulus shorthand                                       *)
(* ================================================================ *)

Definition bls12_p : Z := bls12_381_modulus.

Lemma bls12_p_pos : 0 < bls12_p.
Proof. unfold bls12_p, bls12_381_modulus. lia. Qed.

(* ================================================================ *)
(* §2. Section: BLS12 tower helpers                                  *)
(* ================================================================ *)

Section BLS12TowerHelpers.

(** Same parametric impls as the BN254 Section. *)
Variable add_impl : rust_val TFp -> rust_val TFp -> rust_val TFp.
Variable sub_impl : rust_val TFp -> rust_val TFp -> rust_val TFp.
Variable mul_impl : rust_val TFp -> rust_val TFp -> rust_val TFp.
Variable opp_impl : rust_val TFp -> rust_val TFp.
Variable fp_eval : rust_val TFp -> Z.

(** Per-leaf correctness, against [bls12_p] (not [bn254_p]). *)
Hypothesis add_correct : forall x y,
  fp_eval (add_impl x y) = (fp_eval x + fp_eval y) mod bls12_p.

Hypothesis sub_correct : forall x y,
  fp_eval (sub_impl x y) = (fp_eval x - fp_eval y + bls12_p) mod bls12_p.

Hypothesis mul_correct : forall x y,
  fp_eval (mul_impl x y) = (fp_eval x * fp_eval y) mod bls12_p.

Hypothesis opp_correct : forall x,
  fp_eval (opp_impl x) = (bls12_p - fp_eval x) mod bls12_p.

(* ---------------------------------------------------------------- *)
(* §2a. Fp2 evaluation (re-derivation pinned to bls12_p)            *)
(* ---------------------------------------------------------------- *)

Definition bls12_fp2_eval (v : rust_val TFp2) : Z * Z :=
  match v with
  | VFp2 a b => (fp_eval a, fp_eval b)
  end.

(* ---------------------------------------------------------------- *)
(* §2b. mul_xi for BLS12-381: ξ = (1, 1)                            *)
(*      (a + b·u)·(1 + u) = (a - b) + (a + b)·u                     *)
(* ---------------------------------------------------------------- *)

Lemma bls12_fp2_mul_xi_eval : forall a b,
  let re := sub_impl a b in
  let im := add_impl a b in
  bls12_fp2_eval (VFp2 re im) =
    ((fp_eval a - fp_eval b + bls12_p) mod bls12_p,
     (fp_eval a + fp_eval b) mod bls12_p).
Proof.
  intros. unfold bls12_fp2_eval. f_equal.
  - subst re. apply sub_correct.
  - subst im. apply add_correct.
Qed.

(* ---------------------------------------------------------------- *)
(* §2c. Fp6 / Fp12 projections (curve-agnostic; pinned to fp_eval)  *)
(* ---------------------------------------------------------------- *)

Definition bls12_fp6_eval (v : rust_val TFp6) : (Z * Z) * (Z * Z) * (Z * Z) :=
  match v with
  | VFp6 c0 c1 c2 => (bls12_fp2_eval c0, bls12_fp2_eval c1, bls12_fp2_eval c2)
  end.

Definition bls12_fp12_eval (v : rust_val TFp12) :
    ((Z * Z) * (Z * Z) * (Z * Z)) * ((Z * Z) * (Z * Z) * (Z * Z)) :=
  match v with
  | VFp12 c0 c1 => (bls12_fp6_eval c0, bls12_fp6_eval c1)
  end.

Definition bls12_fp2_re (v : rust_val TFp2) : rust_val TFp :=
  match v with VFp2 a _ => a end.
Definition bls12_fp2_im (v : rust_val TFp2) : rust_val TFp :=
  match v with VFp2 _ b => b end.

Definition bls12_fp6_c0 (v : rust_val TFp6) : rust_val TFp2 :=
  match v with VFp6 a _ _ => a end.
Definition bls12_fp6_c1 (v : rust_val TFp6) : rust_val TFp2 :=
  match v with VFp6 _ b _ => b end.
Definition bls12_fp6_c2 (v : rust_val TFp6) : rust_val TFp2 :=
  match v with VFp6 _ _ c => c end.

Definition bls12_fp12_c0 (v : rust_val TFp12) : rust_val TFp6 :=
  match v with VFp12 a _ => a end.
Definition bls12_fp12_c1 (v : rust_val TFp12) : rust_val TFp6 :=
  match v with VFp12 _ b => b end.

(* ---------------------------------------------------------------- *)
(* §2d. Fp6 mul_by_v with BLS12 mul_xi                              *)
(*      (a0 + a1·v + a2·v²)·v = ξ·a2 + a0·v + a1·v²                 *)
(*      where ξ·(re, im) = (re - im, re + im) for ξ = 1+u           *)
(* ---------------------------------------------------------------- *)

Definition bls12_fp6_mul_by_v (x : rust_val TFp6) : rust_val TFp6 :=
  let a0 := bls12_fp6_c0 x in
  let a1 := bls12_fp6_c1 x in
  let a2 := bls12_fp6_c2 x in
  let a2_re := bls12_fp2_re a2 in
  let a2_im := bls12_fp2_im a2 in
  let a2_mulxi := VFp2 (sub_impl a2_re a2_im) (add_impl a2_re a2_im) in
  VFp6 a2_mulxi a0 a1.

Lemma bls12_fp6_mul_by_v_eval_structure : forall x,
  bls12_fp6_eval (bls12_fp6_mul_by_v x) =
    (bls12_fp2_eval (VFp2 (sub_impl (bls12_fp2_re (bls12_fp6_c2 x))
                                     (bls12_fp2_im (bls12_fp6_c2 x)))
                           (add_impl (bls12_fp2_re (bls12_fp6_c2 x))
                                     (bls12_fp2_im (bls12_fp6_c2 x)))),
     bls12_fp2_eval (bls12_fp6_c0 x),
     bls12_fp2_eval (bls12_fp6_c1 x)).
Proof.
  intros x. unfold bls12_fp6_mul_by_v, bls12_fp6_eval. reflexivity.
Qed.

(* ---------------------------------------------------------------- *)
(* §2e. Fp6 negation and Fp12 conjugate (curve-agnostic structure)  *)
(* ---------------------------------------------------------------- *)

Definition bls12_fp6_neg (x : rust_val TFp6) : rust_val TFp6 :=
  VFp6 (VFp2 (opp_impl (bls12_fp2_re (bls12_fp6_c0 x)))
             (opp_impl (bls12_fp2_im (bls12_fp6_c0 x))))
       (VFp2 (opp_impl (bls12_fp2_re (bls12_fp6_c1 x)))
             (opp_impl (bls12_fp2_im (bls12_fp6_c1 x))))
       (VFp2 (opp_impl (bls12_fp2_re (bls12_fp6_c2 x)))
             (opp_impl (bls12_fp2_im (bls12_fp6_c2 x)))).

Lemma bls12_fp6_neg_eval : forall x,
  bls12_fp6_eval (bls12_fp6_neg x) =
    (bls12_fp2_eval (VFp2 (opp_impl (bls12_fp2_re (bls12_fp6_c0 x)))
                           (opp_impl (bls12_fp2_im (bls12_fp6_c0 x)))),
     bls12_fp2_eval (VFp2 (opp_impl (bls12_fp2_re (bls12_fp6_c1 x)))
                           (opp_impl (bls12_fp2_im (bls12_fp6_c1 x)))),
     bls12_fp2_eval (VFp2 (opp_impl (bls12_fp2_re (bls12_fp6_c2 x)))
                           (opp_impl (bls12_fp2_im (bls12_fp6_c2 x))))).
Proof. reflexivity. Qed.

Definition bls12_fp12_conjugate (x : rust_val TFp12) : rust_val TFp12 :=
  VFp12 (bls12_fp12_c0 x) (bls12_fp6_neg (bls12_fp12_c1 x)).

Lemma bls12_fp12_conjugate_structure : forall x,
  bls12_fp12_eval (bls12_fp12_conjugate x) =
    (bls12_fp6_eval (bls12_fp12_c0 x),
     bls12_fp6_eval (bls12_fp6_neg (bls12_fp12_c1 x))).
Proof. reflexivity. Qed.

End BLS12TowerHelpers.
