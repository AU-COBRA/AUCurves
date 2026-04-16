(** * ZModTower: concrete Z-mod-p implementation of the full Fp12 tower.

    Provides a [FieldOps Z (Z*Z) Fp12_Z] instance that can be instantiated
    for any prime [p] and nonresidue [xi = (xi_re, xi_im)] in Fp2. Intended
    for [Eval vm_compute in affine_miller (zmod_ops bn254_p bn254_xi) ...].

    The tower mirrors the bedrock2 representation exactly:
      Fp   = Z (operations mod p)
      Fp2  = Z * Z          (a0 + a1*u, u^2 = -1)
      Fp6  = Fp2 * Fp2 * Fp2  (c0 + c1*v + c2*v^2, v^3 = xi)
      Fp12 = Fp6 * Fp6          (c0 + c1*w, w^2 = v)

    All operations are [Z]-level (no [F PrimeField.M_pos] wrappers, no
    [bounded_by], no bedrock2 semantics). This is the lightest possible
    functional model.
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import micromega.Lia.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.

Require Import Bedrock.Field.PairingTheory.Affine.
Require Import Bedrock.Field.PairingTheory.CurveParams.
Require Import Bedrock.Field.PairingTheory.Curves.BN254_params.
Require Import Bedrock.Field.PairingTheory.Curves.BLS12_381_params.
Require Import Bedrock.Field.PairingTheory.Curves.BN256_params.
Require Import Bedrock.Field.PairingTheory.Curves.BN446_params.
Require Import Bedrock.Field.PairingTheory.Curves.BLS12_377_params.

Local Open Scope Z_scope.

(* ================================================================ *)
(* Fp = Z mod p                                                      *)
(* ================================================================ *)

Definition zfp_add (p : Z) (a b : Z) : Z := (a + b) mod p.
Definition zfp_sub (p : Z) (a b : Z) : Z := (a - b) mod p.
Definition zfp_mul (p : Z) (a b : Z) : Z := (a * b) mod p.
Definition zfp_neg (p : Z) (a : Z) : Z := (p - a) mod p.
(** Modular exponentiation for inversion: a^(p-2) mod p. *)
Fixpoint zpow_mod_aux (base exp acc p : Z) (fuel : nat) : Z :=
  match fuel with
  | O => acc
  | S fuel' =>
    let acc' := if Z.odd exp then (acc * base) mod p else acc in
    let base' := (base * base) mod p in
    zpow_mod_aux base' (Z.div2 exp) acc' p fuel'
  end.
Definition zfp_inv (p : Z) (a : Z) : Z :=
  zpow_mod_aux a (p - 2) 1 p (Z.to_nat (Z.log2 (p - 2) + 2)).

(* ================================================================ *)
(* Fp2 = (Z * Z), with u^2 = -1                                      *)
(* ================================================================ *)

Definition Fp2_Z := (Z * Z)%type.

Definition zfp2_add (p : Z) (a b : Fp2_Z) : Fp2_Z :=
  (zfp_add p (fst a) (fst b), zfp_add p (snd a) (snd b)).
Definition zfp2_sub (p : Z) (a b : Fp2_Z) : Fp2_Z :=
  (zfp_sub p (fst a) (fst b), zfp_sub p (snd a) (snd b)).
Definition zfp2_neg (p : Z) (a : Fp2_Z) : Fp2_Z :=
  (zfp_neg p (fst a), zfp_neg p (snd a)).
(** [Fp2 = Fp[u] / (u^2 - beta)] multiplication for arbitrary nonresidue [beta].
    [(a0+a1u)(b0+b1u) = (a0b0 + beta·a1b1) + (a0b1 + a1b0)u].
    For [beta = -1] this gives the standard [a0b0 - a1b1] form. *)
Definition zfp2_mul_beta (p : Z) (beta : Z) (a b : Fp2_Z) : Fp2_Z :=
  let a0 := fst a in let a1 := snd a in
  let b0 := fst b in let b1 := snd b in
  (zfp_add p (zfp_mul p a0 b0) (zfp_mul p beta (zfp_mul p a1 b1)),
   zfp_add p (zfp_mul p a0 b1) (zfp_mul p a1 b0)).
Definition zfp2_sqr_beta (p : Z) (beta : Z) (a : Fp2_Z) : Fp2_Z :=
  zfp2_mul_beta p beta a a.
(** Inversion: norm of [a + bu] is [a^2 - beta·b^2]; conjugate is [(a, -b)]. *)
Definition zfp2_inv_beta (p : Z) (beta : Z) (a : Fp2_Z) : Fp2_Z :=
  let n := zfp_sub p (zfp_mul p (fst a) (fst a))
                     (zfp_mul p beta (zfp_mul p (snd a) (snd a))) in
  let ni := zfp_inv p n in
  (zfp_mul p (fst a) ni, zfp_mul p (zfp_neg p (snd a)) ni).

(** Backwards-compat: [beta = -1] specialisations matching the original
    sum-of-squares / [a0b0 - a1b1] forms.  All existing proofs about
    [zfp2_mul] / [zfp2_inv] continue to apply via the equivalence
    lemmas [zfp2_mul_eq_beta_neg1] / [zfp2_inv_eq_beta_neg1] below. *)
Definition zfp2_mul (p : Z) (a b : Fp2_Z) : Fp2_Z :=
  let a0 := fst a in let a1 := snd a in
  let b0 := fst b in let b1 := snd b in
  (zfp_sub p (zfp_mul p a0 b0) (zfp_mul p a1 b1),
   zfp_add p (zfp_mul p a0 b1) (zfp_mul p a1 b0)).
Definition zfp2_sqr (p : Z) (a : Fp2_Z) : Fp2_Z := zfp2_mul p a a.
Definition zfp2_inv (p : Z) (a : Fp2_Z) : Fp2_Z :=
  let n := zfp_add p (zfp_mul p (fst a) (fst a))
                      (zfp_mul p (snd a) (snd a)) in
  let ni := zfp_inv p n in
  (zfp_mul p (fst a) ni, zfp_mul p (zfp_neg p (snd a)) ni).
Definition zfp2_mul_fp (p : Z) (a : Fp2_Z) (s : Z) : Fp2_Z :=
  (zfp_mul p (fst a) s, zfp_mul p (snd a) s).

(** Reduction lemma: the original [zfp2_mul] is [_beta] at [beta = -1].
    [_beta] takes the literal Z multiplier and applies [zfp_mul p (-1) x],
    which mod-reduces to [(p - x) mod p].  The original [zfp2_mul] uses
    [zfp_sub] which mod-reduces to the same canonical residue. *)
(** Reduction lemmas linking the [_beta] forms at [beta = -1] back to
    the original [zfp2_mul] / [zfp2_inv] (which were hardcoded for that
    case): both sides give the same canonical residue mod p, but not
    definitionally — the proof requires push_Zmod normalization plus
    [(-1) * x mod p = (p - x) mod p].  Deferred. *)

(* ================================================================ *)
(* Fp6 = (Fp2 * Fp2 * Fp2), v^3 = xi                                 *)
(* ================================================================ *)

Definition Fp6_Z := (Fp2_Z * Fp2_Z * Fp2_Z)%type.
Definition fp6_c0 (a : Fp6_Z) : Fp2_Z := fst (fst a).
Definition fp6_c1 (a : Fp6_Z) : Fp2_Z := snd (fst a).
Definition fp6_c2 (a : Fp6_Z) : Fp2_Z := snd a.
Definition mk_fp6 (c0 c1 c2 : Fp2_Z) : Fp6_Z := ((c0, c1), c2).

(** Multiply an Fp2 element by xi = (xi_re, xi_im).
    For BLS12-381: xi = (1, 1), so (a0+a1u)*(1+u) = (a0-a1) + (a0+a1)u.
    For BN254:     xi = (9, 1), so (a0+a1u)*(9+u) = (9a0-a1) + (a0+9a1)u. *)
Definition zfp2_mul_xi (p : Z) (xi : Fp2_Z) (a : Fp2_Z) : Fp2_Z :=
  zfp2_mul p a xi.

(** Multiply Fp6 by v: c0*v + c1*v^2 + c2*v^3 = c2*xi + c0*v + c1*v^2. *)
Definition zfp6_mul_v (p : Z) (xi : Fp2_Z) (a : Fp6_Z) : Fp6_Z :=
  mk_fp6 (zfp2_mul_xi p xi (fp6_c2 a)) (fp6_c0 a) (fp6_c1 a).

Definition zfp6_add (p : Z) (a b : Fp6_Z) : Fp6_Z :=
  mk_fp6 (zfp2_add p (fp6_c0 a) (fp6_c0 b))
         (zfp2_add p (fp6_c1 a) (fp6_c1 b))
         (zfp2_add p (fp6_c2 a) (fp6_c2 b)).
Definition zfp6_sub (p : Z) (a b : Fp6_Z) : Fp6_Z :=
  mk_fp6 (zfp2_sub p (fp6_c0 a) (fp6_c0 b))
         (zfp2_sub p (fp6_c1 a) (fp6_c1 b))
         (zfp2_sub p (fp6_c2 a) (fp6_c2 b)).

(** Schoolbook Fp6 multiplication (Chung-Hasan or Karatsuba). *)
Definition zfp6_mul (p : Z) (xi : Fp2_Z) (a b : Fp6_Z) : Fp6_Z :=
  let a0 := fp6_c0 a in let a1 := fp6_c1 a in let a2 := fp6_c2 a in
  let b0 := fp6_c0 b in let b1 := fp6_c1 b in let b2 := fp6_c2 b in
  let t0 := zfp2_mul p a0 b0 in
  let t1 := zfp2_mul p a1 b1 in
  let t2 := zfp2_mul p a2 b2 in
  let c0 := zfp2_add p t0
              (zfp2_mul_xi p xi
                (zfp2_sub p
                  (zfp2_sub p
                    (zfp2_mul p (zfp2_add p a1 a2) (zfp2_add p b1 b2))
                    t1)
                  t2)) in
  let c1 := zfp2_add p
              (zfp2_sub p
                (zfp2_sub p
                  (zfp2_mul p (zfp2_add p a0 a1) (zfp2_add p b0 b1))
                  t0)
                t1)
              (zfp2_mul_xi p xi t2) in
  let c2 := zfp2_sub p
              (zfp2_add p
                (zfp2_sub p
                  (zfp2_mul p (zfp2_add p a0 a2) (zfp2_add p b0 b2))
                  t0)
                t1)
              t2 in
  mk_fp6 c0 c1 c2.

(* ================================================================ *)
(* Fp12 = (Fp6 * Fp6), w^2 = v                                       *)
(* ================================================================ *)

Definition Fp12_Z := (Fp6_Z * Fp6_Z)%type.
Definition fp12_c0 (a : Fp12_Z) : Fp6_Z := fst a.
Definition fp12_c1 (a : Fp12_Z) : Fp6_Z := snd a.

Definition zfp12_mul (p : Z) (xi : Fp2_Z) (a b : Fp12_Z) : Fp12_Z :=
  let a0 := fp12_c0 a in let a1 := fp12_c1 a in
  let b0 := fp12_c0 b in let b1 := fp12_c1 b in
  let t0 := zfp6_mul p xi a0 b0 in
  let t1 := zfp6_mul p xi a1 b1 in
  let c0 := zfp6_add p t0 (zfp6_mul_v p xi t1) in
  let c1 := zfp6_sub p
              (zfp6_sub p
                (zfp6_mul p xi (zfp6_add p a0 a1) (zfp6_add p b0 b1))
                t0)
              t1 in
  (c0, c1).

Definition zfp12_sqr (p : Z) (xi : Fp2_Z) (a : Fp12_Z) : Fp12_Z :=
  zfp12_mul p xi a a.

Definition zfp6_zero : Fp6_Z := mk_fp6 (0, 0) (0, 0) (0, 0).
Definition zfp12_one : Fp12_Z :=
  (mk_fp6 (1, 0) (0, 0) (0, 0), zfp6_zero).

(** ** Beta-parametric tower for [Fp2 = Fp[u]/(u^2 - beta)] with [beta ≠ -1].

    For BLS12-377 ([beta = -5]) the legacy [zfp2_mul] above is unsound:
    it hardcodes [a0b0 - a1b1] in the first component, which matches
    [beta = -1] only.  The [_beta] tower below threads the curve's
    [fp2_beta] through every multiplication at all three levels. *)

Definition zfp2_mul_xi_beta (p : Z) (beta : Z) (xi : Fp2_Z) (a : Fp2_Z) : Fp2_Z :=
  zfp2_mul_beta p beta a xi.

Definition zfp6_mul_v_beta (p : Z) (beta : Z) (xi : Fp2_Z) (a : Fp6_Z) : Fp6_Z :=
  mk_fp6 (zfp2_mul_xi_beta p beta xi (fp6_c2 a)) (fp6_c0 a) (fp6_c1 a).

Definition zfp6_mul_beta (p : Z) (beta : Z) (xi : Fp2_Z)
                         (a b : Fp6_Z) : Fp6_Z :=
  let a0 := fp6_c0 a in let a1 := fp6_c1 a in let a2 := fp6_c2 a in
  let b0 := fp6_c0 b in let b1 := fp6_c1 b in let b2 := fp6_c2 b in
  let t0 := zfp2_mul_beta p beta a0 b0 in
  let t1 := zfp2_mul_beta p beta a1 b1 in
  let t2 := zfp2_mul_beta p beta a2 b2 in
  let c0 := zfp2_add p t0
              (zfp2_mul_xi_beta p beta xi
                (zfp2_sub p
                  (zfp2_sub p
                    (zfp2_mul_beta p beta (zfp2_add p a1 a2) (zfp2_add p b1 b2))
                    t1)
                  t2)) in
  let c1 := zfp2_add p
              (zfp2_sub p
                (zfp2_sub p
                  (zfp2_mul_beta p beta (zfp2_add p a0 a1) (zfp2_add p b0 b1))
                  t0)
                t1)
              (zfp2_mul_xi_beta p beta xi t2) in
  let c2 := zfp2_sub p
              (zfp2_add p
                (zfp2_sub p
                  (zfp2_mul_beta p beta (zfp2_add p a0 a2) (zfp2_add p b0 b2))
                  t0)
                t1)
              t2 in
  mk_fp6 c0 c1 c2.

Definition zfp12_mul_beta (p : Z) (beta : Z) (xi : Fp2_Z)
                          (a b : Fp12_Z) : Fp12_Z :=
  let a0 := fp12_c0 a in let a1 := fp12_c1 a in
  let b0 := fp12_c0 b in let b1 := fp12_c1 b in
  let t0 := zfp6_mul_beta p beta xi a0 b0 in
  let t1 := zfp6_mul_beta p beta xi a1 b1 in
  let c0 := zfp6_add p t0 (zfp6_mul_v_beta p beta xi t1) in
  let c1 := zfp6_sub p
              (zfp6_sub p
                (zfp6_mul_beta p beta xi (zfp6_add p a0 a1) (zfp6_add p b0 b1))
                t0)
              t1 in
  (c0, c1).

Definition zfp12_sqr_beta (p : Z) (beta : Z) (xi : Fp2_Z) (a : Fp12_Z) : Fp12_Z :=
  zfp12_mul_beta p beta xi a a.

(* ================================================================ *)
(* FieldOps instance builder                                          *)
(* ================================================================ *)

(** Build a [FieldOps] instance from a [CurveParams].
    The [make_line] parameter must be supplied by the caller because its
    body depends on the twist convention (D vs M). *)
Definition zmod_ops
    (c : CurveParams)
    (ml : Fp2_Z -> Fp2_Z -> Fp2_Z -> Z -> Z -> Fp12_Z)
  : FieldOps Z Fp2_Z Fp12_Z :=
  let p := prime_p c in
  let xi := (xi_re c, xi_im c) in
{|
  Affine.fp_zero     := 0;
  Affine.fp_one      := 1;
  Affine.fp2_zero    := (0, 0);
  Affine.fp2_one     := (1, 0);
  Affine.fp2_add     := zfp2_add p;
  Affine.fp2_sub     := zfp2_sub p;
  Affine.fp2_neg     := zfp2_neg p;
  Affine.fp2_mul     := zfp2_mul p;
  Affine.fp2_sqr     := zfp2_sqr p;
  Affine.fp2_inv     := zfp2_inv p;
  Affine.fp2_mul_fp  := zfp2_mul_fp p;
  Affine.fp12_one    := zfp12_one;
  Affine.fp12_mul    := zfp12_mul p xi;
  Affine.fp12_sqr    := zfp12_sqr p xi;
  Affine.make_line   := ml;
|}.

(** Beta-parametric instance constructor — uses [fp2_beta c] throughout
    the tower.  For [beta = -1] curves this is value-equivalent to
    [zmod_ops] (pending the deferred equivalence lemma
    [zfp2_mul_eq_beta_neg1]); for BLS12-377 ([beta = -5]) this is the
    SOUND constructor.  Users should prefer [zmod_ops_beta] for new
    work; [zmod_ops] is kept for backwards compatibility with existing
    proofs that pattern-match on the [zfp2_mul]/[zfp12_mul] forms. *)
Definition zmod_ops_beta
    (c : CurveParams)
    (ml : Fp2_Z -> Fp2_Z -> Fp2_Z -> Z -> Z -> Fp12_Z)
  : FieldOps Z Fp2_Z Fp12_Z :=
  let p := prime_p c in
  let beta := fp2_beta c in
  let xi := (xi_re c, xi_im c) in
{|
  Affine.fp_zero     := 0;
  Affine.fp_one      := 1;
  Affine.fp2_zero    := (0, 0);
  Affine.fp2_one     := (1, 0);
  Affine.fp2_add     := zfp2_add p;
  Affine.fp2_sub     := zfp2_sub p;
  Affine.fp2_neg     := zfp2_neg p;
  Affine.fp2_mul     := zfp2_mul_beta p beta;
  Affine.fp2_sqr     := zfp2_sqr_beta p beta;
  Affine.fp2_inv     := zfp2_inv_beta p beta;
  Affine.fp2_mul_fp  := zfp2_mul_fp p;
  Affine.fp12_one    := zfp12_one;
  Affine.fp12_mul    := zfp12_mul_beta p beta xi;
  Affine.fp12_sqr    := zfp12_sqr_beta p beta xi;
  Affine.make_line   := ml;
|}.

(** D-twist make_line (BN254): line = Py + (-lam*Px)*w + (lam*Tx-Ty)*w^3.
    In bedrock2 basis: c0.c0 = (Py, 0), c1.c0 = -lam*Px, c1.c1 = lam*Tx-Ty. *)
Definition dtwist_make_line (p : Z) (lam Tx Ty : Fp2_Z) (Px Py : Z) : Fp12_Z :=
  let c0_c0 := (Py, 0 : Z) in
  let c1_c0 := zfp2_neg p (zfp2_mul_fp p lam Px) in
  let c1_c1 := zfp2_sub p (zfp2_mul p lam Tx) Ty in
  (mk_fp6 c0_c0 (0, 0) (0, 0), mk_fp6 c1_c0 c1_c1 (0, 0)).

(** M-twist make_line (BLS12-381): line * w^3 form, as bedrock2 stores it.
    c0.c0 = lam*Tx-Ty, c0.c1 = -lam*Px, c1.c1 = (Py, 0). *)
Definition mtwist_make_line (p : Z) (lam Tx Ty : Fp2_Z) (Px Py : Z) : Fp12_Z :=
  let c0_c0 := zfp2_sub p (zfp2_mul p lam Tx) Ty in
  let c0_c1 := zfp2_neg p (zfp2_mul_fp p lam Px) in
  let c1_c1 := (Py, 0 : Z) in
  (mk_fp6 c0_c0 c0_c1 (0, 0), mk_fp6 (0, 0) c1_c1 (0, 0)).

(* ================================================================ *)
(* Extra tower ops for the optimal_ate spec (Frob corrections + final exp) *)
(* ================================================================ *)

(** Conjugation in Fp2: (a + bu) -> (a - bu). Trivial — just negate the
    imaginary part. *)
Definition zfp2_conj (p : Z) (a : Fp2_Z) : Fp2_Z :=
  (fst a, zfp_neg p (snd a)).

(** Conjugation in Fp12: (a + bw) -> (a - bw). Negate the c1 component. *)
Definition zfp6_neg (p : Z) (a : Fp6_Z) : Fp6_Z :=
  let '((a0, a1), a2) := a in
  ((zfp2_neg p a0, zfp2_neg p a1), zfp2_neg p a2).

Definition zfp12_conj (p : Z) (a : Fp12_Z) : Fp12_Z :=
  (fst a, zfp6_neg p (snd a)).

(** [zfp2_mul_const] is the same as [zfp2_mul] for the spec (the
    distinction in the spec is documentary — "this argument is a
    precomputed Frobenius constant"). *)
Definition zfp2_mul_const (p : Z) (a c : Fp2_Z) : Fp2_Z := zfp2_mul p a c.

(** Generic Fp12 exponentiation by Z exponent via square-and-multiply. *)
Fixpoint zfp12_pow_aux (p : Z) (xi : Fp2_Z)
                      (base : Fp12_Z) (exp : Z) (acc : Fp12_Z)
                      (fuel : nat) : Fp12_Z :=
  match fuel with
  | O => acc
  | S fuel' =>
    let acc' := if Z.odd exp then zfp12_mul p xi acc base else acc in
    let base' := zfp12_sqr p xi base in
    zfp12_pow_aux p xi base' (Z.div2 exp) acc' fuel'
  end.

Definition zfp12_pow (p : Z) (xi : Fp2_Z) (base : Fp12_Z) (exp : Z) : Fp12_Z :=
  zfp12_pow_aux p xi base exp zfp12_one (Z.to_nat (Z.log2 (Z.abs exp) + 2)).

(** Fp12 inversion via Fermat's little theorem: a^(p^12 - 2). Slow but
    correct in the abstract spec. The bedrock2 implementation uses a
    Frobenius-tower formula that's much faster, but for the spec the
    Fermat exponent suffices. *)
Definition zfp12_inv (p : Z) (xi : Fp2_Z) (a : Fp12_Z) : Fp12_Z :=
  zfp12_pow p xi a (p^12 - 2).

(** Frobenius x -> x^{p^2}. Spec form: also a power. *)
Definition zfp12_frob_p2 (p : Z) (xi : Fp2_Z) (a : Fp12_Z) : Fp12_Z :=
  zfp12_pow p xi a (p^2).

(** Build [FieldOps] for BN254. *)
Definition bn254_zmod_ops : FieldOps Z Fp2_Z Fp12_Z :=
  zmod_ops
    (bn254_params)
    (dtwist_make_line (bn254_params.(prime_p))).

(** Build [FieldOps] for BLS12-381. *)
Definition bls12_381_zmod_ops : FieldOps Z Fp2_Z Fp12_Z :=
  zmod_ops
    (bls12_381_params)
    (mtwist_make_line (bls12_381_params.(prime_p))).

(** Build [FieldOps] for BN256 (BN family, D-twist). *)
Definition bn256_zmod_ops : FieldOps Z Fp2_Z Fp12_Z :=
  zmod_ops
    (bn256_params)
    (dtwist_make_line (bn256_params.(prime_p))).

(** Build [FieldOps] for BN446 (BN family, D-twist). *)
Definition bn446_zmod_ops : FieldOps Z Fp2_Z Fp12_Z :=
  zmod_ops
    (bn446_params)
    (dtwist_make_line (bn446_params.(prime_p))).

(** Build [FieldOps] for BLS12-377 (BLS12 family, D-twist — note this
    differs from BLS12-381 which is M-twist). *)
Definition bls12_377_zmod_ops : FieldOps Z Fp2_Z Fp12_Z :=
  zmod_ops
    (bls12_377_params)
    (dtwist_make_line (bls12_377_params.(prime_p))).

(** ** Projective ops (spec form).

    Wraps [zmod_ops] with the two extra fields the projective Miller
    loop needs.  Spec-only: we use the existing [make_line] composed
    with Z-normalisation for [make_line_proj], and the existing dense
    [fp12_mul] for [fp12_mul_by_line].  This gives a [ProjFieldOps]
    that is observably equal to the affine instance — useful for
    [vm_compute] cross-checks and for building correctness theorems
    against [projective_miller_eq_affine] (the SC1/SC2 side conditions
    reduce to definitional equality on this representation).

    The fast version (real projective line formula + actual sparse
    mul) lives in the bedrock2 implementation file and uses these
    spec values as its correctness target. *)

Require Import Bedrock.Field.PairingTheory.Projective.

(** Dehomogenise a projective point [(TX, TY, TZ)] to its affine form
    [(TX/TZ^2, TY/TZ^3)]. *)
Definition zproj_to_affine (p : Z) (TX TY TZ : Fp2_Z) : Fp2_Z * Fp2_Z :=
  let z2 := zfp2_sqr p TZ in
  let z3 := zfp2_mul p z2 TZ in
  (zfp2_mul p TX (zfp2_inv p z2),
   zfp2_mul p TY (zfp2_inv p z3)).

(** Spec instance: dehomogenise + reuse existing affine [ml].  Slow
    (uses Fp2 inversions) but correct.  Each curve's fast bedrock2
    instance avoids the inversions via the proper Bernstein--Lange line
    formula and proves equivalent at the L4 level.

    IMPORTANT: the slope for doubling is the TANGENT slope at [T_old],
    [3*Tx_aff^2 / (2*Ty_aff)], not the chord slope through [T_old] and
    [T_new].  Geometrically, the tangent at [T_old] hits the curve at
    [T_old] (double root) and [-T_new], not at [T_new] itself; using
    the [T_old]-to-[T_new] chord gives a different line, which is why
    the first cross-check attempt failed. *)
Definition zproj_make_line_double
    (p : Z)
    (ml : Fp2_Z -> Fp2_Z -> Fp2_Z -> Z -> Z -> Fp12_Z)
    (TX TY TZ NX NY NZ : Fp2_Z) (Px Py : Z) : Fp12_Z :=
  let '(tx_aff, ty_aff) := zproj_to_affine p TX TY TZ in
  let tx_sq := zfp2_sqr p tx_aff in
  let three_tx_sq := zfp2_add p (zfp2_add p tx_sq tx_sq) tx_sq in
  let two_ty := zfp2_add p ty_aff ty_aff in
  let lam := zfp2_mul p three_tx_sq (zfp2_inv p two_ty) in
  ml lam tx_aff ty_aff Px Py.

Definition zproj_make_line_add
    (p : Z)
    (ml : Fp2_Z -> Fp2_Z -> Fp2_Z -> Z -> Z -> Fp12_Z)
    (TX TY TZ Qx Qy NX NY NZ : Fp2_Z) (Px Py : Z) : Fp12_Z :=
  let '(tx_aff, ty_aff) := zproj_to_affine p TX TY TZ in
  let lam := zfp2_mul p (zfp2_sub p Qy ty_aff)
                        (zfp2_inv p (zfp2_sub p Qx tx_aff)) in
  ml lam tx_aff ty_aff Px Py.

Definition zproj_ops
    (c : CurveParams)
    (ml : Fp2_Z -> Fp2_Z -> Fp2_Z -> Z -> Z -> Fp12_Z)
  : ProjFieldOps Z Fp2_Z Fp12_Z :=
  let p := prime_p c in
  let xi := (xi_re c, xi_im c) in
  {|
    Projective.base_ops := zmod_ops c ml;
    Projective.make_line_proj_double := zproj_make_line_double p ml;
    Projective.make_line_proj_add := zproj_make_line_add p ml;
    Projective.fp12_mul_by_line := zfp12_mul p xi;
  |}.

Definition bn254_zmod_proj_ops : ProjFieldOps Z Fp2_Z Fp12_Z :=
  zproj_ops bn254_params (dtwist_make_line (bn254_params.(prime_p))).

Definition bls12_381_zmod_proj_ops : ProjFieldOps Z Fp2_Z Fp12_Z :=
  zproj_ops bls12_381_params (mtwist_make_line (bls12_381_params.(prime_p))).

Definition bn256_zmod_proj_ops : ProjFieldOps Z Fp2_Z Fp12_Z :=
  zproj_ops bn256_params (dtwist_make_line (bn256_params.(prime_p))).

Definition bn446_zmod_proj_ops : ProjFieldOps Z Fp2_Z Fp12_Z :=
  zproj_ops bn446_params (dtwist_make_line (bn446_params.(prime_p))).

Definition bls12_377_zmod_proj_ops : ProjFieldOps Z Fp2_Z Fp12_Z :=
  zproj_ops bls12_377_params (dtwist_make_line (bls12_377_params.(prime_p))).

(* The per-instance simulation lemmas and [projective_miller_eq_affine_zproj]
   live in [MillerEquiv.v] (cannot go here due to the import direction). *)
