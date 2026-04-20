(** * BLS24-509 tower arithmetic using generic extension operations.

    Tower: Fp → Fp2 → Fp4 → Fp8 → Fp24

      Fp2  = Fp[u]  / (u²+1)         β = -1
      Fp4  = Fp2[v] / (v²-(1+u))     ξ₂ = (1,1) in Fp2
      Fp8  = Fp4[w] / (w²-v)         ξ₄ = v (generator of Fp4)
      Fp24 = Fp8[t] / (t³-w)         ξ₈ = w (generator of Fp8)

    Each layer is built from QuadraticExtensionsAbstract (degree 2)
    or CubicExtensionsAbstract (degree 3), parameterized by
    the base field's FieldParameters instance and the nonresidue.

    This file defines:
    - Type aliases (Fp2, Fp4, Fp8, Fp24)
    - Gallina arithmetic at each level
    - mul_by_nonresidue functions (fp2_mul_xi, fp4_mul_by_v, fp8_mul_by_w)
    - The BLS24-509 seed and parametric prime
*)

From Coq Require Import ZArith.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Field.FieldExtensions.Theory.QuadraticExtensionsAbstract.
Require Import Bedrock.Field.FieldExtensions.Theory.CubicExtensionsAbstract.

Local Open Scope Z_scope.

Section BLS24_Tower.
  Variable p : positive.

  (* ================================================================ *)
  (** ** Base field Fp and type aliases                                *)
  (* ================================================================ *)

  Local Notation Fp := (F p).
  Local Notation Fp2 := (Fp * Fp)%type.
  Local Notation Fp4 := (Fp2 * Fp2)%type.
  Local Notation Fp8 := (Fp4 * Fp4)%type.
  Local Notation Fp24 := (Fp8 * Fp8 * Fp8)%type.

  (* ================================================================ *)
  (** ** Fp2 = Fp[u]/(u²+1), β = -1                                  *)
  (* ================================================================ *)

  (** Fp2 element (a₀, a₁) represents a₀ + a₁·u where u² = -1. *)

  Definition fp2_zero : Fp2 := (F.zero, F.zero).
  Definition fp2_one  : Fp2 := (F.one, F.zero).

  Definition fp2_add (a b : Fp2) : Fp2 :=
    (F.add (fst a) (fst b), F.add (snd a) (snd b)).

  Definition fp2_sub (a b : Fp2) : Fp2 :=
    (F.sub (fst a) (fst b), F.sub (snd a) (snd b)).

  Definition fp2_neg (a : Fp2) : Fp2 :=
    (F.opp (fst a), F.opp (snd a)).

  (** Fp2 mul: (a₀+a₁u)(b₀+b₁u) = (a₀b₀ - a₁b₁) + (a₀b₁+a₁b₀)u
      Uses β = -1: β·a₁b₁ = -a₁b₁. *)
  Definition fp2_mul (a b : Fp2) : Fp2 :=
    let a0 := fst a in let a1 := snd a in
    let b0 := fst b in let b1 := snd b in
    (F.sub (F.mul a0 b0) (F.mul a1 b1),
     F.add (F.mul a0 b1) (F.mul a1 b0)).

  Definition fp2_sqr (a : Fp2) : Fp2 :=
    let a0 := fst a in let a1 := snd a in
    (F.sub (F.mul a0 a0) (F.mul a1 a1),
     F.add (F.mul a0 a1) (F.mul a0 a1)).

  Definition fp2_inv (a : Fp2) : Fp2 :=
    let a0 := fst a in let a1 := snd a in
    let norm := F.add (F.mul a0 a0) (F.mul a1 a1) in (* a₀²+a₁² since β=-1 *)
    let inv_norm := F.inv norm in
    (F.mul a0 inv_norm, F.mul (F.opp a1) inv_norm).

  Definition fp2_conjugate (a : Fp2) : Fp2 := (fst a, F.opp (snd a)).

  (* ================================================================ *)
  (** ** Fp2 → Fp4: multiply by ξ₂ = (1,1) = 1+u in Fp2             *)
  (* ================================================================ *)

  (** fp2_mul_xi(a) = (1+u)·a = (a₀-a₁, a₀+a₁) using u²=-1. *)
  Definition fp2_mul_xi (a : Fp2) : Fp2 :=
    (F.sub (fst a) (snd a), F.add (fst a) (snd a)).

  (* ================================================================ *)
  (** ** Fp4 = Fp2[v]/(v²-(1+u))                                     *)
  (* ================================================================ *)

  (** An Fp4 element (c₀, c₁) represents c₀ + c₁·v where v² = 1+u. *)

  Definition fp4_zero : Fp4 := (fp2_zero, fp2_zero).
  Definition fp4_one  : Fp4 := (fp2_one, fp2_zero).

  Definition fp4_add (a b : Fp4) : Fp4 :=
    (fp2_add (fst a) (fst b), fp2_add (snd a) (snd b)).
  Definition fp4_sub (a b : Fp4) : Fp4 :=
    (fp2_sub (fst a) (fst b), fp2_sub (snd a) (snd b)).
  Definition fp4_neg (a : Fp4) : Fp4 :=
    (fp2_neg (fst a), fp2_neg (snd a)).

  (** Fp4 mul: (c₀+c₁v)(d₀+d₁v) = (c₀d₀ + ξ₂·c₁d₁) + (c₀d₁+c₁d₀)v *)
  Definition fp4_mul (a b : Fp4) : Fp4 :=
    let a0 := fst a in let a1 := snd a in
    let b0 := fst b in let b1 := snd b in
    (fp2_add (fp2_mul a0 b0) (fp2_mul_xi (fp2_mul a1 b1)),
     fp2_add (fp2_mul a0 b1) (fp2_mul a1 b0)).

  Definition fp4_inv (a : Fp4) : Fp4 :=
    let a0 := fst a in let a1 := snd a in
    let norm := fp2_sub (fp2_mul a0 a0) (fp2_mul_xi (fp2_mul a1 a1)) in
    let inv_norm := fp2_inv norm in
    (fp2_mul a0 inv_norm, fp2_mul (fp2_neg a1) inv_norm).

  (* ================================================================ *)
  (** ** Fp4 → Fp8: multiply by ξ₄ = v (the Fp4 generator)           *)
  (* ================================================================ *)

  (** fp4_mul_by_v(a) = v·(a₀+a₁v) = ξ₂·a₁ + a₀·v *)
  Definition fp4_mul_by_v (a : Fp4) : Fp4 :=
    (fp2_mul_xi (snd a), fst a).

  (* ================================================================ *)
  (** ** Fp8 = Fp4[w]/(w²-v)                                         *)
  (* ================================================================ *)

  (** An Fp8 element (e₀, e₁) represents e₀ + e₁·w where w² = v. *)

  Definition fp8_zero : Fp8 := (fp4_zero, fp4_zero).
  Definition fp8_one  : Fp8 := (fp4_one, fp4_zero).

  Definition fp8_add (a b : Fp8) : Fp8 :=
    (fp4_add (fst a) (fst b), fp4_add (snd a) (snd b)).
  Definition fp8_sub (a b : Fp8) : Fp8 :=
    (fp4_sub (fst a) (fst b), fp4_sub (snd a) (snd b)).
  Definition fp8_neg (a : Fp8) : Fp8 :=
    (fp4_neg (fst a), fp4_neg (snd a)).

  (** Fp8 mul: uses ξ₄ = v as nonresidue *)
  Definition fp8_mul (a b : Fp8) : Fp8 :=
    let a0 := fst a in let a1 := snd a in
    let b0 := fst b in let b1 := snd b in
    (fp4_add (fp4_mul a0 b0) (fp4_mul_by_v (fp4_mul a1 b1)),
     fp4_add (fp4_mul a0 b1) (fp4_mul a1 b0)).

  Definition fp8_inv (a : Fp8) : Fp8 :=
    let a0 := fst a in let a1 := snd a in
    let norm := fp4_sub (fp4_mul a0 a0) (fp4_mul_by_v (fp4_mul a1 a1)) in
    let inv_norm := fp4_inv norm in
    (fp4_mul a0 inv_norm, fp4_mul (fp4_neg a1) inv_norm).

  (* ================================================================ *)
  (** ** Fp8 → Fp24: multiply by ξ₈ = w (the Fp8 generator)          *)
  (* ================================================================ *)

  (** fp8_mul_by_w(a) = w·(a₀+a₁w) = ξ₄·a₁ + a₀·w = (v·a₁, a₀) *)
  Definition fp8_mul_by_w (a : Fp8) : Fp8 :=
    (fp4_mul_by_v (snd a), fst a).

  (* ================================================================ *)
  (** ** Fp24 = Fp8[t]/(t³-w)                                        *)
  (* ================================================================ *)

  (** An Fp24 element ((f₀, f₁), f₂) represents f₀ + f₁·t + f₂·t²
      where t³ = w. *)

  Definition fp24_c0 (x : Fp24) : Fp8 := fst (fst x).
  Definition fp24_c1 (x : Fp24) : Fp8 := snd (fst x).
  Definition fp24_c2 (x : Fp24) : Fp8 := snd x.
  Definition fp24_build (c0 c1 c2 : Fp8) : Fp24 := ((c0, c1), c2).

  Definition fp24_zero : Fp24 := fp24_build fp8_zero fp8_zero fp8_zero.
  Definition fp24_one  : Fp24 := fp24_build fp8_one  fp8_zero fp8_zero.

  Definition fp24_add (a b : Fp24) : Fp24 :=
    fp24_build (fp8_add (fp24_c0 a) (fp24_c0 b))
               (fp8_add (fp24_c1 a) (fp24_c1 b))
               (fp8_add (fp24_c2 a) (fp24_c2 b)).

  Definition fp24_sub (a b : Fp24) : Fp24 :=
    fp24_build (fp8_sub (fp24_c0 a) (fp24_c0 b))
               (fp8_sub (fp24_c1 a) (fp24_c1 b))
               (fp8_sub (fp24_c2 a) (fp24_c2 b)).

  Definition fp24_neg (a : Fp24) : Fp24 :=
    fp24_build (fp8_neg (fp24_c0 a))
               (fp8_neg (fp24_c1 a))
               (fp8_neg (fp24_c2 a)).

  (** Multiply by t: t·(f₀+f₁t+f₂t²) = w·f₂ + f₀·t + f₁·t² *)
  Definition fp24_mul_by_t (a : Fp24) : Fp24 :=
    fp24_build (fp8_mul_by_w (fp24_c2 a))
               (fp24_c0 a)
               (fp24_c1 a).

  (** Fp24 Karatsuba multiplication *)
  Definition fp24_mul (a b : Fp24) : Fp24 :=
    let a0 := fp24_c0 a in let a1 := fp24_c1 a in let a2 := fp24_c2 a in
    let b0 := fp24_c0 b in let b1 := fp24_c1 b in let b2 := fp24_c2 b in
    let a0b0 := fp8_mul a0 b0 in
    let a1b1 := fp8_mul a1 b1 in
    let a2b2 := fp8_mul a2 b2 in
    let t0 := fp8_sub (fp8_sub (fp8_mul (fp8_add a1 a2) (fp8_add b1 b2))
                                a1b1) a2b2 in
    let c0 := fp8_add a0b0 (fp8_mul_by_w t0) in
    let t1 := fp8_sub (fp8_sub (fp8_mul (fp8_add a0 a1) (fp8_add b0 b1))
                                a0b0) a1b1 in
    let c1 := fp8_add t1 (fp8_mul_by_w a2b2) in
    let t2 := fp8_sub (fp8_sub (fp8_mul (fp8_add a0 a2) (fp8_add b0 b2))
                                a0b0) a2b2 in
    let c2 := fp8_add t2 a1b1 in
    fp24_build c0 c1 c2.

  (** Fp24 conjugation (for easy part of final exp):
      conj(f₀+f₁t+f₂t²) = f₀-f₁t+f₂t² when using w²=v, t³=w structure *)
  Definition fp24_conjugate (a : Fp24) : Fp24 :=
    fp24_build (fp24_c0 a) (fp8_neg (fp24_c1 a)) (fp24_c2 a).

  (* ================================================================ *)
  (** ** BLS24-509 curve parameters                                   *)
  (* ================================================================ *)

  (** The BLS parameter (seed). *)
  Definition bls24_z : Z := -(0x800000ffff801).

  (** Parametric prime: p(z) = (z-1)²·(z⁸-z⁴+1)/3 + z *)
  Definition bls24_prime (z : Z) : Z :=
    ((z - 1)^2 * (z^8 - z^4 + 1)) / 3 + z.

  (** Subgroup order: r(z) = z⁸ - z⁴ + 1 *)
  Definition bls24_order (z : Z) : Z :=
    z^8 - z^4 + 1.

  (** Curve: y² = x³ + b, b = 1 *)
  Definition bls24_b : Fp := F.of_Z p 1.

End BLS24_Tower.
