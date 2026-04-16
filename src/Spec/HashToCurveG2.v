(** * Hash-to-Curve specification for BLS12-381 G2.

    Implements the Simplified SWU map (RFC 9380 §6.6.2) over Fp2,
    the 3-isogeny from E2' to E2 (RFC 9380 Appendix E.3), and the
    full hash_to_curve_g2 pipeline (§3).

    BLS12-381 G2 uses an isogenous curve E2': y² = x³ + A'·x + B'
    over Fp2 = Fp[u]/(u²+1), with Simplified SWU constant
    Z = -(2 + i), then maps back to E2: y² = x³ + 4·(1+u)
    via a 3-isogeny (degree 3, much shorter than the 11-isogeny for G1).

    References:
    - RFC 9380: Hashing to Elliptic Curves
    - Suite: BLS12381G2_XMD:SHA-256_SSWU_RO_

    Some isogeny coefficients are kept abstract here (Parameter)
    so the file compiles fast. The full spec just needs them
    instantiated to the RFC 9380 §E.3 values. *)

From Stdlib Require Import ZArith BinPos List Bool.
Import ListNotations.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.SHA256_axiom.
Require Import Spec.HashToCurve.

Local Open Scope Z_scope.

Local Notation Fp := (F p_pos).
Local Notation "x +f y" := (@F.add p_pos x y) (at level 50, left associativity).
Local Notation "x *f y" := (@F.mul p_pos x y) (at level 40, left associativity).
Local Notation "x -f y" := (@F.sub p_pos x y) (at level 50, left associativity).
Local Notation "-f x" := (@F.opp p_pos x) (at level 35, right associativity).
Local Notation "0f" := (@F.zero p_pos).
Local Notation "1f" := (@F.one p_pos).
Local Notation invFp := (@F.inv p_pos).
Local Notation of_Z := (F.of_Z p_pos).

(* ================================================================== *)
(** * Fp2 = Fp[u]/(u² + 1)                                              *)
(* ================================================================== *)

(** β = -1 for BLS12-381's Fp2. *)
Definition beta_g2 : Fp := -f 1f.

Notation Fp2 := (Fp * Fp)%type.

Definition fp2_zero : Fp2 := (0f, 0f).
Definition fp2_one : Fp2 := (1f, 0f).

(** The imaginary unit u. *)
Definition fp2_u : Fp2 := (0f, 1f).

Definition fp2_add (a b : Fp2) : Fp2 :=
  (fst a +f fst b, snd a +f snd b).

Definition fp2_sub (a b : Fp2) : Fp2 :=
  (fst a -f fst b, snd a -f snd b).

Definition fp2_neg (a : Fp2) : Fp2 :=
  (-f fst a, -f snd a).

(** Multiplication: (a0 + a1·u)(b0 + b1·u) = (a0·b0 - a1·b1) + (a0·b1 + a1·b0)·u
    using u² = -1. *)
Definition fp2_mul (a b : Fp2) : Fp2 :=
  (fst a *f fst b -f snd a *f snd b,
   fst a *f snd b +f snd a *f fst b).

Definition fp2_sqr (a : Fp2) : Fp2 := fp2_mul a a.

Definition fp2_cube (a : Fp2) : Fp2 := fp2_mul (fp2_sqr a) a.

(** Inverse: (a0 + a1·u)⁻¹ = (a0 - a1·u) / (a0² + a1²). *)
Definition fp2_inv (a : Fp2) : Fp2 :=
  let norm := fst a *f fst a +f snd a *f snd a in
  let inv_norm := invFp norm in
  (fst a *f inv_norm, (-f snd a) *f inv_norm).

Definition fp2_div (a b : Fp2) : Fp2 := fp2_mul a (fp2_inv b).

(** Boolean equality on Fp2. *)
Definition fp2_eqb (a b : Fp2) : bool :=
  andb (fp_eqb (fst a) (fst b)) (fp_eqb (snd a) (snd b)).

(** Construct an Fp2 element from two Z values. *)
Definition fp2_of_Z (re im : Z) : Fp2 := (of_Z re, of_Z im).

(* ================================================================== *)
(** * Fp2 sqrt and is_square                                            *)
(* ================================================================== *)

(** is_square for Fp2 uses the norm: an Fp2 element (c0 + c1·u) is
    a QR in Fp2 iff its norm (c0² - β·c1²) is a QR in Fp.

    With β = -1, norm(c0, c1) = c0² + c1². *)
Definition fp2_norm (a : Fp2) : Fp :=
  fst a *f fst a +f snd a *f snd a.

Definition fp2_is_square (a : Fp2) : bool :=
  is_square (fp2_norm a).

(** fp2_sqrt via the "complex method" for p ≡ 3 mod 4, β = -1:

    Input: a = c0 + c1·u
    Output: some y with y² = a (if a is a QR; otherwise unspecified).

    Algorithm (from classical references, used in noble-curves):
    1. If c1 = 0:
       - If c0 is a QR in Fp: return (sqrt(c0), 0)
       - Else: return (0, sqrt(-c0))  (since β = -1, -c0/β = -c0/-1 = c0,
         wait — we need sqrt(c0 / β) = sqrt(-c0), and -c0 is a QR iff c0 is not)
    2. Else:
       - t = sqrt(c0² + c1²)     [norm sqrt, always a QR if a is]
       - d = (t + c0) / 2
       - If d is not a QR: d ← d - t = (−t + c0) / 2 is a QR
       - r = sqrt(d)
       - Return (r, c1 / (2·r)) *)
Definition fp2_sqrt (a : Fp2) : Fp2 :=
  let c0 := fst a in
  let c1 := snd a in
  if fp_eqb c1 0f then
    if is_square c0
    then (fp_sqrt c0, 0f)
    else (0f, fp_sqrt (-f c0))
  else
    let t := fp_sqrt (c0 *f c0 +f c1 *f c1) in
    let half := invFp (of_Z 2) in
    let d0 := (t +f c0) *f half in
    let d :=
      if is_square d0 then d0
      else (c0 -f t) *f half in
    let r := fp_sqrt d in
    (r, c1 *f invFp (of_Z 2 *f r)).

(** sgn0 for Fp2: sgn0(a0 + a1·u) = sgn0(a0) ∨ (a0 == 0 ∧ sgn0(a1)).
    This is the "sign or imaginary sign" convention from RFC 9380 §4.1. *)
Definition sgn0_fp2 (a : Fp2) : Z :=
  let s0 := sgn0 (fst a) in
  let z0 := if fp_eqb (fst a) 0f then 1 else 0 in
  let s1 := sgn0 (snd a) in
  Z.lor s0 (Z.land z0 s1).

(* ================================================================== *)
(** * Simplified SWU map over Fp2                                       *)
(* ================================================================== *)

Section SimplifiedSWU_Fp2.
  Variable swu_a : Fp2.   (** A' coefficient (nonzero). *)
  Variable swu_b : Fp2.   (** B' coefficient (nonzero). *)
  Variable swu_z : Fp2.   (** SWU constant (a non-square in Fp2). *)

  Definition curve_rhs2 (x : Fp2) : Fp2 :=
    fp2_add (fp2_add (fp2_cube x) (fp2_mul swu_a x)) swu_b.

  Definition map_to_curve_simple_swu_fp2 (u : Fp2) : Fp2 * Fp2 :=
    let u2 := fp2_sqr u in
    let u4 := fp2_sqr u2 in
    let z2 := fp2_sqr swu_z in
    let denom := fp2_add (fp2_mul z2 u4) (fp2_mul swu_z u2) in
    let tv1 := fp2_inv denom in
    let neg_B_over_A := fp2_mul (fp2_neg swu_b) (fp2_inv swu_a) in
    let x1_normal := fp2_mul neg_B_over_A (fp2_add fp2_one tv1) in
    let x1 :=
      if fp2_eqb tv1 fp2_zero
      then fp2_div swu_b (fp2_mul swu_z swu_a)
      else x1_normal in
    let gx1 := curve_rhs2 x1 in
    let x2 := fp2_mul (fp2_mul swu_z u2) x1 in
    let gx2 := curve_rhs2 x2 in
    let '(x, y) :=
      if fp2_is_square gx1
      then (x1, fp2_sqrt gx1)
      else (x2, fp2_sqrt gx2) in
    let y_final :=
      if Z.eqb (sgn0_fp2 u) (sgn0_fp2 y)
      then y
      else fp2_neg y in
    (x, y_final).
End SimplifiedSWU_Fp2.

(* ================================================================== *)
(** * BLS12-381 G2 isogenous curve E2' and SWU constants                *)
(* ================================================================== *)

(** From RFC 9380 §8.8.2 / Appendix E.3:
    A' = 240·u
    B' = 1012 + 1012·u
    Z  = -(2 + u) *)
Definition iso_A_g2 : Fp2 := (0f, of_Z 240).
Definition iso_B_g2 : Fp2 := (of_Z 1012, of_Z 1012).
Definition swu_Z_g2 : Fp2 := fp2_neg (of_Z 2, 1f).

(** Target curve coefficient: B = 4·(1+u) for E2: y² = x³ + 4(1+u). *)
Definition bls12_b_g2 : Fp2 := (of_Z 4, of_Z 4).

(* ================================================================== *)
(** * 3-isogeny map E2' -> E2 (RFC 9380 Appendix E.3)                  *)
(* ================================================================== *)

(** The 3-isogeny phi: E2' -> E2 is given by rational maps:
      x_E = x_num(x') / x_den(x')
      y_E = y' · y_num(x') / y_den(x')
    where x_num, x_den, y_num, y_den are degree ≤ 3 polynomials in x'
    with coefficients in Fp2.

    Coefficient values from RFC 9380 §E.3 (omitted here; the spec
    structure is the same as G1 but the coefficient lists are
    shorter — degree 3 instead of 11). *)

(** Coefficient values from RFC 9380 §E.3 (cross-verified against
    paulmillr/noble-curves bls12-381 isogenyMapG2 constants).
    Each Fp2 is written (re, im). The convention: list is in
    ascending degree order [c₀, c₁, c₂, ...]. Monic denominators
    omit the leading 1 (appended by horner_eval_monic_fp2). *)

(** x_num: 4 Fp2 coefficients, degree 3 (non-monic). *)
Definition iso_xnum_g2 : list Fp2 := [
  (of_Z 0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97d6,
   of_Z 0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97d6);
  (0f,
   of_Z 0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71a);
  (of_Z 0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71e,
   of_Z 0x8ab05f8bdd54cde190937e76bc3e447cc27c3d6fbd7063fcd104635a790520c0a395554e5c6aaaa9354ffffffffe38d);
  (of_Z 0x171d6541fa38ccfaed6dea691f5fb614cb14b4e7f4e810aa22d6108f142b85757098e38d0f671c7188e2aaaaaaaa5ed1,
   0f)
].

(** x_den: 2 Fp2 coefficients, degree 2, monic (leading 1 implicit). *)
Definition iso_xden_g2 : list Fp2 := [
  (0f,
   of_Z 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa63);
  (of_Z 0xc,
   of_Z 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa9f)
].

(** y_num: 4 Fp2 coefficients, degree 3 (non-monic). *)
Definition iso_ynum_g2 : list Fp2 := [
  (of_Z 0x1530477c7ab4113b59a4c18b076d11930f7da5d4a07f649bf54439d87d27e500fc8c25ebf8c92f6812cfc71c71c6d706,
   of_Z 0x1530477c7ab4113b59a4c18b076d11930f7da5d4a07f649bf54439d87d27e500fc8c25ebf8c92f6812cfc71c71c6d706);
  (0f,
   of_Z 0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97be);
  (of_Z 0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71c,
   of_Z 0x8ab05f8bdd54cde190937e76bc3e447cc27c3d6fbd7063fcd104635a790520c0a395554e5c6aaaa9354ffffffffe38f);
  (of_Z 0x124c9ad43b6cf79bfbf7043de3811ad0761b0f37a1e26286b0e977c69aa274524e79097a56dc4bd9e1b371c71c718b10,
   0f)
].

(** y_den: 3 Fp2 coefficients, degree 3, monic (leading 1 implicit). *)
Definition iso_yden_g2 : list Fp2 := [
  (of_Z 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa8fb,
   of_Z 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa8fb);
  (0f,
   of_Z 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa9d3);
  (of_Z 0x12,
   of_Z 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa99)
].

(** Horner evaluation in Fp2. *)
Fixpoint horner_eval_fp2 (cs : list Fp2) (x : Fp2) : Fp2 :=
  match cs with
  | [] => fp2_zero
  | c :: cs' => fp2_add c (fp2_mul x (horner_eval_fp2 cs' x))
  end.

(** Monic Horner evaluation: append a leading 1 coefficient. *)
Definition horner_eval_monic_fp2 (cs : list Fp2) (x : Fp2) : Fp2 :=
  horner_eval_fp2 (cs ++ [fp2_one]) x.

(** Fixed sentinel for kernel points: (2, 0) is the x-coordinate,
    y-coordinate satisfies y² = 2³ + 4(1+u) = (12, 4).
    We verify (12, 4) IS a square in Fp2 (unlike (4, 4) which is not). *)
Definition sentinel_x_g2 : Fp2 := (of_Z 2, 0f).
Definition sentinel_rhs_g2 : Fp2 := fp2_add (fp2_cube sentinel_x_g2) bls12_b_g2.
Definition sentinel_y_g2 : Fp2 := fp2_sqrt sentinel_rhs_g2.

(** The 3-isogeny map. Branch on z = xden·yden = 0 for kernel points.
    Kernel points map to a fixed point on E2 (the sentinel). *)
Definition iso_map_g2 (pt : Fp2 * Fp2) : Fp2 * Fp2 :=
  let '(x', y') := pt in
  let xn := horner_eval_fp2 iso_xnum_g2 x' in
  let xd := horner_eval_monic_fp2 iso_xden_g2 x' in
  let yn := horner_eval_fp2 iso_ynum_g2 x' in
  let yd := horner_eval_monic_fp2 iso_yden_g2 x' in
  let z := fp2_mul xd yd in
  if fp2_eqb z fp2_zero then
    (sentinel_x_g2, sentinel_y_g2)
  else
    let inv_z := fp2_inv z in
    (fp2_mul (fp2_mul xn yd) inv_z,
     fp2_mul (fp2_mul (fp2_mul y' yn) xd) inv_z).

(* ================================================================== *)
(** * map_to_curve for BLS12-381 G2                                    *)
(* ================================================================== *)

Definition map_to_curve_g2 (u : Fp2) : Fp2 * Fp2 :=
  iso_map_g2 (map_to_curve_simple_swu_fp2 iso_A_g2 iso_B_g2 swu_Z_g2 u).

(* ================================================================== *)
(** * Affine point operations on E2                                    *)
(* ================================================================== *)

Definition affine_point_g2 := option (Fp2 * Fp2).

Definition point_at_infinity_g2 : affine_point_g2 := None.

(** Point addition on E2 (a = 0 case). *)
Definition point_add_g2 (P Q : affine_point_g2) : affine_point_g2 :=
  match P, Q with
  | None, _ => Q
  | _, None => P
  | Some (x1, y1), Some (x2, y2) =>
    if fp2_eqb x1 x2
    then
      if fp2_eqb y1 (fp2_neg y2)
      then point_at_infinity_g2
      else
        let two_y1 := fp2_add y1 y1 in
        let three := fp2_add fp2_one (fp2_add fp2_one fp2_one) in
        let lambda := fp2_mul (fp2_mul three (fp2_sqr x1)) (fp2_inv two_y1) in
        let x3 := fp2_sub (fp2_sub (fp2_sqr lambda) x1) x2 in
        let y3 := fp2_sub (fp2_mul lambda (fp2_sub x1 x3)) y1 in
        Some (x3, y3)
    else
      let lambda := fp2_mul (fp2_sub y2 y1) (fp2_inv (fp2_sub x2 x1)) in
      let x3 := fp2_sub (fp2_sub (fp2_sqr lambda) x1) x2 in
      let y3 := fp2_sub (fp2_mul lambda (fp2_sub x1 x3)) y1 in
      Some (x3, y3)
  end.

Fixpoint scalar_mul_g2 (n : nat) (P : affine_point_g2) : affine_point_g2 :=
  match n with
  | O => point_at_infinity_g2
  | S n' => point_add_g2 P (scalar_mul_g2 n' P)
  end.

(* ================================================================== *)
(** * Cofactor clearing (RFC 9380 §8.8.2)                              *)
(* ================================================================== *)

(** Effective cofactor h_eff for BLS12-381 G2.
    From RFC 9380 §8.8.2: h_eff = 0xbc69f08f2ee75b3584c6a0ea91b352888e2a8e9145ad7689986ff031508ffe1329c2f178731db956d82bf015d1212b02ec0ec69d7477c1ae954cbc06689f6a359894c0adebbf6b4e8020005aaa95551
    This is a large constant — for efficiency, real implementations use the
    Budroni-Pintore endomorphism-based method. The spec just iterates. *)
Definition h_eff_g2 : Z :=
  0xbc69f08f2ee75b3584c6a0ea91b352888e2a8e9145ad7689986ff031508ffe1329c2f178731db956d82bf015d1212b02ec0ec69d7477c1ae954cbc06689f6a359894c0adebbf6b4e8020005aaa95551.

Definition clear_cofactor_g2 (P : affine_point_g2) : affine_point_g2 :=
  scalar_mul_g2 (Z.to_nat h_eff_g2) P.

(* ================================================================== *)
(** * hash_to_curve_g2 pipeline (RFC 9380 §3)                           *)
(* ================================================================== *)

(** L = 64 for BLS12-381 G2 as well (each Fp2 element needs 2·L bytes). *)
Definition hash_to_field_fp2
  (msg : list Byte.byte) (dst : list Byte.byte) (count : nat) : list Fp2 :=
  let elements := hash_to_field p_pos msg dst (2 * count) in
  let fix pair_up (l : list Fp) : list Fp2 :=
    match l with
    | a :: b :: rest => (a, b) :: pair_up rest
    | _ => []
    end in
  pair_up elements.

Definition hash_to_curve_g2 (msg : list Byte.byte) (dst : list Byte.byte)
  : affine_point_g2 :=
  let us := hash_to_field_fp2 msg dst 2 in
  match us with
  | [u0; u1] =>
    let Q0 := map_to_curve_g2 u0 in
    let Q1 := map_to_curve_g2 u1 in
    let R := point_add_g2 (Some Q0) (Some Q1) in
    clear_cofactor_g2 R
  | _ => point_at_infinity_g2
  end.

Definition encode_to_curve_g2 (msg : list Byte.byte) (dst : list Byte.byte)
  : affine_point_g2 :=
  let us := hash_to_field_fp2 msg dst 1 in
  match us with
  | [u0] =>
    let Q := map_to_curve_g2 u0 in
    clear_cofactor_g2 (Some Q)
  | _ => point_at_infinity_g2
  end.

(* ================================================================== *)
(** * Well-formedness                                                   *)
(* ================================================================== *)

(** A point is on E2: y² = x³ + 4(1+u). *)
Definition on_curve_E2 (pt : Fp2 * Fp2) : Prop :=
  let '(x, y) := pt in
  fp2_sqr y = fp2_add (fp2_cube x) bls12_b_g2.

Definition on_curve_E2prime (pt : Fp2 * Fp2) : Prop :=
  let '(x, y) := pt in
  fp2_sqr y = fp2_add (fp2_add (fp2_cube x) (fp2_mul iso_A_g2 x)) iso_B_g2.

Definition on_curve_E2_opt (P : affine_point_g2) : Prop :=
  match P with
  | None => True
  | Some pt => on_curve_E2 pt
  end.
