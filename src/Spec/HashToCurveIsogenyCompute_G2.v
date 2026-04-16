(** * G2 isogeny polynomial identity verification at the Z×Z level.

    Mirrors HashToCurveIsogenyCompute.v but operates over Z×Z (Fp2 at the Z level).
    Verifies the degree-15 polynomial identity for the 3-isogeny E2' → E2
    using native_compute for all modular arithmetic. *)

From Stdlib Require Import ZArith BinPos List Bool.
Import ListNotations.
Require Import Spec.HashToCurve.
Require Import Spec.HashToCurveG2.

Local Open Scope Z_scope.

Definition p_Z : Z := Z.pos p_pos.

(** Z×Z representation of Fp2 elements. *)
Definition Zp2 := (Z * Z)%type.

Definition zp2_add (a b : Zp2) : Zp2 :=
  ((fst a + fst b) mod p_Z, (snd a + snd b) mod p_Z).

Definition zp2_sub (a b : Zp2) : Zp2 :=
  ((fst a - fst b) mod p_Z, (snd a - snd b) mod p_Z).

Definition zp2_mul (a b : Zp2) : Zp2 :=
  ((fst a * fst b - snd a * snd b) mod p_Z,
   (fst a * snd b + snd a * fst b) mod p_Z).

Definition zp2_zero : Zp2 := (0, 0).
Definition zp2_one : Zp2 := (1, 0).

(** Polynomial evaluation at Z×Z level (Horner's method). *)
Fixpoint poly_eval_zp2 (cs : list Zp2) (x : Zp2) : Zp2 :=
  match cs with
  | [] => zp2_zero
  | c :: cs' => zp2_add c (zp2_mul x (poly_eval_zp2 cs' x))
  end.

Definition poly_eval_monic_zp2 (cs : list Zp2) (x : Zp2) : Zp2 :=
  poly_eval_zp2 (cs ++ [zp2_one]) x.

(** Polynomial multiplication at Z×Z level. *)
Definition zp2_scale (c : Zp2) (cs : list Zp2) : list Zp2 :=
  map (zp2_mul c) cs.

Fixpoint poly_add_zp2 (f g : list Zp2) : list Zp2 :=
  match f, g with
  | [], _ => g
  | _, [] => f
  | a :: f', b :: g' => zp2_add a b :: poly_add_zp2 f' g'
  end.

Fixpoint poly_mul_zp2 (f g : list Zp2) : list Zp2 :=
  match f with
  | [] => []
  | a :: f' => poly_add_zp2 (zp2_scale a g) (zp2_zero :: poly_mul_zp2 f' g)
  end.

Definition poly_sqr_zp2 (f : list Zp2) : list Zp2 := poly_mul_zp2 f f.
Definition poly_cube_zp2 (f : list Zp2) : list Zp2 := poly_mul_zp2 (poly_sqr_zp2 f) f.

(** Isogeny coefficient lists as Z×Z values. *)

Definition xnum_Z : list Zp2 := Eval native_compute in
  map (fun c => (Crypto.Spec.ModularArithmetic.F.to_Z (fst c),
                 Crypto.Spec.ModularArithmetic.F.to_Z (snd c)))
      iso_xnum_g2.

Definition xden_Z : list Zp2 := Eval native_compute in
  map (fun c => (Crypto.Spec.ModularArithmetic.F.to_Z (fst c),
                 Crypto.Spec.ModularArithmetic.F.to_Z (snd c)))
      (iso_xden_g2 ++ [(Crypto.Spec.ModularArithmetic.F.one,
                         @Crypto.Spec.ModularArithmetic.F.zero p_pos)]).

Definition ynum_Z : list Zp2 := Eval native_compute in
  map (fun c => (Crypto.Spec.ModularArithmetic.F.to_Z (fst c),
                 Crypto.Spec.ModularArithmetic.F.to_Z (snd c)))
      iso_ynum_g2.

Definition yden_Z : list Zp2 := Eval native_compute in
  map (fun c => (Crypto.Spec.ModularArithmetic.F.to_Z (fst c),
                 Crypto.Spec.ModularArithmetic.F.to_Z (snd c)))
      (iso_yden_g2 ++ [(Crypto.Spec.ModularArithmetic.F.one,
                         @Crypto.Spec.ModularArithmetic.F.zero p_pos)]).

Definition A_Z : Zp2 := Eval native_compute in
  (Crypto.Spec.ModularArithmetic.F.to_Z (fst iso_A_g2),
   Crypto.Spec.ModularArithmetic.F.to_Z (snd iso_A_g2)).

Definition B_Z : Zp2 := Eval native_compute in
  (Crypto.Spec.ModularArithmetic.F.to_Z (fst iso_B_g2),
   Crypto.Spec.ModularArithmetic.F.to_Z (snd iso_B_g2)).

Definition b_Z : Zp2 := (4, 4).

(** Build the identity polynomials:
    LHS = curve_eprime(x) · ynum² · xden³
    RHS = xnum³ · yden² + b · xden³ · yden² *)

(* curve E2'(x) = x³ + A·x + B as a polynomial *)
Definition curve_eprime_poly : list Zp2 := [B_Z; A_Z; zp2_zero; zp2_one].

Definition lhs_poly : list Zp2 := Eval native_compute in
  poly_mul_zp2 (poly_mul_zp2 curve_eprime_poly (poly_sqr_zp2 ynum_Z))
               (poly_cube_zp2 xden_Z).

Definition rhs_poly : list Zp2 := Eval native_compute in
  poly_add_zp2
    (poly_mul_zp2 (poly_cube_zp2 xnum_Z) (poly_sqr_zp2 yden_Z))
    (poly_mul_zp2 (zp2_scale b_Z (poly_cube_zp2 xden_Z)) (poly_sqr_zp2 yden_Z)).

(** The polynomial identity check: all coefficients of LHS - RHS are zero mod p. *)
Definition diff_poly : list Zp2 := Eval native_compute in
  poly_add_zp2 lhs_poly (map (fun c => zp2_sub zp2_zero c) rhs_poly).

Lemma isogeny_poly_identity :
  forallb (fun c => andb (Z.eqb (fst c) 0) (Z.eqb (snd c) 0)) diff_poly = true.
Proof. native_compute. reflexivity. Qed.
