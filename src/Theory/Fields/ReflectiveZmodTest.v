(** Test suite for rpull_Zmod reflective tactic *)

From Stdlib Require Import ZArith List.
From Theory.Fields Require Import ReflectiveZmod ReflectiveZmodTac.
Import ListNotations.

Local Open Scope Z_scope.

(** Simple: (a mod m + b mod m) mod m = (a + b) mod m *)
Lemma test_add (a b m : Z) :
  ((a mod m) + (b mod m)) mod m = (a + b) mod m.
Proof. rpull_Zmod. Qed.

(** Simple: (a mod m * b mod m) mod m = (a * b) mod m *)
Lemma test_mul (a b m : Z) :
  ((a mod m) * (b mod m)) mod m = (a * b) mod m.
Proof. rpull_Zmod. Qed.

(** Nested: ((a mod m + b) mod m * c mod m) mod m = ((a+b)*c) mod m *)
Lemma test_nested (a b c m : Z) :
  (((a mod m) + b) mod m * (c mod m)) mod m = ((a + b) * c) mod m.
Proof. rpull_Zmod. Qed.

(** Deep: point-addition-like expression (6 variables, many operations) *)
Lemma test_deep (x1 x2 y1 y2 z1 z2 tb m : Z) :
  (((((y1 mod m * y2 mod m) mod m + (x1 mod m * x2 mod m) mod m) mod m
      * (tb mod m)) mod m
     - (z1 mod m * z2 mod m) mod m) mod m) mod m
  = ((y1 * y2 + x1 * x2) * tb - z1 * z2) mod m.
Proof. rpull_Zmod. Qed.

(** Reflexivity case: both sides identical with mods *)
Lemma test_refl (a b m : Z) :
  ((a mod m) * (b mod m)) mod m = ((a mod m) * (b mod m)) mod m.
Proof. rpull_Zmod. Qed.

(** Sub and opp *)
Lemma test_sub_opp (a b m : Z) :
  ((a mod m) - (b mod m)) mod m = (a - b) mod m.
Proof. rpull_Zmod. Qed.

(** Complex atoms: terms containing m as subterm but not as mod *)
Definition foo (m x : Z) : Z := x * m + 1.

Lemma test_complex_atoms (m x y : Z) :
  ((foo m x mod m) + (foo m y mod m)) mod m = (foo m x + foo m y) mod m.
Proof. rpull_Zmod. Qed.

(** Simulate push_mont output: atoms are eval(from_mont(val ...)) *)
Lemma test_opaque_atoms (f g h m : Z) :
  ((f mod m * g mod m) mod m + h mod m) mod m = (f * g + h) mod m.
Proof. rpull_Zmod. Qed.

(** Simulate MontgomeryCurveSpecs: atoms contain m as subterm *)
Section WithM.
  Variable m : Z.
  Variable f : Z -> Z.

  Lemma test_atom_with_m (a b : Z) :
    ((f a mod m) + (f b mod m)) mod m = (f a + f b) mod m.
  Proof. rpull_Zmod. Qed.

  Lemma test_deep_with_m (a b c d : Z) :
    (((f a mod m) * (f b mod m)) mod m - ((f c mod m) + (f d mod m)) mod m) mod m
    = (f a * f b - (f c + f d)) mod m.
  Proof. rpull_Zmod. Qed.
End WithM.

(** Real-world: 30-term point addition style with mixed mod depths *)
Lemma test_point_add (x1 x2 y1 y2 z1 z2 tb a m : Z) :
  ((((x1 mod m * x2 mod m) mod m - (y1 mod m * y2 mod m) mod m) mod m
    * tb mod m) mod m
   + (z1 mod m * z2 mod m) mod m
   + (a mod m * ((x1 mod m + y1 mod m) mod m * (x2 mod m + y2 mod m) mod m) mod m) mod m) mod m
  = ((x1 * x2 - y1 * y2) * tb + z1 * z2 + a * ((x1 + y1) * (x2 + y2))) mod m.
Proof. rpull_Zmod. Qed.
