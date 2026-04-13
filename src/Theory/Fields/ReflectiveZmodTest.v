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
