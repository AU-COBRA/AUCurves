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

(** * Tests for rpush_Zmod (push direction) *)

Lemma test_push_simple (a b m : Z) :
  (a + b) mod m = ((a mod m) + (b mod m)) mod m.
Proof. rpush_Zmod. Qed.

Lemma test_push_mul (a b c m : Z) :
  (a * (b + c)) mod m = ((a mod m) * ((b mod m) + (c mod m)) mod m) mod m.
Proof. rpush_Zmod. Qed.

(** * Tests for push_mont-style compound atoms *)

(** Post-push_mont style atom: [eval (from_mont (val x))] occurring multiple
    times.  This mimics the atom shape produced by [evfrom_val_{add,sub,mul}]
    rewrites in [MontgomeryCurveSpecs].  Identical compound atoms must be
    identified by the reifier even when they contain function applications. *)
Lemma test_evfrom_atoms
    (m : Z) (val : Z -> Z) (eval : Z -> Z) (from_mont : Z -> Z) (x y : Z) :
  ((eval (from_mont (val x)) mod m) * (eval (from_mont (val y)) mod m)) mod m
  = (eval (from_mont (val x)) * eval (from_mont (val y))) mod m.
Proof. rpull_Zmod. Qed.

(** Deeper post-push_mont goal: same compound atom appears multiple times on
    both sides, mixed with arithmetic, like the point-addition goals
    produced after [push_mont] in MontgomeryCurveSpecs. *)
Lemma test_evfrom_atoms_deep
    (m : Z) (val : Z -> Z) (eval : Z -> Z) (from_mont : Z -> Z)
    (x y z : Z) :
  (((eval (from_mont (val x)) mod m * eval (from_mont (val y)) mod m) mod m
      + eval (from_mont (val z)) mod m) mod m
   - (eval (from_mont (val x)) mod m * eval (from_mont (val x)) mod m) mod m) mod m
  = (eval (from_mont (val x)) * eval (from_mont (val y))
     + eval (from_mont (val z))
     - eval (from_mont (val x)) * eval (from_mont (val x))) mod m.
Proof. rpull_Zmod. Qed.

(** Simulate the exact [+m/-m/*m] reification: atom form with [val (x +m y)]
    compound.  A compound atom [eval (from_mont (val (op x y)))] should reify
    as a single variable whenever it reappears. *)
Section EvFromCompound.
  Variable m : Z.
  Variable val : Z -> Z.
  Variable eval : Z -> Z.
  Variable from_mont : Z -> Z.
  Variable addm : Z -> Z -> Z.  (* stands in for [+m] *)

  Lemma test_evfrom_compound_atom (x y : Z) :
    ((eval (from_mont (val (addm x y))) mod m)
       * (eval (from_mont (val (addm x y))) mod m)) mod m
    = (eval (from_mont (val (addm x y)))
       * eval (from_mont (val (addm x y)))) mod m.
  Proof. rpull_Zmod. Qed.
End EvFromCompound.
