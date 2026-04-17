(** * BN Frobenius constant verification — generic infrastructure.

    Provides Fp2 arithmetic, fast exponentiation, and limb packing
    used by BN254/BN256/BN446 Frobenius verification files.

    Reduces ~80 lines of duplicated boilerplate per curve. *)

Require Import Coq.ZArith.ZArith.

Local Open Scope Z_scope.

(* === Fp2 arithmetic (in Z) === *)
(* Fp2 = Fp[u]/(u^2 + 1). Element (a, b) represents a + b*u. *)

Definition fp2_mul (p : Z) (x y : Z * Z) : Z * Z :=
  let '(a0, a1) := x in
  let '(b0, b1) := y in
  ((a0*b0 - a1*b1) mod p, (a0*b1 + a1*b0) mod p).

(* Fast modular exponentiation in Fp2 (square-and-multiply) *)
Fixpoint fp2_pow_pos (p : Z) (x : Z * Z) (n : positive) : Z * Z :=
  match n with
  | xH => x
  | xO n' => let r := fp2_pow_pos p x n' in fp2_mul p r r
  | xI n' => let r := fp2_pow_pos p x n' in fp2_mul p (fp2_mul p r r) x
  end.

Definition fp2_pow (p : Z) (x : Z * Z) (n : Z) : Z * Z :=
  match n with
  | Z0 => (1 mod p, 0)
  | Zpos n' => fp2_pow_pos p x n'
  | Zneg _ => (0, 0)
  end.

(* === Limb packing === *)

(* Pack k 64-bit limbs (LE order) into a single Z *)
Definition pack4 (l0 l1 l2 l3 : Z) : Z :=
  l0 + l1 * 2^64 + l2 * 2^128 + l3 * 2^192.

Definition pack7 (l0 l1 l2 l3 l4 l5 l6 : Z) : Z :=
  l0 + l1 * 2^64 + l2 * 2^128 + l3 * 2^192 +
  l4 * 2^256 + l5 * 2^320 + l6 * 2^384.

(* === Montgomery conversion === *)

(* For an n-limb representation, R = 2^(64n) *)
Definition R256 : Z := 2^256.   (* 4 limbs *)
Definition R448 : Z := 2^448.   (* 7 limbs *)

Definition to_mont256 (p x : Z) : Z := (x * R256) mod p.
Definition to_mont448 (p x : Z) : Z := (x * R448) mod p.
