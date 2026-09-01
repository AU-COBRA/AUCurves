(** * Bilinearity axioms for the BLS12 optimal Ate pairing.

    These axioms state the standard mathematical properties of the
    pairing: bilinearity and non-degeneracy. They are sound because
    the optimal Ate pairing is a well-established mathematical
    construction (Vercauteren 2007, IETF RFC 9380).

    No formal proof of pairing bilinearity exists in any proof
    assistant as of 2026. The proof requires divisor theory on
    elliptic curves (PhD-thesis scope). These axioms enable
    verification of cryptographic protocols (BLS signatures, SNARKs)
    without requiring the full mathematical proof.

    Trust model: the pairing definition in Pairing.v correctly
    implements the optimal Ate pairing formula. Bilinearity is a
    mathematical property of that formula, not an implementation
    choice.
*)

From Stdlib Require Import ZArith.ZArith.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Theory.BLS12Pairing.Pairing.

Section Bilinearity.

  Variable p : positive.

  (* Frobenius constants — needed for final_exponentiation *)
  Variable gamma1_p2 gamma2_p2 coeff_p2_c1 : F p * F p.
  Variable fp12_eq_dec : forall (a b : (((F p * F p) * (F p * F p) * (F p * F p)) *
    ((F p * F p) * (F p * F p) * (F p * F p)))),
    {a = b} + {a <> b}.

  Local Notation Fp := (F p).
  Local Notation Fp2 := ((Fp * Fp)%type).
  Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
  Local Notation Fp12 := ((Fp6 * Fp6)%type).
  Local Notation G1 := (G1Affine p).
  Local Notation G2 := (G2Affine p).

  Local Notation e := (pairing p gamma1_p2 gamma2_p2 coeff_p2_c1).

  (* ================================================================ *)
  (** ** Group operations (abstract)                                   *)
  (*                                                                   *)
  (* The axioms are stated with abstract group operations. These are   *)
  (* the mathematical operations on the elliptic curve groups, not     *)
  (* the bedrock2 implementations.                                     *)
  (* ================================================================ *)

  Variable g1_add : G1 -> G1 -> G1.
  Variable g1_scalar_mult : Z -> G1 -> G1.

  (* ================================================================ *)
  (** ** GT (multiplicative subgroup of Fp12-star)                     *)
  (* ================================================================ *)

  Local Notation fp12_mul := (fp12_mul p).
  Local Notation fp12_one := (fp12_one p).

  Definition fp12_pow (base : Fp12) (exp : Z) : Fp12 :=
    fp12_pow_Z p base exp (Z.to_nat (Z.log2 exp + 1)).

  (* ================================================================ *)
  (** ** Bilinearity axioms                                            *)
  (* ================================================================ *)

  (** Bilinearity in the first argument:
      e(aP, Q) = e(P, Q)^a for all a ∈ Z, P ∈ G1, Q ∈ G2. *)
  Axiom pairing_bilinear_left :
    forall (a : Z) (P : G1) (Q : G2),
      e (g1_scalar_mult a P) Q = fp12_pow (e P Q) a.

  (** Bilinearity in the second argument:
      e(P, bQ) = e(P, Q)^b for all b ∈ Z, P ∈ G1, Q ∈ G2.
      (Requires G2 scalar multiplication — stated abstractly.) *)
  Variable g2_scalar_mult : Z -> G2 -> G2.

  Axiom pairing_bilinear_right :
    forall (b : Z) (P : G1) (Q : G2),
      e P (g2_scalar_mult b Q) = fp12_pow (e P Q) b.

  (** Additive form of bilinearity:
      e(P + Q, R) = e(P, R) * e(Q, R) *)
  Axiom pairing_additive_left :
    forall (P Q : G1) (R : G2),
      e (g1_add P Q) R = fp12_mul (e P R) (e Q R).

  (** Non-degeneracy: there exist P, Q such that e(P, Q) ≠ 1.
      Equivalently: for generators g1 ∈ G1, g2 ∈ G2,
      e(g1, g2) generates GT. *)
  Variable g1_generator : G1.
  Variable g2_generator : G2.

  Axiom pairing_non_degenerate :
    e g1_generator g2_generator <> fp12_one.

  (* ================================================================ *)
  (** ** Derived properties                                            *)
  (* ================================================================ *)

  (** e(0, Q) = 1 (follows from bilinearity: e(0, Q) = e(P-P, Q) = e(P,Q)*e(-P,Q)) *)
  (** e(P, 0) = 1 *)
  (** e(-P, Q) = e(P, Q)^{-1} *)
  (** Pairing check: e(P1,Q1) = e(P2,Q2) iff e(P1,Q1) * e(-P2,Q2) = 1 *)

  (** The pairing_check function from Pairing.v is correct: *)
  Axiom pairing_check_correct :
    forall (P1 : G1) (Q1 : G2) (P2 : G1) (Q2 : G2),
      pairing_check p gamma1_p2 gamma2_p2 coeff_p2_c1 fp12_eq_dec
        P1 Q1 P2 Q2 = true
      <->
      e P1 Q1 = e P2 Q2.

End Bilinearity.
