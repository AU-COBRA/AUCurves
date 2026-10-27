(** * Bilinearity laws for the BLS12 optimal Ate pairing.

    This file states bilinearity, non-degeneracy and the correctness of
    [pairing_check] as propositions about the pairing of [Pairing.v].
    They are not assumed: a theorem that needs them takes
    [pairing_laws ...] as a hypothesis (see [BLSSignature.v]).

    They used to be [Axiom]s inside a section parameterised by the prime
    [p], the Frobenius constants, the scalar multiplications and the
    generators.  Closing the section generalised each axiom over all of
    these, which is inconsistent: [pairing_non_degenerate_p1] below shows
    that for [p = 1] every pairing value equals [fp12_one], so
    non-degeneracy fails for every choice of generators.

    The laws hold only for the BLS12-381 prime and Frobenius constants,
    for the actual group operations, and for points of the order-r
    subgroups.  Stating them as hypotheses leaves it to the user to supply
    exactly those instances.

    No formal proof of pairing bilinearity exists in any proof assistant
    as of 2026; it requires divisor theory on elliptic curves.
*)

From Stdlib Require Import ZArith.ZArith Eqdep_dec.
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
  (** ** Group operations                                              *)
  (* ================================================================ *)

  Variable g1_add : G1 -> G1 -> G1.
  Variable g1_scalar_mult : Z -> G1 -> G1.
  Variable g2_scalar_mult : Z -> G2 -> G2.
  Variable g1_generator : G1.
  Variable g2_generator : G2.

  (* ================================================================ *)
  (** ** GT (multiplicative subgroup of Fp12-star)                     *)
  (* ================================================================ *)

  Local Notation fp12_mul := (fp12_mul p).
  Local Notation fp12_one := (fp12_one p).

  Definition fp12_pow (base : Fp12) (exp : Z) : Fp12 :=
    fp12_pow_Z p base exp (Z.to_nat (Z.log2 exp + 1)).

  (* ================================================================ *)
  (** ** The laws                                                      *)
  (* ================================================================ *)

  Record pairing_laws : Prop := {
    (** e(aP, Q) = e(P, Q)^a *)
    pairing_bilinear_left :
      forall (a : Z) (P : G1) (Q : G2),
        e (g1_scalar_mult a P) Q = fp12_pow (e P Q) a;
    (** e(P, bQ) = e(P, Q)^b *)
    pairing_bilinear_right :
      forall (b : Z) (P : G1) (Q : G2),
        e P (g2_scalar_mult b Q) = fp12_pow (e P Q) b;
    (** e(P + Q, R) = e(P, R) * e(Q, R) *)
    pairing_additive_left :
      forall (P Q : G1) (R : G2),
        e (g1_add P Q) R = fp12_mul (e P R) (e Q R);
    (** e(g1, g2) <> 1 *)
    pairing_non_degenerate :
      e g1_generator g2_generator <> fp12_one;
    (** [pairing_check] decides equality of pairings. *)
    pairing_check_correct :
      forall (P1 : G1) (Q1 : G2) (P2 : G1) (Q2 : G2),
        pairing_check p gamma1_p2 gamma2_p2 coeff_p2_c1 fp12_eq_dec
          P1 Q1 P2 Q2 = true
        <->
        e P1 Q1 = e P2 Q2
  }.

End Bilinearity.

(* ================================================================ *)
(** ** Why the laws cannot be axioms over arbitrary parameters        *)
(* ================================================================ *)

(** Every element of [F 1] is zero. *)
Lemma F1_all_eq (x y : F 1) : x = y.
Proof.
  destruct x as [x Hx], y as [y Hy].
  assert (Ex : x = 0%Z) by (rewrite Hx; apply Z.mod_1_r).
  assert (Ey : y = 0%Z) by (rewrite Hy; apply Z.mod_1_r).
  subst x y.
  f_equal; apply UIP_dec, Z.eq_dec.
Qed.

(** For [p = 1] the pairing is constant, so non-degeneracy fails for
    every choice of generators and Frobenius constants. *)
Lemma pairing_non_degenerate_p1
  (gamma1_p2 gamma2_p2 coeff_p2_c1 : F 1 * F 1) (P : G1Affine 1) (Q : G2Affine 1) :
  pairing 1 gamma1_p2 gamma2_p2 coeff_p2_c1 P Q = fp12_one 1.
Proof.
  destruct (pairing 1 gamma1_p2 gamma2_p2 coeff_p2_c1 P Q)
    as [[[[a0 a1] [a2 a3]] [a4 a5]] [[[b0 b1] [b2 b3]] [b4 b5]]].
  unfold fp12_one, fp12_build, fp6_one, fp6_zero, fp6_build, fp2_one, fp2_zero.
  repeat f_equal; apply F1_all_eq.
Qed.
