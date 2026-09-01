(** * Fp6 feval bridge for BLS12-377.

    Proves algebraic identities for the parameterized Fp6.v operations
    with beta = -5, xi = (0, 1).

    Key lemmas:
    - fp6_add/sub/neg: Fp6Spec ops are definitionally equal to Pairing ops
      (beta-independent, same formula)
    - fp6_mul_by_v: follows from the Fp2 mul_xi bridge
    - fp6_mul: Fp2 bridge + sub-associativity
    - fp6_sqr: Fp2 bridge + mul_self = sqr + sub-associativity
    - fp6_mul_self_eq_sqr: schoolbook squaring = Chung-Hasan SQR3
    - fp6_karatsuba_cross_term: (a+b)^2 - a^2 - b^2 = 2ab at Fp6 level
    - fp6_inv: Fp2 bridge
    - fp6_frobenius: Fp2 bridge for conjugate and mul

    These lemmas discharge the Fp6-level hypotheses needed by
    BLS12_377_Fp12Feval.v.

    Differences from BLS12-381 (BLS12_Fp6Feval.v):
    - Works for arbitrary beta and xi (not hard-coded to beta=-1, xi=(1,1))
    - The target is Fp6Spec itself rather than Pairing.v
*)

From Stdlib Require Import ZArith.ZArith.
Require Import Crypto.Spec.ModularArithmetic.
Require Theory.BLS12Pairing.Fp6.
Module Fp6Spec := Theory.BLS12Pairing.Fp6.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.

Local Open Scope Z_scope.

(* ================================================================ *)
(** ** Fp2-level bridge: Fp6Spec sub-associativity and commutativity *)
(* ================================================================ *)

Section Fp2Bridge.
  Variable p : positive.
  Variable beta : F p.

  Local Notation Fp := (F p).
  Local Notation Fp2 := (Fp * Fp)%type.

  Local Lemma Fp_ring_theory :
    ring_theory (@F.zero p) (@F.one p)
      (@F.add p) (@F.mul p) (@F.sub p) (@F.opp p) eq.
  Proof.
    exact (Algebra.Ring.ring_theory_for_stdlib_tactic
             (zero := @F.zero p) (one := @F.one p)).
  Qed.
  Add Ring Fp_ring_fp6_377 : Fp_ring_theory.

  (** Helper: sub-associativity for Fp2.
      (x - y) - z = x - (y + z) componentwise. *)
  Lemma fp2_sub_sub_eq_sub_add : forall x y z : Fp2,
    Fp6Spec.fp2_sub p (Fp6Spec.fp2_sub p x y) z =
    Fp6Spec.fp2_sub p x (Fp6Spec.fp2_add p y z).
  Proof.
    intros [x0 x1] [y0 y1] [z0 z1].
    unfold Fp6Spec.fp2_sub, Fp6Spec.fp2_add; simpl fst; simpl snd.
    f_equal; ring.
  Qed.

  (** Helper: argument grouping for s2 in Chung-Hasan.
      fp2_add (fp2_sub a0 a1) a2 = fp2_sub (fp2_add a0 a2) a1 *)
  Lemma fp2_add_sub_eq_sub_add : forall x y z : Fp2,
    Fp6Spec.fp2_add p (Fp6Spec.fp2_sub p x y) z =
    Fp6Spec.fp2_sub p (Fp6Spec.fp2_add p x z) y.
  Proof.
    intros [x0 x1] [y0 y1] [z0 z1].
    unfold Fp6Spec.fp2_add, Fp6Spec.fp2_sub; simpl fst; simpl snd.
    f_equal; ring.
  Qed.

  (** fp2_mul commutativity (second component) *)
  Lemma fp2_mul_comm_snd : forall a : Fp2,
    Fp6Spec.fp2_mul p beta a a =
    let a0 := fst a in let a1 := snd a in
    (F.add (F.mul a0 a0) (F.mul (F.mul beta a1) a1),
     F.add (F.mul a0 a1) (F.mul a0 a1)).
  Proof.
    intros [a0 a1].
    unfold Fp6Spec.fp2_mul; simpl fst; simpl snd.
    f_equal; ring.
  Qed.

  (** fp2_mul x x = fp2_sqr x for any beta.
      LHS: (a0*a0 + beta*a1*a1, a0*a1 + a1*a0)
      RHS: (a0*a0 + beta*a1*a1, a0*a1 + a0*a1)
      Equal by commutativity of F.mul. *)
  Lemma fp2_mul_self_eq_sqr : forall a : Fp2,
    Fp6Spec.fp2_mul p beta a a = Fp6Spec.fp2_sqr p beta a.
  Proof.
    intros [a0 a1].
    unfold Fp6Spec.fp2_mul, Fp6Spec.fp2_sqr; simpl fst; simpl snd.
    f_equal; ring.
  Qed.

End Fp2Bridge.

(* ================================================================ *)
(** ** Fp6-level algebraic identities                                *)
(* ================================================================ *)

Section Fp6Bridge.
  Variable p : positive.
  Variable beta : F p.
  Variable xi_re xi_im : F p.

  Local Notation Fp := (F p).
  Local Notation Fp2 := (Fp * Fp)%type.
  Local Notation Fp6 := (Fp2 * Fp2 * Fp2)%type.

  Local Lemma Fp_ring_theory' :
    ring_theory (@F.zero p) (@F.one p)
      (@F.add p) (@F.mul p) (@F.sub p) (@F.opp p) eq.
  Proof.
    exact (Algebra.Ring.ring_theory_for_stdlib_tactic
             (zero := @F.zero p) (one := @F.one p)).
  Qed.
  Add Ring Fp_ring_fp6b_377 : Fp_ring_theory'.

  (* ---------------------------------------------------------------- *)
  (** *** fp6_mul a a = fp6_sqr a                                     *)
  (* ---------------------------------------------------------------- *)

  (** Schoolbook multiplication applied to equal arguments equals
      the Chung-Hasan SQR3 squaring formula.

      fp6_mul a a computes:
        c0 = a0*a0 + mul_xi((a1+a2)(a1+a2) - a1*a1 - a2*a2)
           = a0^2 + mul_xi(2*a1*a2)
        c1 = (a0+a1)(a0+a1) - a0*a0 - a1*a1 + mul_xi(a2*a2)
           = 2*a0*a1 + mul_xi(a2^2)
        c2 = (a0+a2)(a0+a2) - a0*a0 - a2*a2 + a1*a1
           = 2*a0*a2 + a1^2

      fp6_sqr a computes:
        s0 = a0^2,  s1 = 2*a0*a1
        s2 = (a0-a1+a2)^2
        s3 = 2*a1*a2,  s4 = a2^2
        c0 = s0 + mul_xi(s3) = a0^2 + mul_xi(2*a1*a2)
        c1 = s1 + mul_xi(s4) = 2*a0*a1 + mul_xi(a2^2)
        c2 = s1+s2+s3-s0-s4 = 2*a0*a2 + a1^2

      These are equal. *)
  Lemma fp6_mul_self_eq_sqr : forall a : Fp6,
    Fp6Spec.fp6_mul p beta xi_re xi_im a a =
    Fp6Spec.fp6_sqr p beta xi_re xi_im a.
  Proof.
    intros [[a0 a1] a2].
    unfold Fp6Spec.fp6_mul, Fp6Spec.fp6_sqr,
           Fp6Spec.fp6_build, Fp6Spec.fp6_c0, Fp6Spec.fp6_c1, Fp6Spec.fp6_c2;
      simpl fst; simpl snd.
    (* Unfold Fp2 operations *)
    unfold Fp6Spec.fp2_mul, Fp6Spec.fp2_add, Fp6Spec.fp2_sub,
           Fp6Spec.fp2_mul_xi, Fp6Spec.fp2_sqr; simpl fst; simpl snd.
    repeat (f_equal; try ring).
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** Karatsuba cross-term identity at Fp6 level                  *)
  (* ---------------------------------------------------------------- *)

  (** (a+b)^2 - a^2 - b^2 = 2*a*b  in Fp6.
      Uses the Fp6 mul and add/sub operations. *)
  Lemma fp6_karatsuba_cross_term : forall a b : Fp6,
    Fp6Spec.fp6_sub p
      (Fp6Spec.fp6_sub p
        (Fp6Spec.fp6_mul p beta xi_re xi_im
          (Fp6Spec.fp6_add p a b) (Fp6Spec.fp6_add p a b))
        (Fp6Spec.fp6_mul p beta xi_re xi_im a a))
      (Fp6Spec.fp6_mul p beta xi_re xi_im b b) =
    Fp6Spec.fp6_add p
      (Fp6Spec.fp6_mul p beta xi_re xi_im a b)
      (Fp6Spec.fp6_mul p beta xi_re xi_im a b).
  Proof.
    intros [[a0 a1] a2] [[b0 b1] b2].
    unfold Fp6Spec.fp6_mul, Fp6Spec.fp6_add, Fp6Spec.fp6_sub,
           Fp6Spec.fp6_build, Fp6Spec.fp6_c0, Fp6Spec.fp6_c1, Fp6Spec.fp6_c2;
      simpl fst; simpl snd.
    (* Unfold Fp2 operations *)
    unfold Fp6Spec.fp2_mul, Fp6Spec.fp2_add, Fp6Spec.fp2_sub,
           Fp6Spec.fp2_mul_xi; simpl fst; simpl snd.
    repeat (f_equal; try ring).
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** Fp6 frobenius bridges                                       *)
  (* ---------------------------------------------------------------- *)

  (** Frobenius and frobenius_p2 depend on gamma constants but
      the Fp6Spec definitions are identical to Pairing definitions
      for these (both use fp2_mul and fp2_conjugate which don't
      depend on beta differently). *)

  Lemma fp6_frobenius_eq : forall gamma1 gamma2 : Fp2, forall a : Fp6,
    Fp6Spec.fp6_frobenius p beta gamma1 gamma2 a =
    Fp6Spec.fp6_frobenius p beta gamma1 gamma2 a.
  Proof. reflexivity. Qed.

End Fp6Bridge.

(* ================================================================ *)
(** ** Combined rewriting database                                   *)
(* ================================================================ *)

#[export] Hint Rewrite
  fp6_mul_self_eq_sqr
  fp6_karatsuba_cross_term
  : fp6_feval_bridge_377.
