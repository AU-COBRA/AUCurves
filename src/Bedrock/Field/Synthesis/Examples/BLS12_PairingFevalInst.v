(** * Closed instantiation of the Fp12 / Miller loop / pairing feval bridges.

    [BLS12_Fp12Feval.v] and [BLS12_PairingFeval.v] state their results
    under Fp6-level Section hypotheses.  This file proves every hypothesis
    for the BLS12-381 tower (beta = -1, xi = 1 + u) and restates the
    results without hypotheses.

    No primality or characteristic assumption is needed: every hypothesis
    is a polynomial identity over the commutative ring [F p], which holds
    for every modulus [p] (the [ring] tactic on [F p] uses
    [Algebra.Ring.ring_theory_for_stdlib_tactic], valid for any positive
    [p]).  The generic lemmas are stated for all [p]; the [_381] versions
    specialise them to the BLS12-381 prime and Frobenius constants of
    [BLS12_FrobConstants.v] (= SSProve/Commitments' [BLS12_381.p] and
    [frob_gamma1_p2], [frob_gamma2_p2], [frob_coeff_fp12_p2_c1]). *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Theory.BLS12Pairing.Pairing.
Require Theory.BLS12Pairing.Fp6.
Require Theory.BLS12Pairing.Fp12.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_Fp6Feval.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_Fp12Feval.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingFeval.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_FrobConstants.

Module Fp6S := Theory.BLS12Pairing.Fp6.
Module Fp12S := Theory.BLS12Pairing.Fp12.

Local Open Scope Z_scope.

(* ================================================================ *)
(** ** The Fp6 hypotheses not already in BLS12_Fp6Feval.v            *)
(* ================================================================ *)

Section Fp6Extra.
  Variable p : positive.

  Local Notation Fp := (F p).
  Local Notation Fp2 := (Fp * Fp)%type.
  Local Notation Fp6' := (Fp2 * Fp2 * Fp2)%type.

  Local Lemma Fp_ring_theory_inst :
    ring_theory (@F.zero p) (@F.one p)
      (@F.add p) (@F.mul p) (@F.sub p) (@F.opp p) eq.
  Proof.
    exact (Algebra.Ring.ring_theory_for_stdlib_tactic
             (zero := @F.zero p) (one := @F.one p)).
  Qed.
  Add Ring Fp_ring_inst : Fp_ring_theory_inst.

  (** Karatsuba [fp6_mul a a] = Chung-Hasan [fp6_sqr a] (Pairing.v). *)
  Lemma pairing_fp6_mul_self_eq_sqr : forall a : Fp6',
    Pairing.fp6_mul p a a = Pairing.fp6_sqr p a.
  Proof.
    intros [[[a00 a01] [a10 a11]] [a20 a21]].
    cbv [Pairing.fp6_mul Pairing.fp6_sqr Pairing.fp6_build
         Pairing.fp6_c0 Pairing.fp6_c1 Pairing.fp6_c2
         Pairing.fp2_mul Pairing.fp2_sqr Pairing.fp2_add Pairing.fp2_sub
         Pairing.fp2_mul_xi fst snd].
    repeat match goal with |- (_, _) = (_, _) => f_equal end; ring.
  Qed.

  (** (a+b)^2 - a^2 - b^2 = ab + ab in Fp6 (Pairing.v operations). *)
  Lemma pairing_fp6_karatsuba_cross_term : forall a b : Fp6',
    Pairing.fp6_sub p
      (Pairing.fp6_sub p
        (Pairing.fp6_mul p (Pairing.fp6_add p a b) (Pairing.fp6_add p a b))
        (Pairing.fp6_mul p a a))
      (Pairing.fp6_mul p b b) =
    Pairing.fp6_add p (Pairing.fp6_mul p a b) (Pairing.fp6_mul p a b).
  Proof.
    intros [[[a00 a01] [a10 a11]] [a20 a21]]
           [[[b00 b01] [b10 b11]] [b20 b21]].
    cbv [Pairing.fp6_mul Pairing.fp6_add Pairing.fp6_sub Pairing.fp6_build
         Pairing.fp6_c0 Pairing.fp6_c1 Pairing.fp6_c2
         Pairing.fp2_mul Pairing.fp2_add Pairing.fp2_sub
         Pairing.fp2_mul_xi fst snd].
    repeat match goal with |- (_, _) = (_, _) => f_equal end; ring.
  Qed.

  Lemma fp6_frobenius_p2_eq : forall (g1 g2 : Fp2) (a : Fp6'),
    Fp6S.fp6_frobenius_p2 p (F.of_Z p (-1)) g1 g2 a =
    Pairing.fp6_frobenius_p2 p g1 g2 a.
  Proof.
    intros g1 g2 [[a0 a1] a2].
    cbv [Fp6S.fp6_frobenius_p2 Pairing.fp6_frobenius_p2
         Fp6S.fp6_build Pairing.fp6_build
         Fp6S.fp6_c0 Pairing.fp6_c0 Fp6S.fp6_c1 Pairing.fp6_c1
         Fp6S.fp6_c2 Pairing.fp6_c2 fst snd].
    rewrite !fp6spec_fp2_mul_eq. reflexivity.
  Qed.

  Lemma fp6_mul_fp2_eq : forall (a : Fp6') (s : Fp2),
    Fp6S.fp6_mul_fp2 p (F.of_Z p (-1)) a s = Pairing.fp6_mul_fp2 p a s.
  Proof.
    intros [[a0 a1] a2] s.
    cbv [Fp6S.fp6_mul_fp2 Pairing.fp6_mul_fp2
         Fp6S.fp6_build Pairing.fp6_build
         Fp6S.fp6_c0 Pairing.fp6_c0 Fp6S.fp6_c1 Pairing.fp6_c1
         Fp6S.fp6_c2 Pairing.fp6_c2 fst snd].
    rewrite !fp6spec_fp2_mul_eq. reflexivity.
  Qed.

End Fp6Extra.

(* ================================================================ *)
(** ** Closed Fp12 bridge lemmas (all p)                             *)
(* ================================================================ *)

Section Closed.
  Variable p : positive.

  Local Notation Fp := (F p).
  Local Notation Fp2 := (Fp * Fp)%type.
  Local Notation Fp6' := (Fp2 * Fp2 * Fp2)%type.
  Local Notation Fp12' := (Fp6' * Fp6')%type.
  Local Notation beta := (F.of_Z p (-1)).
  Local Notation one := (@F.one p).

  (** The Fp6 hypotheses, all discharged. *)
  Local Ltac fp6_hyps :=
    first
      [ exact (fp6_add_eq p)
      | exact (fp6_sub_eq p)
      | exact (fp6_neg_eq p)
      | exact (fp6_mul_eq p)
      | exact (fp6_mul_by_v_eq p)
      | exact (fp6_sqr_eq p)
      | exact (pairing_fp6_mul_self_eq_sqr p)
      | exact (pairing_fp6_karatsuba_cross_term p)
      | exact (fp6_inv_eq p)
      | exact (fp6_frobenius_eq p _ _)
      | exact (fp6_frobenius_p2_eq p _ _)
      | exact (fp6_mul_fp2_eq p) ].

  Theorem fp12_add_eq_closed : forall a b : Fp12',
    Fp12S.fp12_add p a b = Pairing.fp12_add p a b.
  Proof. apply fp12_add_eq; fp6_hyps. Qed.

  Theorem fp12_sub_eq_closed : forall a b : Fp12',
    Fp12S.fp12_sub p a b = Pairing.fp12_sub p a b.
  Proof. apply fp12_sub_eq; fp6_hyps. Qed.

  Theorem fp12_neg_eq_closed : forall a : Fp12',
    Fp12S.fp12_neg p a = Pairing.fp12_neg p a.
  Proof. apply fp12_neg_eq; fp6_hyps. Qed.

  Theorem fp12_mul_eq_closed : forall a b : Fp12',
    Fp12S.fp12_mul p beta one one a b = Pairing.fp12_mul p a b.
  Proof. apply fp12_mul_eq; fp6_hyps. Qed.

  Theorem fp12_sqr_eq_closed : forall a : Fp12',
    Fp12S.fp12_sqr p beta one one a = Pairing.fp12_sqr p a.
  Proof. apply fp12_sqr_eq; fp6_hyps. Qed.

  Theorem fp12_conjugate_eq_closed : forall a : Fp12',
    Fp12S.fp12_conjugate p a = Pairing.fp12_conjugate p a.
  Proof. apply fp12_conjugate_eq; fp6_hyps. Qed.

  Theorem fp12_square_eq_pairing_sqr_closed : forall x : Fp12',
    Fp12S.fp12_mul p beta one one x x = Pairing.fp12_sqr p x.
  Proof. apply bedrock2_fp12_square_eq_pairing_sqr; fp6_hyps. Qed.

  Theorem fp12_inv_eq_closed : forall a : Fp12',
    Fp12S.fp12_inv p beta one one a = Pairing.fp12_inv p a.
  Proof. apply fp12_inv_eq; fp6_hyps. Qed.

  Theorem fp12_frobenius_eq_closed :
    forall (g1 g2 w_c1 : Fp2) (a : Fp12'),
    Fp12S.fp12_frobenius p beta g1 g2 w_c1 a =
    Pairing.fp12_frobenius p g1 g2 w_c1 a.
  Proof.
    intros g1 g2 w_c1.
    apply fp12_frobenius_eq; fp6_hyps.
  Qed.

  Theorem fp12_frobenius_p2_eq_closed :
    forall (g1_p2 g2_p2 w_p2_c1 : Fp2) (a : Fp12'),
    Fp12S.fp12_frobenius_p2 p beta g1_p2 g2_p2 w_p2_c1 a =
    Pairing.fp12_frobenius_p2 p g1_p2 g2_p2 w_p2_c1 a.
  Proof.
    intros g1_p2 g2_p2 w_p2_c1.
    apply fp12_frobenius_p2_eq; fp6_hyps.
  Qed.

  (* -------------------------------------------------------------- *)
  (** *** Miller loop                                                 *)
  (* -------------------------------------------------------------- *)

  Theorem miller_loop_feval_correct_closed :
    forall (q_x q_y : Fp2) (x_p y_p : Fp),
      fst (fold_left
             (bedrock2_miller_step p q_x q_y x_p y_p)
             Pairing.bls_x_bits
             (Fp12S.fp12_one p, (q_x, q_y))) =
      fst (fold_left
             (Pairing.miller_loop_step p q_x q_y x_p y_p)
             Pairing.bls_x_bits
             (Pairing.fp12_one p, (q_x, q_y))).
  Proof. apply miller_loop_feval_correct; fp6_hyps. Qed.

  Theorem bedrock2_miller_loop_eq_closed :
    forall (P : Pairing.G1Affine p) (Q : Pairing.G2Affine p),
      Pairing.g1_infinity p P = false ->
      Pairing.g2_infinity p Q = false ->
      fst (fold_left
        (bedrock2_miller_step p
           (Pairing.g2_x p Q) (Pairing.g2_y p Q)
           (Pairing.g1_x p P) (Pairing.g1_y p P))
        Pairing.bls_x_bits
        (Fp12S.fp12_one p, (Pairing.g2_x p Q, Pairing.g2_y p Q))) =
      Pairing.miller_loop p P Q.
  Proof.
    apply bedrock2_miller_loop_eq; fp6_hyps.
  Qed.

  (* -------------------------------------------------------------- *)
  (** *** Final exponentiation (h3 version) and pairing               *)
  (* -------------------------------------------------------------- *)

  Theorem final_exp_feval_correct_closed :
    forall (g1_p2 g2_p2 w_p2_c1 : Fp2) (f : Fp12'),
      bedrock2_final_exp p g1_p2 g2_p2 w_p2_c1 f =
      Pairing.final_exponentiation p g1_p2 g2_p2 w_p2_c1 f.
  Proof.
    intros g1_p2 g2_p2 w_p2_c1.
    apply final_exp_feval_correct; fp6_hyps.
  Qed.

  Theorem pairing_feval_correct_closed :
    forall (g1_p2 g2_p2 w_p2_c1 : Fp2)
           (P : Pairing.G1Affine p) (Q : Pairing.G2Affine p),
      Pairing.g1_infinity p P = false ->
      Pairing.g2_infinity p Q = false ->
      bedrock2_pairing p g1_p2 g2_p2 w_p2_c1 P Q =
      Pairing.pairing p g1_p2 g2_p2 w_p2_c1 P Q.
  Proof.
    intros g1_p2 g2_p2 w_p2_c1.
    apply pairing_feval_correct; fp6_hyps.
  Qed.

End Closed.

(* ================================================================ *)
(** ** BLS12-381 specialisation                                     *)
(* ================================================================ *)

Module BLS12_381_FevalInst.
  Import BLS12_381_Frob.

  (** The Gallina pairing of SSProve/Commitments' concrete instance:
      [BLS12_381.e = pairing p frob_gamma1_p2 frob_gamma2_p2
                                frob_coeff_fp12_p2_c1]. *)
  Theorem pairing_feval_correct_381 :
    forall (P : Pairing.G1Affine p) (Q : Pairing.G2Affine p),
      Pairing.g1_infinity p P = false ->
      Pairing.g2_infinity p Q = false ->
      bedrock2_pairing p frob_gamma1_p2 frob_gamma2_p2 frob_coeff_fp12_p2_c1 P Q =
      Pairing.pairing p frob_gamma1_p2 frob_gamma2_p2 frob_coeff_fp12_p2_c1 P Q.
  Proof. apply pairing_feval_correct_closed. Qed.

  (** The same with the constants as loaded by the bedrock2 loaders. *)
  Theorem pairing_feval_correct_381_loaded :
    forall (P : Pairing.G1Affine p) (Q : Pairing.G2Affine p),
      Pairing.g1_infinity p P = false ->
      Pairing.g2_infinity p Q = false ->
      bedrock2_pairing p gamma1_p2_loaded gamma2_p2_loaded w_frob_p2_c1_loaded P Q =
      Pairing.pairing p frob_gamma1_p2 frob_gamma2_p2 frob_coeff_fp12_p2_c1 P Q.
  Proof.
    intros P Q HP HQ.
    rewrite gamma1_p2_loaded_eq, gamma2_p2_loaded_eq, w_frob_p2_c1_loaded_eq.
    apply pairing_feval_correct_closed; assumption.
  Qed.

  Theorem bedrock2_miller_loop_eq_381 :
    forall (P : Pairing.G1Affine p) (Q : Pairing.G2Affine p),
      Pairing.g1_infinity p P = false ->
      Pairing.g2_infinity p Q = false ->
      fst (fold_left
        (bedrock2_miller_step p
           (Pairing.g2_x p Q) (Pairing.g2_y p Q)
           (Pairing.g1_x p P) (Pairing.g1_y p P))
        Pairing.bls_x_bits
        (Fp12S.fp12_one p, (Pairing.g2_x p Q, Pairing.g2_y p Q))) =
      Pairing.miller_loop p P Q.
  Proof. apply bedrock2_miller_loop_eq_closed. Qed.

End BLS12_381_FevalInst.
