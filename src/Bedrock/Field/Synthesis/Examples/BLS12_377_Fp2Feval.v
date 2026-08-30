(** * Fp2 feval bridge for BLS12-377: bedrock2 algebraic models = Fp6.v Gallina models.

    Each lemma shows that the Fp2 bin_model / un_model from the
    AbstractField FieldParameters instance (which the WP proofs use)
    equals the corresponding operation in Spec.BLS12Pairing.Fp6 (the
    parameterized Gallina spec).

    For add/sub/neg/conjugate the models are definitionally equal.
    For mul/sqr/mul_xi the bedrock2 model uses a generic quadratic
    non-residue beta while Fp6.v also parameterizes by beta/xi.
    The bridge requires beta = -5 and xi = (0, 1) for BLS12-377.

    Differences from BLS12-381 (BLS12_Fp2Feval.v):
    - beta = -5 instead of -1
    - xi = (0, 1) instead of (1, 1)
*)

From Stdlib Require Import ZArith.ZArith.
Require Import Crypto.Spec.ModularArithmetic.
Require Spec.BLS12Pairing.Fp6.
Module Fp6Spec := Spec.BLS12Pairing.Fp6.
Require Import Bedrock.Field.FieldExtensions.Theory.QuadraticExtensions.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.

Local Open Scope Z_scope.

(* ================================================================ *)
(** ** Generic lemmas (hold for all p, all beta)                     *)
(* ================================================================ *)

Section Generic.
  Variable p : positive.

  Local Notation Fp := (F p).
  Local Notation Fp2 := (Fp * Fp)%type.

  (** addp2 = Fp6Spec.fp2_add *)
  Lemma addp2_eq_fp2_add : forall a b : Fp2,
    QuadraticExtensions.addp2 p a b = Fp6Spec.fp2_add p a b.
  Proof. intros [a0 a1] [b0 b1]; reflexivity. Qed.

  (** subp2 = Fp6Spec.fp2_sub *)
  Lemma subp2_eq_fp2_sub : forall a b : Fp2,
    QuadraticExtensions.subp2 p a b = Fp6Spec.fp2_sub p a b.
  Proof. intros [a0 a1] [b0 b1]; reflexivity. Qed.

  (** oppp2 = Fp6Spec.fp2_neg *)
  Lemma oppp2_eq_fp2_neg : forall a : Fp2,
    QuadraticExtensions.oppp2 p a = Fp6Spec.fp2_neg p a.
  Proof. intros [a0 a1]; reflexivity. Qed.

  (** Fp2 conjugate model = Fp6Spec.fp2_conjugate. *)
  Lemma conj_model_eq_fp2_conjugate : forall a : Fp2,
    (fst a, @F.opp p (snd a)) = Fp6Spec.fp2_conjugate p a.
  Proof. intros [a0 a1]; reflexivity. Qed.

End Generic.

(* ================================================================ *)
(** ** Beta-dependent lemmas (need beta = -5, i.e. u^2 = -5)        *)
(* ================================================================ *)

Section BetaMinus5.
  Variable p : positive.

  Local Notation Fp := (F p).
  Local Notation Fp2 := (Fp * Fp)%type.

  Let beta : Fp := F.of_Z p (-5).

  Local Lemma beta_unfold : beta = F.of_Z p (-5).
  Proof. reflexivity. Qed.

  (* Install Fp ring for ring tactic *)
  Local Lemma Fp_ring_theory :
    ring_theory (@F.zero p) (@F.one p)
      (@F.add p) (@F.mul p) (@F.sub p) (@F.opp p) eq.
  Proof.
    exact (Algebra.Ring.ring_theory_for_stdlib_tactic
             (zero := @F.zero p) (one := @F.one p)).
  Qed.
  Add Ring Fp_ring : Fp_ring_theory.

  (** mulp2 with beta = -5 equals Fp6Spec.fp2_mul with same beta.

      mulp2:          (a0*b0 + beta*a1*b1,  a0*b1 + a1*b0)
      Fp6Spec.fp2_mul: (a0*b0 + beta*a1*b1,  a0*b1 + a1*b0)

      These are definitionally equal since both use the same formula. *)
  Lemma mulp2_eq_fp2_mul : forall a b : Fp2,
    QuadraticExtensions.mulp2 p beta a b = Fp6Spec.fp2_mul p beta a b.
  Proof.
    intros [a0 a1] [b0 b1].
    unfold QuadraticExtensions.mulp2, Fp6Spec.fp2_mul; simpl fst; simpl snd.
    reflexivity.
  Qed.

  (** Squaring: mulp2 x x with beta = -5 equals Fp6Spec.fp2_sqr.

      mulp2 x x:       (a0*a0 + beta*a1*a1,  a0*a1 + a1*a0)
      Fp6Spec.fp2_sqr: (a0*a0 + beta*a1*a1,  a0*a1 + a0*a1)

      The second components differ only in commutativity: a1*a0 vs a0*a1. *)
  Lemma sqrp2_eq_fp2_sqr : forall a : Fp2,
    QuadraticExtensions.mulp2 p beta a a = Fp6Spec.fp2_sqr p beta a.
  Proof.
    intros [a0 a1].
    unfold QuadraticExtensions.mulp2, Fp6Spec.fp2_sqr; simpl fst; simpl snd.
    f_equal; ring.
  Qed.

  (** mul_xi: the Fp6.v model with beta = -5, xi = (0,1) computes
      Fp2 multiplication by (0, 1) = u.

      Fp6Spec.fp2_mul_xi (0, 1):  (a0*0 + beta*a1*1, a0*1 + a1*0)
                                 = (beta*a1, a0)
                                 = (-5*a1, a0)  *)
  Lemma fp2_mul_xi_eq : forall a : Fp2,
    Fp6Spec.fp2_mul_xi p beta (@F.zero p) (@F.one p) a =
    (F.mul beta (snd a), fst a).
  Proof.
    intros [a0 a1].
    unfold Fp6Spec.fp2_mul_xi; simpl fst; simpl snd.
    f_equal; ring.
  Qed.

  (** Fp2 inverse: the Fp6.v model with beta = -5 computes
      inv(a0 + a1*u) = (a0, -a1) / (a0^2 - beta*a1^2)
                     = (a0, -a1) / (a0^2 + 5*a1^2).  *)
  Lemma fp2_inv_unfold : forall a : Fp2,
    Fp6Spec.fp2_inv p beta a =
    let a0 := fst a in let a1 := snd a in
    let norm := @F.sub p (F.mul a0 a0) (F.mul (F.mul beta a1) a1) in
    let inv_norm := @F.inv p norm in
    (F.mul a0 inv_norm, F.mul (@F.opp p a1) inv_norm).
  Proof. intros [a0 a1]; reflexivity. Qed.

End BetaMinus5.

(* ================================================================ *)
(** ** Combined rewriting database                                   *)
(* ================================================================ *)

(** Collect all bridge lemmas into a hint database for easy rewriting. *)
#[export] Hint Rewrite
  addp2_eq_fp2_add subp2_eq_fp2_sub oppp2_eq_fp2_neg
  conj_model_eq_fp2_conjugate
  mulp2_eq_fp2_mul sqrp2_eq_fp2_sqr
  fp2_mul_xi_eq fp2_inv_unfold
  : fp2_feval_bridge_377.
