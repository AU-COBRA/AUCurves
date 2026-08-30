(** * Fp2 feval bridge: bedrock2 algebraic models = Pairing.v Gallina models.

    Each lemma shows that the Fp2 bin_model / un_model from the
    AbstractField FieldParameters instance (which the WP proofs use)
    equals the corresponding operation in Spec.BLS12Pairing.Pairing.

    For add/sub/neg/conjugate the models are definitionally equal.
    For mul/sqr/mul_xi the bedrock2 model uses a generic quadratic
    non-residue beta while Pairing.v hardcodes u^2 = -1.  The bridge
    requires beta = -1 and a short ring proof.
*)

From Stdlib Require Import ZArith.ZArith.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Spec.BLS12Pairing.Pairing.
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

  (** addp2 = Pairing.fp2_add *)
  Lemma addp2_eq_fp2_add : forall a b : Fp2,
    QuadraticExtensions.addp2 p a b = Pairing.fp2_add p a b.
  Proof. intros [a0 a1] [b0 b1]; reflexivity. Qed.

  (** subp2 = Pairing.fp2_sub *)
  Lemma subp2_eq_fp2_sub : forall a b : Fp2,
    QuadraticExtensions.subp2 p a b = Pairing.fp2_sub p a b.
  Proof. intros [a0 a1] [b0 b1]; reflexivity. Qed.

  (** oppp2 = Pairing.fp2_neg *)
  Lemma oppp2_eq_fp2_neg : forall a : Fp2,
    QuadraticExtensions.oppp2 p a = Pairing.fp2_neg p a.
  Proof. intros [a0 a1]; reflexivity. Qed.

  (** Fp2 conjugate model = Pairing.fp2_conjugate.
      The bedrock2 un_model for conjugate is (fst x, F.opp (snd x)). *)
  Lemma conj_model_eq_fp2_conjugate : forall a : Fp2,
    (fst a, @F.opp p (snd a)) = Pairing.fp2_conjugate p a.
  Proof. intros [a0 a1]; reflexivity. Qed.

End Generic.

(* ================================================================ *)
(** ** Beta-dependent lemmas (need beta = -1, i.e. u^2 = -1)        *)
(* ================================================================ *)

Section BetaMinus1.
  Variable p : positive.

  Local Notation Fp := (F p).
  Local Notation Fp2 := (Fp * Fp)%type.

  Let beta : Fp := F.of_Z p (-1).

  Local Lemma beta_is_opp_one : beta = @F.opp p (@F.one p).
  Proof.
    unfold beta. change (-1)%Z with (Z.opp 1%Z).
    rewrite F.of_Z_opp. reflexivity.
  Qed.

  (* Install Fp ring for ring tactic *)
  Local Lemma Fp_ring_theory :
    ring_theory (@F.zero p) (@F.one p)
      (@F.add p) (@F.mul p) (@F.sub p) (@F.opp p) eq.
  Proof.
    exact (Algebra.Ring.ring_theory_for_stdlib_tactic
             (zero := @F.zero p) (one := @F.one p)).
  Qed.
  Add Ring Fp_ring : Fp_ring_theory.

  (** mulp2 with beta = -1 equals Pairing.fp2_mul.

      mulp2:       (a0*b0 + beta*a1*b1,  a0*b1 + a1*b0)
      fp2_mul:     (a0*b0 - a1*b1,       a0*b1 + a1*b0)

      With beta = -1:  beta*a1*b1 = -(a1*b1).  *)
  Lemma mulp2_eq_fp2_mul : forall a b : Fp2,
    QuadraticExtensions.mulp2 p beta a b = Pairing.fp2_mul p a b.
  Proof.
    intros [a0 a1] [b0 b1].
    unfold QuadraticExtensions.mulp2, Pairing.fp2_mul; simpl fst; simpl snd.
    rewrite beta_is_opp_one.
    f_equal; ring.
  Qed.

  (** Squaring: mulp2 x x with beta = -1 equals Pairing.fp2_sqr.

      mulp2 x x:  (a0*a0 + beta*a1*a1,  a0*a1 + a1*a0)
      fp2_sqr:    ((a0+a1)*(a0-a1),      a0*a1 + a0*a1)

      These are equal in any commutative ring with beta = -1. *)
  Lemma sqrp2_eq_fp2_sqr : forall a : Fp2,
    QuadraticExtensions.mulp2 p beta a a = Pairing.fp2_sqr p a.
  Proof.
    intros [a0 a1].
    unfold QuadraticExtensions.mulp2, Pairing.fp2_sqr; simpl fst; simpl snd.
    rewrite beta_is_opp_one.
    f_equal; ring.
  Qed.

  (** mul_xi: the Fp6.v model with beta = -1, xi = (1,1) equals
      Pairing.fp2_mul_xi.

      Fp6Spec.fp2_mul_xi:  (a0*1 + beta*a1*1, a0*1 + a1*1)
                              = (a0 - a1, a0 + a1)
      Pairing.fp2_mul_xi:       (a0 - a1, a0 + a1)              *)
  Lemma fp2_mul_xi_eq : forall a : Fp2,
    Fp6Spec.fp2_mul_xi p beta (@F.one p) (@F.one p) a =
    Pairing.fp2_mul_xi p a.
  Proof.
    intros [a0 a1].
    unfold Fp6Spec.fp2_mul_xi, Pairing.fp2_mul_xi; simpl fst; simpl snd.
    rewrite beta_is_opp_one.
    f_equal; ring.
  Qed.

  (** Fp2 inverse: the Fp6.v model with beta = -1 equals Pairing.fp2_inv.

      Fp6.fp2_inv:     norm = a0^2 - beta*a1^2, inv = (a0/norm, -a1/norm)
      Pairing.fp2_inv: norm = a0^2 + a1^2,      inv = (a0/norm, -a1/norm)

      With beta = -1:  a0^2 - (-1)*a1^2 = a0^2 + a1^2.  *)
  Lemma fp2_inv_eq : forall a : Fp2,
    Fp6Spec.fp2_inv p beta a = Pairing.fp2_inv p a.
  Proof.
    intros [a0 a1].
    unfold Fp6Spec.fp2_inv, Pairing.fp2_inv; simpl fst; simpl snd.
    rewrite beta_is_opp_one.
    replace (a0 * a0 - F.opp 1 * a1 * a1)%F
      with (a0 * a0 + a1 * a1)%F by ring.
    reflexivity.
  Qed.

End BetaMinus1.

(* ================================================================ *)
(** ** Combined rewriting database                                   *)
(* ================================================================ *)

(** Collect all bridge lemmas into a hint database for easy rewriting. *)
#[export] Hint Rewrite
  addp2_eq_fp2_add subp2_eq_fp2_sub oppp2_eq_fp2_neg
  conj_model_eq_fp2_conjugate
  mulp2_eq_fp2_mul sqrp2_eq_fp2_sqr
  fp2_mul_xi_eq fp2_inv_eq
  : fp2_feval_bridge.
