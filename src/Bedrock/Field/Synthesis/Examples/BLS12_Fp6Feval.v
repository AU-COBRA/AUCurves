(** * Fp6 feval bridge: Fp6.v (bedrock2 model) = Pairing.v (Gallina target).

    Extends the Fp2 bridge (BLS12_Fp2Feval.v) to the Fp6 level.

    For each Fp6 operation, we show that the parameterised Fp6.v model
    (used by CubicFieldExtensionsSpecs.v / the bedrock2 WP proofs)
    equals the Pairing.v model (the verification target) under the
    BLS12-381 instantiation: beta = -1, xi = (1, 1).

    - add / sub / neg : definitionally equal (reflexivity)
    - mul_by_v        : follows from the Fp2 mul_xi bridge
    - mul             : Fp2 bridge + ring reasoning for sub-associativity
    - sqr             : Fp2 bridge + ring reasoning
    - inv             : Fp2 bridge
    - frobenius       : Fp2 bridge for conjugate and mul
*)

From Stdlib Require Import ZArith.ZArith.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Theory.BLS12Pairing.Pairing.
Require Theory.BLS12Pairing.Fp6.
Module Fp6Spec := Theory.BLS12Pairing.Fp6.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.

Local Open Scope Z_scope.

(* ================================================================ *)
(** ** Fp2-level bridge: Fp6.fp2_XXX vs Pairing.fp2_XXX              *)
(* ================================================================ *)

Section Fp2Bridge.
  Variable p : positive.

  Local Notation Fp := (F p).
  Local Notation Fp2 := (Fp * Fp)%type.

  (** fp2_add, fp2_sub, fp2_neg are definitionally equal. *)
  Lemma fp6spec_fp2_add_eq : forall a b : Fp2,
    Fp6Spec.fp2_add p a b = Pairing.fp2_add p a b.
  Proof. reflexivity. Qed.

  Lemma fp6spec_fp2_sub_eq : forall a b : Fp2,
    Fp6Spec.fp2_sub p a b = Pairing.fp2_sub p a b.
  Proof. reflexivity. Qed.

  Lemma fp6spec_fp2_neg_eq : forall a : Fp2,
    Fp6Spec.fp2_neg p a = Pairing.fp2_neg p a.
  Proof. reflexivity. Qed.

  Lemma fp6spec_fp2_conjugate_eq : forall a : Fp2,
    Fp6Spec.fp2_conjugate p a = Pairing.fp2_conjugate p a.
  Proof. reflexivity. Qed.

  (** For mul, sqr, mul_xi, inv we need beta = -1, xi = (1,1). *)
  Let beta : Fp := F.of_Z p (-1).

  Local Lemma beta_is_opp_one : beta = @F.opp p (@F.one p).
  Proof.
    unfold beta. change (-1)%Z with (Z.opp 1%Z).
    rewrite F.of_Z_opp. reflexivity.
  Qed.

  Local Lemma Fp_ring_theory :
    ring_theory (@F.zero p) (@F.one p)
      (@F.add p) (@F.mul p) (@F.sub p) (@F.opp p) eq.
  Proof.
    exact (Algebra.Ring.ring_theory_for_stdlib_tactic
             (zero := @F.zero p) (one := @F.one p)).
  Qed.
  Add Ring Fp_ring_fp6 : Fp_ring_theory.

  Lemma fp6spec_fp2_mul_eq : forall a b : Fp2,
    Fp6Spec.fp2_mul p beta a b = Pairing.fp2_mul p a b.
  Proof.
    intros [a0 a1] [b0 b1].
    unfold Fp6Spec.fp2_mul, Pairing.fp2_mul; simpl fst; simpl snd.
    rewrite beta_is_opp_one. f_equal; ring.
  Qed.

  Lemma fp6spec_fp2_sqr_eq : forall a : Fp2,
    Fp6Spec.fp2_sqr p beta a = Pairing.fp2_sqr p a.
  Proof.
    intros [a0 a1].
    unfold Fp6Spec.fp2_sqr, Pairing.fp2_sqr; simpl fst; simpl snd.
    rewrite beta_is_opp_one. f_equal; ring.
  Qed.

  Lemma fp6spec_fp2_mul_xi_eq : forall a : Fp2,
    Fp6Spec.fp2_mul_xi p beta (@F.one p) (@F.one p) a =
    Pairing.fp2_mul_xi p a.
  Proof.
    intros [a0 a1].
    unfold Fp6Spec.fp2_mul_xi, Pairing.fp2_mul_xi; simpl fst; simpl snd.
    rewrite beta_is_opp_one. f_equal; ring.
  Qed.

  Lemma fp6spec_fp2_inv_eq : forall a : Fp2,
    Fp6Spec.fp2_inv p beta a = Pairing.fp2_inv p a.
  Proof.
    intros [a0 a1].
    unfold Fp6Spec.fp2_inv, Pairing.fp2_inv; simpl fst; simpl snd.
    rewrite beta_is_opp_one.
    replace (a0 * a0 - F.opp 1 * a1 * a1)%F
      with (a0 * a0 + a1 * a1)%F by ring.
    reflexivity.
  Qed.

  (** Helper: sub-associativity for Fp2.
      (x - y) - z = x - (y + z) componentwise. *)
  Lemma fp2_sub_sub_eq_sub_add : forall x y z : Fp2,
    Fp6Spec.fp2_sub p (Fp6Spec.fp2_sub p x y) z =
    Pairing.fp2_sub p x (Pairing.fp2_add p y z).
  Proof.
    intros [x0 x1] [y0 y1] [z0 z1].
    unfold Fp6Spec.fp2_sub, Pairing.fp2_sub, Pairing.fp2_add;
      simpl fst; simpl snd.
    f_equal; ring.
  Qed.

End Fp2Bridge.

(* ================================================================ *)
(** ** Fp6-level bridge lemmas                                       *)
(* ================================================================ *)

Section Fp6Bridge.
  Variable p : positive.

  Local Notation Fp := (F p).
  Local Notation Fp2 := (Fp * Fp)%type.
  Local Notation Fp6 := (Fp2 * Fp2 * Fp2)%type.

  Let beta : Fp := F.of_Z p (-1).

  Local Lemma beta_is_opp_one' : beta = @F.opp p (@F.one p).
  Proof.
    unfold beta. change (-1)%Z with (Z.opp 1%Z).
    rewrite F.of_Z_opp. reflexivity.
  Qed.

  Local Lemma Fp_ring_theory' :
    ring_theory (@F.zero p) (@F.one p)
      (@F.add p) (@F.mul p) (@F.sub p) (@F.opp p) eq.
  Proof.
    exact (Algebra.Ring.ring_theory_for_stdlib_tactic
             (zero := @F.zero p) (one := @F.one p)).
  Qed.
  Add Ring Fp_ring_fp6b : Fp_ring_theory'.

  (* ---------------------------------------------------------------- *)
  (** *** 1. fp6_add                                                   *)
  (* ---------------------------------------------------------------- *)

  Lemma fp6_add_eq : forall a b : Fp6,
    Fp6Spec.fp6_add p a b = Pairing.fp6_add p a b.
  Proof. reflexivity. Qed.

  (* ---------------------------------------------------------------- *)
  (** *** 2. fp6_sub                                                   *)
  (* ---------------------------------------------------------------- *)

  Lemma fp6_sub_eq : forall a b : Fp6,
    Fp6Spec.fp6_sub p a b = Pairing.fp6_sub p a b.
  Proof. reflexivity. Qed.

  (* ---------------------------------------------------------------- *)
  (** *** 3. fp6_neg                                                   *)
  (* ---------------------------------------------------------------- *)

  Lemma fp6_neg_eq : forall a : Fp6,
    Fp6Spec.fp6_neg p a = Pairing.fp6_neg p a.
  Proof. reflexivity. Qed.

  (* ---------------------------------------------------------------- *)
  (** *** 4. fp6_mul_by_v                                              *)
  (* ---------------------------------------------------------------- *)

  Lemma fp6_mul_by_v_eq : forall a : Fp6,
    Fp6Spec.fp6_mul_by_v p beta (@F.one p) (@F.one p) a =
    Pairing.fp6_mul_by_v p a.
  Proof.
    intros [[a0 a1] a2].
    unfold Fp6Spec.fp6_mul_by_v, Pairing.fp6_mul_by_v,
           Fp6Spec.fp6_build, Pairing.fp6_build,
           Fp6Spec.fp6_c0, Pairing.fp6_c0,
           Fp6Spec.fp6_c1, Pairing.fp6_c1,
           Fp6Spec.fp6_c2, Pairing.fp6_c2; simpl fst; simpl snd.
    rewrite fp6spec_fp2_mul_xi_eq. reflexivity.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** 5. fp6_mul                                                   *)
  (* ---------------------------------------------------------------- *)

  Lemma fp6_mul_eq : forall a b : Fp6,
    Fp6Spec.fp6_mul p beta (@F.one p) (@F.one p) a b =
    Pairing.fp6_mul p a b.
  Proof.
    intros [[a0 a1] a2] [[b0 b1] b2].
    unfold Fp6Spec.fp6_mul, Pairing.fp6_mul,
           Fp6Spec.fp6_build, Pairing.fp6_build,
           Fp6Spec.fp6_c0, Pairing.fp6_c0,
           Fp6Spec.fp6_c1, Pairing.fp6_c1,
           Fp6Spec.fp6_c2, Pairing.fp6_c2; simpl fst; simpl snd.
    (* Rewrite Fp6Spec Fp2 operations to Pairing Fp2 operations *)
    repeat rewrite fp6spec_fp2_mul_eq.
    repeat rewrite fp6spec_fp2_add_eq.
    repeat rewrite fp6spec_fp2_mul_xi_eq.
    (* Now the only difference is sub-associativity:
       Fp6Spec uses (x - y) - z, Pairing uses x - (y + z) *)
    repeat rewrite fp2_sub_sub_eq_sub_add.
    reflexivity.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** 6. fp6_sqr                                                   *)
  (* ---------------------------------------------------------------- *)

  (** Helper: Fp6Spec.fp2_mul a a with beta=-1 = Pairing.fp2_sqr a.
      The Fp6Spec.fp6_sqr uses fp2_mul for squaring, Pairing uses fp2_sqr. *)
  Local Lemma fp6spec_fp2_mul_self_eq_sqr : forall a : Fp2,
    Fp6Spec.fp2_mul p beta a a = Pairing.fp2_sqr p a.
  Proof.
    intros [a0 a1].
    unfold Fp6Spec.fp2_mul, Pairing.fp2_sqr; simpl fst; simpl snd.
    rewrite beta_is_opp_one'. f_equal; ring.
  Qed.

  (** Helper: argument to s2 differs in grouping.
      Fp6Spec: fp2_add (fp2_sub a0 a1) a2
      Pairing: fp2_sub (fp2_add a0 a2) a1 *)
  Local Lemma fp2_add_sub_eq_sub_add : forall x y z : Fp2,
    Fp6Spec.fp2_add p (Fp6Spec.fp2_sub p x y) z =
    Pairing.fp2_sub p (Pairing.fp2_add p x z) y.
  Proof.
    intros [x0 x1] [y0 y1] [z0 z1].
    unfold Fp6Spec.fp2_add, Fp6Spec.fp2_sub,
           Pairing.fp2_sub, Pairing.fp2_add; simpl fst; simpl snd.
    f_equal; ring.
  Qed.

  Lemma fp6_sqr_eq : forall a : Fp6,
    Fp6Spec.fp6_sqr p beta (@F.one p) (@F.one p) a =
    Pairing.fp6_sqr p a.
  Proof.
    intros [[a0 a1] a2].
    unfold Fp6Spec.fp6_sqr, Pairing.fp6_sqr,
           Fp6Spec.fp6_build, Pairing.fp6_build,
           Fp6Spec.fp6_c0, Pairing.fp6_c0,
           Fp6Spec.fp6_c1, Pairing.fp6_c1,
           Fp6Spec.fp6_c2, Pairing.fp6_c2; simpl fst; simpl snd.
    (* Rewrite fp2_mul x x -> fp2_sqr *)
    repeat rewrite fp6spec_fp2_mul_self_eq_sqr.
    (* Rewrite remaining Fp2 operations *)
    repeat rewrite fp6spec_fp2_mul_eq.
    repeat rewrite fp6spec_fp2_add_eq.
    repeat rewrite fp6spec_fp2_mul_xi_eq.
    (* s2 argument grouping *)
    rewrite fp2_add_sub_eq_sub_add.
    (* c2 sub-associativity *)
    rewrite fp2_sub_sub_eq_sub_add.
    reflexivity.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** 7. fp6_inv                                                   *)
  (* ---------------------------------------------------------------- *)

  Lemma fp6_inv_eq : forall a : Fp6,
    Fp6Spec.fp6_inv p beta (@F.one p) (@F.one p) a =
    Pairing.fp6_inv p a.
  Proof.
    intros [[a0 a1] a2].
    unfold Fp6Spec.fp6_inv, Pairing.fp6_inv,
           Fp6Spec.fp6_build, Pairing.fp6_build,
           Fp6Spec.fp6_c0, Pairing.fp6_c0,
           Fp6Spec.fp6_c1, Pairing.fp6_c1,
           Fp6Spec.fp6_c2, Pairing.fp6_c2; simpl fst; simpl snd.
    (* Rewrite fp2_mul x x -> fp2_sqr *)
    repeat rewrite fp6spec_fp2_mul_self_eq_sqr.
    (* Rewrite all Fp2 operations *)
    repeat rewrite fp6spec_fp2_mul_eq.
    repeat rewrite fp6spec_fp2_add_eq.
    repeat rewrite fp6spec_fp2_sub_eq.
    repeat rewrite fp6spec_fp2_mul_xi_eq.
    repeat rewrite fp6spec_fp2_inv_eq.
    reflexivity.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** 8. fp6_frobenius                                             *)
  (* ---------------------------------------------------------------- *)

  Lemma fp6_frobenius_eq : forall gamma1 gamma2 : Fp2, forall a : Fp6,
    Fp6Spec.fp6_frobenius p beta gamma1 gamma2 a =
    Pairing.fp6_frobenius p gamma1 gamma2 a.
  Proof.
    intros gamma1 gamma2 [[a0 a1] a2].
    unfold Fp6Spec.fp6_frobenius, Pairing.fp6_frobenius,
           Fp6Spec.fp6_build, Pairing.fp6_build,
           Fp6Spec.fp6_c0, Pairing.fp6_c0,
           Fp6Spec.fp6_c1, Pairing.fp6_c1,
           Fp6Spec.fp6_c2, Pairing.fp6_c2; simpl fst; simpl snd.
    rewrite fp6spec_fp2_conjugate_eq.
    repeat rewrite fp6spec_fp2_mul_eq.
    reflexivity.
  Qed.

End Fp6Bridge.

(* ================================================================ *)
(** ** Combined rewriting database                                   *)
(* ================================================================ *)

#[export] Hint Rewrite
  fp6_add_eq fp6_sub_eq fp6_neg_eq
  fp6_mul_by_v_eq fp6_mul_eq fp6_sqr_eq
  fp6_inv_eq fp6_frobenius_eq
  : fp6_feval_bridge.
