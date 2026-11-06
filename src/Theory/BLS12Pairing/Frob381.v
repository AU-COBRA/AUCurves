(** * Concrete BLS12-381 Frobenius constants for Pairing.v.

    Explicit Fp2 values for the six Frobenius constants of Pairing.v
    (xi = 1 + u):

      gamma1    = xi^((p-1)/3),   gamma2    = gamma1^2,     c1    = xi^((p-1)/6),
      gamma1_p2 = xi^((p^2-1)/3), gamma2_p2 = gamma1_p2^2,  c1_p2 = xi^((p^2-1)/6),

    each checked by computation (square-and-multiply in Fp2, [vm_compute]),
    and the hypothesis-free instances of the theorems of
    [FinalExpFunctional.v] and [Frobenius.v] for these constants.
*)

From Stdlib Require Import ZArith NArith BinPos Lia.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Theory.BLS12Pairing.Pairing.
Require Import Theory.BLS12Pairing.Fp12Ring.
Require Import Theory.BLS12Pairing.Cyclotomic.
Require Import Theory.BLS12Pairing.Frobenius.
Require Import Theory.BLS12Pairing.Prime381.
Require Import Theory.BLS12Pairing.FinalExpFunctional.
Module P := Theory.BLS12Pairing.Pairing.

Local Notation p := p381.
Local Notation F := (F p381).
Local Notation Fp2 := (F * F)%type.
Local Open Scope Z_scope.

Add Ring fp12_ring381 : (@fp12_ring_theory p381).

(** Square-and-multiply in Fp2. *)
Fixpoint fp2_pow_pos (a : Fp2) (n : positive) : Fp2 :=
  match n with
  | xH => a
  | xO n' => let r := fp2_pow_pos a n' in P.fp2_mul p r r
  | xI n' => let r := fp2_pow_pos a n' in P.fp2_mul p a (P.fp2_mul p r r)
  end.

Lemma pw_double : forall (f : (Fp2 * Fp2 * Fp2 * (Fp2 * Fp2 * Fp2))%type) n,
  pw f (2 * n) = P.fp12_mul p (pw f n) (pw f n).
Proof.
  intros f n. rewrite N.mul_comm, pw_mul.
  change 2%N with (N.succ (N.succ 0)). rewrite !pw_succ, pw_0.
  ring.
Qed.

Lemma e212_fp2_pow_pos : forall a n, e212 (fp2_pow_pos a n) = pw (e212 a) (Npos n).
Proof.
  intros a n. induction n as [n IH|n IH|]; cbn [fp2_pow_pos].
  - rewrite !e212_mul, IH.
    change (Npos n~1) with (N.succ (2 * Npos n))%N.
    rewrite pw_succ, pw_double. reflexivity.
  - rewrite !e212_mul, IH.
    change (Npos n~0) with (2 * Npos n)%N.
    rewrite pw_double. reflexivity.
  - rewrite pw_1. reflexivity.
Qed.

(** Fp2 arithmetic on representatives in Z (fast under [vm_compute]). *)
Definition fp2_ofZ (z : Z * Z) : Fp2 := (F.of_Z p (fst z), F.of_Z p (snd z)).

Definition zmul2 (a b : Z * Z) : Z * Z :=
  ((fst a * fst b - snd a * snd b) mod Z.pos p, (fst a * snd b + snd a * fst b) mod Z.pos p).

Fixpoint zpow2 (a : Z * Z) (n : positive) : Z * Z :=
  match n with
  | xH => a
  | xO n' => let r := zpow2 a n' in zmul2 r r
  | xI n' => let r := zpow2 a n' in zmul2 a (zmul2 r r)
  end.

Lemma fp2_ofZ_mul : forall a b, fp2_ofZ (zmul2 a b) = P.fp2_mul p (fp2_ofZ a) (fp2_ofZ b).
Proof.
  intros [a0 a1] [b0 b1]. cbv [fp2_ofZ zmul2 P.fp2_mul fst snd].
  rewrite <- !F.of_Z_mod.
  pose proof (F.ring_morph p) as M.
  rewrite (Ring_theory.morph_sub M), (Ring_theory.morph_add M), !(Ring_theory.morph_mul M).
  reflexivity.
Qed.

Lemma fp2_ofZ_pow : forall a n, fp2_ofZ (zpow2 a n) = fp2_pow_pos (fp2_ofZ a) n.
Proof.
  intros a n. induction n as [n IH|n IH|]; cbn [zpow2 fp2_pow_pos];
    rewrite ?fp2_ofZ_mul, ?IH; reflexivity.
Qed.

Lemma xi2_ofZ : xi2 = fp2_ofZ (1, 1)%Z.
Proof. reflexivity. Qed.

(** The constants (representatives in [0, p)). *)
Definition gamma1_381_Z : Z * Z := (0,
  4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436)%Z.
Definition gamma2_381_Z : Z * Z := (
  4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939437,
  0)%Z.
Definition c1_381_Z : Z * Z := (
  3850754370037169011952147076051364057158807420970682438676050522613628423219637725072182697113062777891589506424760,
  151655185184498381465642749684540099398075398968325446656007613510403227271200139370504932015952886146304766135027)%Z.
Definition gamma1_p2_381_Z : Z * Z := (
  793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620350,
  0)%Z.
Definition gamma2_p2_381_Z : Z * Z := (
  4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436,
  0)%Z.
Definition c1_p2_381_Z : Z * Z := (
  793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620351,
  0)%Z.

Definition gamma1_381 : Fp2 := fp2_ofZ gamma1_381_Z.
Definition gamma2_381 : Fp2 := fp2_ofZ gamma2_381_Z.
Definition c1_381 : Fp2 := fp2_ofZ c1_381_Z.
Definition gamma1_p2_381 : Fp2 := fp2_ofZ gamma1_p2_381_Z.
Definition gamma2_p2_381 : Fp2 := fp2_ofZ gamma2_p2_381_Z.
Definition c1_p2_381 : Fp2 := fp2_ofZ c1_p2_381_Z.

(** The exponents as positives (computed once). *)
Definition e1_3 : positive := Eval vm_compute in Z.to_pos ((Z.pos p - 1) / 3).
Definition e1_6 : positive := Eval vm_compute in Z.to_pos ((Z.pos p - 1) / 6).
Definition e2_3 : positive := Eval vm_compute in Z.to_pos ((Z.pos p * Z.pos p - 1) / 3).
Definition e2_6 : positive := Eval vm_compute in Z.to_pos ((Z.pos p * Z.pos p - 1) / 6).

Lemma e1_3_eq : Z.to_N ((Z.pos p - 1) / 3) = Npos e1_3.  Proof. vm_compute. reflexivity. Qed.
Lemma e1_6_eq : Z.to_N ((Z.pos p - 1) / 6) = Npos e1_6.  Proof. vm_compute. reflexivity. Qed.
Lemma e2_3_eq : Z.to_N ((Z.pos p * Z.pos p - 1) / 3) = Npos e2_3.  Proof. vm_compute. reflexivity. Qed.
Lemma e2_6_eq : Z.to_N ((Z.pos p * Z.pos p - 1) / 6) = Npos e2_6.  Proof. vm_compute. reflexivity. Qed.

(** Each constant, computed on representatives. *)
Lemma gamma1_381_pow : zpow2 (1, 1)%Z e1_3 = gamma1_381_Z.
Proof. vm_compute. reflexivity. Qed.
Lemma c1_381_pow : zpow2 (1, 1)%Z e1_6 = c1_381_Z.
Proof. vm_compute. reflexivity. Qed.
Lemma gamma1_p2_381_pow : zpow2 (1, 1)%Z e2_3 = gamma1_p2_381_Z.
Proof. vm_compute. reflexivity. Qed.
Lemma c1_p2_381_pow : zpow2 (1, 1)%Z e2_6 = c1_p2_381_Z.
Proof. vm_compute. reflexivity. Qed.
Lemma gamma2_381_sq : zmul2 gamma1_381_Z gamma1_381_Z = gamma2_381_Z.
Proof. vm_compute. reflexivity. Qed.
Lemma gamma2_p2_381_sq : zmul2 gamma1_p2_381_Z gamma1_p2_381_Z = gamma2_p2_381_Z.
Proof. vm_compute. reflexivity. Qed.

Lemma pw_xi2 : forall e z, zpow2 (1, 1)%Z e = z -> pw (e212 xi2) (Npos e) = e212 (fp2_ofZ z).
Proof. intros e z H. rewrite <- e212_fp2_pow_pos, xi2_ofZ, <- fp2_ofZ_pow, H. reflexivity. Qed.

(** The six hypotheses of [FinalExpFunctional.HardPart]. *)
Lemma H381_gamma2 : gamma2_381 = P.fp2_mul p gamma1_381 gamma1_381.
Proof. cbv [gamma1_381 gamma2_381]. rewrite <- fp2_ofZ_mul, gamma2_381_sq. reflexivity. Qed.
Lemma H381_gamma1 : pw (e212 xi2) (Z.to_N ((Z.pos p - 1) / 3)) = e212 gamma1_381.
Proof. rewrite e1_3_eq. exact (pw_xi2 _ _ gamma1_381_pow). Qed.
Lemma H381_c1 : pw (e212 xi2) (Z.to_N ((Z.pos p - 1) / 6)) = e212 c1_381.
Proof. rewrite e1_6_eq. exact (pw_xi2 _ _ c1_381_pow). Qed.
Lemma H381_gamma2_p2 : gamma2_p2_381 = P.fp2_mul p gamma1_p2_381 gamma1_p2_381.
Proof. cbv [gamma1_p2_381 gamma2_p2_381]. rewrite <- fp2_ofZ_mul, gamma2_p2_381_sq. reflexivity. Qed.
Lemma H381_gamma1_p2 :
  pw (e212 xi2) (Z.to_N ((Z.pos p * Z.pos p - 1) / 3)) = e212 gamma1_p2_381.
Proof. rewrite e2_3_eq. exact (pw_xi2 _ _ gamma1_p2_381_pow). Qed.
Lemma H381_c1_p2 :
  pw (e212 xi2) (Z.to_N ((Z.pos p * Z.pos p - 1) / 6)) = e212 c1_p2_381.
Proof. rewrite e2_6_eq. exact (pw_xi2 _ _ c1_p2_381_pow). Qed.

(** Hypothesis-free instances. *)
Theorem frobenius_381_is_pow : forall f,
  P.fp12_frobenius p gamma1_381 gamma2_381 c1_381 f = pw f (Npos p).
Proof.
  exact (frobenius_is_pow p381_prime p381_mod4 p381_mod3 _ _ _ H381_gamma2 H381_gamma1 H381_c1).
Qed.

Theorem frobenius_p2_381_is_pow : forall f,
  P.fp12_frobenius_p2 p gamma1_p2_381 gamma2_p2_381 c1_p2_381 f = pw f (Npos (p * p)).
Proof.
  exact (frobenius_p2_is_pow p381_prime p381_mod4 p381_mod3 _ _ _
           H381_gamma2_p2 H381_gamma1_p2 H381_c1_p2).
Qed.

Theorem final_exp_hard_dsd_381_correct : forall f, cyclotomic f ->
  P.final_exp_hard_dsd p gamma1_381 gamma2_381 gamma1_p2_381 gamma2_p2_381 c1_381 c1_p2_381 f =
  P.fp12_pow_Z p f P.h3_exp P.h3_width.
Proof.
  exact (final_exp_hard_dsd_correct _ _ _ _ _ _ H381_gamma2 H381_gamma1 H381_c1
           H381_gamma2_p2 H381_gamma1_p2 H381_c1_p2).
Qed.

Theorem final_exponentiation_dsd_381_correct : forall f,
  P.fp12_mul p f (P.fp12_inv p f) = P.fp12_one p ->
  P.final_exponentiation_dsd p gamma1_381 gamma2_381 gamma1_p2_381 gamma2_p2_381 c1_381 c1_p2_381 f =
  P.final_exponentiation p gamma1_p2_381 gamma2_p2_381 c1_p2_381 f.
Proof.
  exact (final_exponentiation_dsd_correct _ _ _ _ _ _ H381_gamma2 H381_gamma1 H381_c1
           H381_gamma2_p2 H381_gamma1_p2 H381_c1_p2).
Qed.
