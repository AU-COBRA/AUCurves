(** * The BLS12-381 tower Fp12 = Fp2[v,w] (Pairing.v) is a field: every nonzero f has
      f * fp12_inv f = 1.

    - -1 is a non-residue mod p (Euler's criterion, p = 3 mod 4), so the Fp2 norm
      a0^2 + a1^2 vanishes only at 0: [fp2_inv_ok].
    - xi = 1+u is neither a cube nor a square in Fp2: Fermat in Fp2 (r^(p^2) = r,
      from [Frob381.frobenius_p2_381_is_pow] on the embedded Fp2) and the computed powers
      xi^((p^2-1)/3) = gamma1_p2_381 <> 1 ([Frob381.H381_gamma1_p2]) and
      xi^((p^2-1)/2) <> 1.
    - Fp6 = Fp2[v]/(v^3 - xi): the norm N(a) = a0 A + xi (a2 B + a1 C) of the
      [Pairing.fp6_inv] formula vanishes only at 0 (if a kills a nonzero x, a degree
      argument produces a cube root of xi): [fp6_inv_ok].
    - Fp12 = Fp6[w]/(w^2 - v): v is not a square in Fp6 (N(v) = xi, N(s^2) = N(s)^2),
      so a0^2 - v a1^2 vanishes only at 0: [fp12_inv_ok].
*)

From Stdlib Require Import ZArith NArith BinPos Lia Znumtheory.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Algebra.Field.
Require Theory.BLS12Pairing.Pairing.
Require Import Theory.BLS12Pairing.Fp12Ring.
Require Import Theory.BLS12Pairing.Prime381.
Require Import Theory.BLS12Pairing.Frobenius.
Require Import Theory.BLS12Pairing.Frob381.
Module P := Theory.BLS12Pairing.Pairing.

Local Notation p := p381.
Local Notation F := (F p381).
Local Notation Fp2 := ((F * F)%type).
Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
Local Notation Fp12 := ((Fp6 * Fp6)%type).

Local Instance p381_prime_inst : prime p381 := p381_prime.

Add Field Fp_field381 : (Algebra.Field.field_theory_for_stdlib_tactic (T:=F)).
Add Ring fp2_ring381 : (@fp2_ring_theory p381).
Add Ring fp6_ring381 : (@fp6_ring_theory p381).
Add Ring fp12_ring381' : (@fp12_ring_theory p381).

Ltac split_to_fp2 :=
  repeat match goal with
         | |- @eq (F * F) _ _ => fail 1
         | |- @eq (prod _ _) _ _ => apply injective_projections; cbn [fst snd]
         end.

Local Notation fp2_add := (P.fp2_add p).
Local Notation fp2_sub := (P.fp2_sub p).
Local Notation fp2_mul := (P.fp2_mul p).
Local Notation fp2_zero := (P.fp2_zero p).
Local Notation fp2_one := (P.fp2_one p).
Local Notation fp2_inv := (P.fp2_inv p).
Local Notation fp6_mul := (P.fp6_mul p).
Local Notation fp6_zero := (P.fp6_zero p).
Local Notation fp6_one := (P.fp6_one p).
Local Notation fp12_mul := (P.fp12_mul p).
Local Notation fp12_one := (P.fp12_one p).

(* ================================================================ *)
(** ** Fp                                                            *)
(* ================================================================ *)

Lemma F_one_neq_zero : (F.one : F) <> F.zero.
Proof. intro H. apply (f_equal F.to_Z) in H. vm_compute in H. discriminate. Qed.

Lemma F_mul_nonzero (x y : F) : x <> F.zero -> y <> F.zero -> F.mul x y <> F.zero.
Proof.
  intros Hx Hy Hxy. apply Hy.
  transitivity (F.mul (F.mul (F.inv x) x) y).
  { rewrite F.inv_nonzero by first [exact Hx | exact p381_prime]. ring. }
  transitivity (F.mul (F.inv x) (F.mul x y)); [ring |]. rewrite Hxy. ring.
Qed.

Lemma neg1_nonsquare : ~ exists b : F, F.mul b b = F.opp F.one.
Proof.
  intros Hb.
  assert (Hnz : F.opp (F.one : F) <> F.zero).
  { intro H. apply (f_equal F.to_Z) in H. vm_compute in H. discriminate. }
  assert (H2 : (2 < Z.pos p381)%Z) by (vm_compute; reflexivity).
  apply (proj2 (@F.euler_criterion p381 _ H2 (F.opp F.one) Hnz)) in Hb.
  replace (Z.to_N (Z.pos p381 / 2)) with (2 * Z.to_N (Z.pos p381 / 4) + 1)%N in Hb
    by (vm_compute; reflexivity).
  rewrite F.pow_add_r, <- F.pow_pow_l, F.pow_1_r in Hb.
  replace (F.pow (F.opp F.one) 2) with (F.one : F) in Hb by (rewrite F.pow_2_r; ring).
  rewrite F.pow_1_l in Hb.
  apply (f_equal F.to_Z) in Hb. vm_compute in Hb. discriminate.
Qed.

(* ================================================================ *)
(** ** Fp2                                                           *)
(* ================================================================ *)

Lemma fp2_eq_dec (a b : Fp2) : {a = b} + {a <> b}.
Proof.
  destruct a as [a0 a1], b as [b0 b1].
  destruct (F.eq_dec a0 b0); [| right; congruence].
  destruct (F.eq_dec a1 b1); [| right; congruence].
  left; subst; reflexivity.
Defined.

Lemma fp2_norm_nonzero (a0 a1 : F) : (a0, a1) <> fp2_zero ->
  F.add (F.mul a0 a0) (F.mul a1 a1) <> F.zero.
Proof.
  intros Ha Hn.
  destruct (F.eq_dec a1 F.zero) as [E1 | E1].
  - subst a1. destruct (F.eq_dec a0 F.zero) as [E0 | E0].
    + subst a0. apply Ha. reflexivity.
    + apply (F_mul_nonzero a0 a0 E0 E0). rewrite <- Hn. ring.
  - apply neg1_nonsquare. exists (F.div a0 a1).
    assert (E : F.mul (F.div a0 a1) (F.div a0 a1) =
                F.sub (F.div (F.add (F.mul a0 a0) (F.mul a1 a1)) (F.mul a1 a1)) F.one)
      by (field; exact E1).
    rewrite E, Hn. field. exact E1.
Qed.

Lemma fp2_inv_ok (a : Fp2) : a <> fp2_zero -> fp2_mul a (fp2_inv a) = fp2_one.
Proof.
  destruct a as [a0 a1]. intros Ha.
  pose proof (fp2_norm_nonzero a0 a1 Ha) as Hn.
  cbv [P.fp2_mul P.fp2_inv P.fp2_one fst snd].
  f_equal; field; exact Hn.
Qed.

Lemma fp2_one_neq_zero : fp2_one <> fp2_zero.
Proof. intro H. apply F_one_neq_zero. exact (f_equal fst H). Qed.

Definition fp2_div (a b : Fp2) : Fp2 := fp2_mul a (fp2_inv b).

Lemma fp2_field_theory :
  Field_theory.field_theory fp2_zero fp2_one fp2_add fp2_mul fp2_sub (P.fp2_neg p) fp2_div fp2_inv eq.
Proof.
  constructor.
  - exact (@fp2_ring_theory p381).
  - exact fp2_one_neq_zero.
  - reflexivity.
  - intros a Ha. rewrite <- (fp2_inv_ok a Ha). ring.
Qed.
Add Field fp2_field381 : fp2_field_theory.

Lemma fp2_mul_nonzero (x y : Fp2) : x <> fp2_zero -> y <> fp2_zero -> fp2_mul x y <> fp2_zero.
Proof.
  intros Hx Hy Hxy. apply Hy.
  transitivity (fp2_mul (fp2_mul (fp2_inv x) x) y); [| rewrite <- (@Ring_theory.Rmul_assoc _ _ _ _ _ _ _ _ (@fp2_ring_theory p381)), Hxy; ring].
  replace (fp2_mul (fp2_inv x) x) with fp2_one by (rewrite <- (fp2_inv_ok x Hx); ring). ring.
Qed.

(** *** Fermat in Fp2, through the embedding into Fp12 *)

Lemma frob_p2_e212 (g1 g2 c : Fp2) (r : Fp2) :
  P.fp12_frobenius_p2 p g1 g2 c (e212 r) = e212 r.
Proof.
  cbv [e212 e612 e26 P.fp12_frobenius_p2 P.fp6_frobenius_p2 P.fp6_mul_fp2 P.fp12_build P.fp12_c0
       P.fp12_c1 P.fp6_build P.fp6_c0 P.fp6_c1 P.fp6_c2 P.fp6_zero fst snd].
  split_to_fp2; ring.
Qed.

Lemma e212_inj (a b : Fp2) : e212 a = e212 b -> a = b.
Proof. intros H. exact (f_equal (fun x => fst (fst (fst x))) H). Qed.

Lemma pp_pos : (Npos (p * p) = N.succ (Npos (p * p) - 1))%N.
Proof. lia. Qed.

Lemma fp2_fermat (r : Fp2) : r <> fp2_zero -> pw (e212 r) (Npos (p * p) - 1) = fp12_one.
Proof.
  intros Hr.
  pose proof (frobenius_p2_381_is_pow (e212 r)) as H.
  rewrite frob_p2_e212, pp_pos, pw_succ in H.
  revert H. generalize (pw (e212 r) (Npos (p * p) - 1)). intros X H.
  transitivity (fp12_mul (fp12_mul (e212 (fp2_inv r)) (e212 r)) X).
  - rewrite <- e212_mul.
    replace (fp2_mul (fp2_inv r) r) with fp2_one by (rewrite <- (fp2_inv_ok r Hr); ring).
    rewrite e212_one. ring.
  - transitivity (fp12_mul (e212 (fp2_inv r)) (fp12_mul (e212 r) X)); [ring |].
    rewrite <- H, <- e212_mul.
    replace (fp2_mul (fp2_inv r) r) with fp2_one by (rewrite <- (fp2_inv_ok r Hr); ring).
    reflexivity.
Qed.

Lemma xi2_nonzero : xi2 <> fp2_zero.
Proof. intro H. apply F_one_neq_zero. exact (f_equal fst H). Qed.

Lemma gamma1_p2_381_neq_one : gamma1_p2_381 <> fp2_one.
Proof. intro H. apply (f_equal (fun x => F.to_Z (fst x))) in H. vm_compute in H. discriminate. Qed.

Lemma xi_noncube : ~ exists r : Fp2, fp2_mul r (fp2_mul r r) = xi2.
Proof.
  intros [r Hr].
  assert (Hr0 : r <> fp2_zero).
  { intro E. subst r. apply xi2_nonzero. rewrite <- Hr. ring. }
  pose proof H381_gamma1_p2 as H.
  rewrite <- Hr, !e212_mul in H.
  replace (fp12_mul (e212 r) (fp12_mul (e212 r) (e212 r))) with (pw (e212 r) 3) in H
    by (change 3%N with (N.succ (N.succ (N.succ 0))); rewrite !pw_succ, pw_0; ring).
  rewrite <- pw_mul in H.
  replace (3 * Z.to_N ((Z.pos p * Z.pos p - 1) / 3))%N with (Npos (p * p) - 1)%N in H
    by (vm_compute; reflexivity).
  rewrite (fp2_fermat r Hr0), <- e212_one in H.
  apply gamma1_p2_381_neq_one. symmetry. exact (e212_inj _ _ H).
Qed.

Definition e2_2 : positive := Eval vm_compute in Z.to_pos ((Z.pos p * Z.pos p - 1) / 2).
Definition xi_half_Z : Z * Z := Eval vm_compute in zpow2 (1, 1)%Z e2_2.
Lemma xi_half_pow : zpow2 (1, 1)%Z e2_2 = xi_half_Z.
Proof. vm_compute. reflexivity. Qed.

Lemma xi_nonsquare : ~ exists s : Fp2, fp2_mul s s = xi2.
Proof.
  intros [s Hs].
  assert (Hs0 : s <> fp2_zero).
  { intro E. subst s. apply xi2_nonzero. rewrite <- Hs. ring. }
  pose proof (pw_xi2 _ _ xi_half_pow) as H.
  rewrite <- Hs, e212_mul in H.
  rewrite pw_sq in H.
  replace (2 * Npos e2_2)%N with (Npos (p * p) - 1)%N in H by (vm_compute; reflexivity).
  rewrite (fp2_fermat s Hs0), <- e212_one in H.
  apply e212_inj in H.
  apply (f_equal (fun x => F.to_Z (fst x))) in H. vm_compute in H. discriminate.
Qed.

(* ================================================================ *)
(** ** Fp6                                                           *)
(* ================================================================ *)

Local Notation "a + b" := (fp2_add a b).
Local Notation "a - b" := (fp2_sub a b).
Local Notation "a * b" := (fp2_mul a b).
Local Notation "0" := fp2_zero.
Local Notation "1" := fp2_one.
Local Notation xi := xi2.

(** a * x = 0 in Fp2[v]/(v^3 - xi), componentwise. *)
Definition kills (a0 a1 a2 x0 x1 x2 : Fp2) : Prop :=
  a0 * x0 + xi * (a1 * x2 + a2 * x1) = 0 /\
  a0 * x1 + a1 * x0 + xi * (a2 * x2) = 0 /\
  a0 * x2 + a1 * x1 + a2 * x0 = 0.

Lemma kills_deg0 a0 a1 a2 x0 :
  kills a0 a1 a2 x0 0 0 -> x0 <> 0 -> a0 = 0 /\ a1 = 0 /\ a2 = 0.
Proof.
  intros [E0 [E1 E2]] Hx.
  repeat split.
  - transitivity (a0 * x0 * fp2_inv x0); [field; exact Hx |].
    replace (a0 * x0) with 0 by (rewrite <- E0; ring). ring.
  - transitivity (a1 * x0 * fp2_inv x0); [field; exact Hx |].
    replace (a1 * x0) with 0 by (rewrite <- E1; ring). ring.
  - transitivity (a2 * x0 * fp2_inv x0); [field; exact Hx |].
    replace (a2 * x0) with 0 by (rewrite <- E2; ring). ring.
Qed.

Lemma kills_deg1 a0 a1 a2 x0 x1 :
  kills a0 a1 a2 x0 x1 0 -> x1 <> 0 -> a0 = 0 /\ a1 = 0 /\ a2 = 0.
Proof.
  intros [E0 [E1 E2]] Hx.
  set (r := (fp2_sub 0 x0) * fp2_inv x1).
  assert (A1 : a1 = r * a2).
  { subst r. transitivity ((a1 * x1 + a2 * x0) * fp2_inv x1 + (fp2_sub 0 x0) * fp2_inv x1 * a2);
      [field; exact Hx |].
    replace (a1 * x1 + a2 * x0) with 0 by (rewrite <- E2; ring). ring. }
  assert (A0 : a0 = r * a1).
  { subst r. transitivity ((a0 * x1 + a1 * x0) * fp2_inv x1 + (fp2_sub 0 x0) * fp2_inv x1 * a1);
      [field; exact Hx |].
    replace (a0 * x1 + a1 * x0) with 0 by (rewrite <- E1; ring). ring. }
  assert (AX : xi * a2 = r * a0).
  { subst r. transitivity ((a0 * x0 + xi * (a1 * 0 + a2 * x1)) * fp2_inv x1
                           + (fp2_sub 0 x0) * fp2_inv x1 * a0);
      [field; exact Hx |].
    rewrite E0. ring. }
  destruct (fp2_eq_dec a2 0) as [Z2 | Z2].
  - subst a2. assert (a1 = 0) by (rewrite A1; ring). subst a1.
    assert (a0 = 0) by (rewrite A0; ring). subst a0. auto.
  - exfalso. apply xi_noncube. exists r.
    rewrite A0, A1 in AX.
    transitivity ((r * (r * r)) * a2 * fp2_inv a2); [field; exact Z2 |].
    transitivity (xi * a2 * fp2_inv a2); [| field; exact Z2].
    rewrite AX. ring.
Qed.

Lemma kills_v a0 a1 a2 x0 x1 x2 :
  kills a0 a1 a2 x0 x1 x2 -> kills a0 a1 a2 (xi * x2) x0 x1.
Proof.
  intros [E0 [E1 E2]]. repeat split.
  - transitivity (xi * (a0 * x2 + a1 * x1 + a2 * x0)); [ring |]. rewrite E2. ring.
  - transitivity (a0 * x0 + xi * (a1 * x2 + a2 * x1)); [ring |]. exact E0.
  - transitivity (a0 * x1 + a1 * x0 + xi * (a2 * x2)); [ring |]. exact E1.
Qed.

Lemma kills_lin a0 a1 a2 x0 x1 x2 y0 y1 y2 c d :
  kills a0 a1 a2 x0 x1 x2 -> kills a0 a1 a2 y0 y1 y2 ->
  kills a0 a1 a2 (c * x0 - d * y0) (c * x1 - d * y1) (c * x2 - d * y2).
Proof.
  intros [E0 [E1 E2]] [F0 [F1 F2]]. repeat split.
  - transitivity (c * (a0 * x0 + xi * (a1 * x2 + a2 * x1)) - d * (a0 * y0 + xi * (a1 * y2 + a2 * y1)));
      [ring |]. rewrite E0, F0. ring.
  - transitivity (c * (a0 * x1 + a1 * x0 + xi * (a2 * x2)) - d * (a0 * y1 + a1 * y0 + xi * (a2 * y2)));
      [ring |]. rewrite E1, F1. ring.
  - transitivity (c * (a0 * x2 + a1 * x1 + a2 * x0) - d * (a0 * y2 + a1 * y1 + a2 * y0));
      [ring |]. rewrite E2, F2. ring.
Qed.

Lemma kills_any a0 a1 a2 x0 x1 x2 :
  kills a0 a1 a2 x0 x1 x2 -> (x0, x1, x2) <> (0, 0, 0) -> a0 = 0 /\ a1 = 0 /\ a2 = 0.
Proof.
  intros K Hx.
  destruct (fp2_eq_dec x2 0) as [Z2 | Z2].
  - subst x2. destruct (fp2_eq_dec x1 0) as [Z1 | Z1].
    + subst x1. apply (kills_deg0 _ _ _ x0 K). intro E; apply Hx; subst; reflexivity.
    + exact (kills_deg1 _ _ _ x0 x1 K Z1).
  - (* y := x2 * (v x) - x1 * x has no v^2 term *)
    pose proof (kills_lin _ _ _ _ _ _ _ _ _ x2 x1 (kills_v _ _ _ _ _ _ K) K) as Ky.
    replace (x2 * x1 - x1 * x2) with fp2_zero in Ky by ring.
    set (y0 := x2 * (xi * x2) - x1 * x0) in Ky.
    set (y1 := x2 * x0 - x1 * x1) in Ky.
    destruct (fp2_eq_dec y1 0) as [Y1 | Y1].
    + rewrite Y1 in Ky. destruct (fp2_eq_dec y0 0) as [Y0 | Y0].
      * exfalso. apply xi_noncube. exists (x1 * fp2_inv x2).
        (* x0 x2 = x1^2, xi x2^2 = x1 x0  =>  xi x2^3 = x1^3 *)
        assert (H0 : xi * (x2 * x2) = x1 * x0) by
          (transitivity (y0 + x1 * x0); [subst y0; ring | rewrite Y0; ring]).
        assert (H1 : x2 * x0 = x1 * x1) by
          (transitivity (y1 + x1 * x1); [subst y1; ring | rewrite Y1; ring]).
        transitivity ((x1 * (x1 * x1)) * fp2_inv (x2 * (x2 * x2))); [field; exact Z2 |].
        rewrite <- H1.
        transitivity ((x2 * (x1 * x0)) * fp2_inv (x2 * (x2 * x2))); [ring |].
        rewrite <- H0. field. exact Z2.
      * exact (kills_deg0 _ _ _ y0 Ky Y0).
    + exact (kills_deg1 _ _ _ y0 y1 Ky Y1).
Qed.

(** The norm of the [Pairing.fp6_inv] formula. *)
Definition nA (a0 a1 a2 : Fp2) := a0 * a0 - xi * (a1 * a2).
Definition nB (a0 a1 a2 : Fp2) := xi * (a2 * a2) - a0 * a1.
Definition nC (a0 a1 a2 : Fp2) := a1 * a1 - a0 * a2.
Definition norm6 (a0 a1 a2 : Fp2) :=
  a0 * nA a0 a1 a2 + xi * (a2 * nB a0 a1 a2 + a1 * nC a0 a1 a2).

Lemma norm6_nonzero a0 a1 a2 : (a0, a1, a2) <> (0, 0, 0) -> norm6 a0 a1 a2 <> 0.
Proof.
  intros Ha Hn.
  assert (K : kills a0 a1 a2 (nA a0 a1 a2) (nB a0 a1 a2) (nC a0 a1 a2)).
  { cbv [kills nA nB nC]. repeat split.
    - rewrite <- Hn. cbv [norm6 nA nB nC]. ring.
    - ring.
    - ring. }
  assert (Hx : (nA a0 a1 a2, nB a0 a1 a2, nC a0 a1 a2) <> (0, 0, 0) -> False).
  { intros Hx. destruct (kills_any _ _ _ _ _ _ K Hx) as [-> [-> ->]]. apply Ha. reflexivity. }
  destruct (fp2_eq_dec (nA a0 a1 a2) 0) as [ZA | ZA];
    [| apply Hx; intro E; apply ZA; exact (f_equal (fun t => fst (fst t)) E)].
  destruct (fp2_eq_dec (nB a0 a1 a2) 0) as [ZB | ZB];
    [| apply Hx; intro E; apply ZB; exact (f_equal (fun t => snd (fst t)) E)].
  destruct (fp2_eq_dec (nC a0 a1 a2) 0) as [ZC | ZC];
    [| apply Hx; intro E; apply ZC; exact (f_equal (fun t => snd t) E)].
  (* A = B = C = 0 *)
  cbv [nA nB nC] in ZA, ZB, ZC.
  destruct (fp2_eq_dec a2 0) as [Z2 | Z2].
  - subst a2. apply Ha.
    assert (a1 = 0).
    { destruct (fp2_eq_dec a1 0) as [? | N1]; [assumption |].
      exfalso. apply (fp2_mul_nonzero a1 a1 N1 N1). rewrite <- ZC. ring. }
    subst a1.
    assert (a0 = 0).
    { destruct (fp2_eq_dec a0 0) as [? | N0]; [assumption |].
      exfalso. apply (fp2_mul_nonzero a0 a0 N0 N0). rewrite <- ZA. ring. }
    subst a0. reflexivity.
  - apply xi_noncube. exists (a1 * fp2_inv a2).
    assert (H0 : xi * (a2 * a2) = a0 * a1) by
      (transitivity ((xi * (a2 * a2) - a0 * a1) + a0 * a1); [ring | rewrite ZB; ring]).
    assert (H1 : a0 * a2 = a1 * a1) by
      (transitivity ((a1 * a1) - (a1 * a1 - a0 * a2)); [ring | rewrite ZC; ring]).
    transitivity ((a1 * (a1 * a1)) * fp2_inv (a2 * (a2 * a2))); [field; exact Z2 |].
    rewrite <- H1.
    transitivity ((a2 * (a0 * a1)) * fp2_inv (a2 * (a2 * a2))); [ring |].
    rewrite <- H0. field. exact Z2.
Qed.

Lemma fp6_inv_ok (a : Fp6) : a <> fp6_zero -> fp6_mul a (P.fp6_inv p a) = fp6_one.
Proof.
  destruct a as [[a0 a1] a2]. intros Ha.
  assert (Hn : norm6 a0 a1 a2 <> 0) by (apply norm6_nonzero; exact Ha).
  cbv [P.fp6_inv P.fp6_mul P.fp6_one P.fp6_build P.fp6_c0 P.fp6_c1 P.fp6_c2 fst snd].
  rewrite ?fp2_mul_xi_eq, ?fp2_sqr_eq.
  remember (fp2_inv _) as c eqn:Ec.
  assert (Hc : fp2_mul (norm6 a0 a1 a2) c = fp2_one).
  { rewrite Ec, <- (fp2_inv_ok _ Hn). f_equal; cbv [norm6 nA nB nC]; ring. }
  clear Ec.
  apply injective_projections; [apply injective_projections|]; cbn [fst snd].
  - rewrite <- Hc. cbv [norm6 nA nB nC]. ring.
  - ring.
  - ring.
Qed.

Lemma fp6_one_neq_zero : fp6_one <> fp6_zero.
Proof. intro H. apply fp2_one_neq_zero. exact (f_equal (fun x => fst (fst x)) H). Qed.

Lemma fp6_mul_nonzero (x y : Fp6) : x <> fp6_zero -> y <> fp6_zero -> fp6_mul x y <> fp6_zero.
Proof.
  intros Hx Hy Hxy. apply Hy.
  transitivity (fp6_mul (fp6_mul (P.fp6_inv p x) x) y).
  - replace (fp6_mul (P.fp6_inv p x) x) with fp6_one by (rewrite <- (fp6_inv_ok x Hx); ring). ring.
  - transitivity (fp6_mul (P.fp6_inv p x) (fp6_mul x y)); [ring |]. rewrite Hxy. ring.
Qed.

(** v is not a square in Fp6. *)
Lemma norm6_sqr a0 a1 a2 :
  let s := fp6_mul (a0, a1, a2) (a0, a1, a2) in
  norm6 (fst (fst s)) (snd (fst s)) (snd s) = norm6 a0 a1 a2 * norm6 a0 a1 a2.
Proof.
  cbv [P.fp6_mul P.fp6_build P.fp6_c0 P.fp6_c1 P.fp6_c2 fst snd norm6 nA nB nC].
  rewrite ?fp2_mul_xi_eq. ring.
Qed.

Lemma v_nonsquare : ~ exists s : Fp6, fp6_mul s s = v6.
Proof.
  intros [[[s0 s1] s2] Hs].
  apply xi_nonsquare. exists (norm6 s0 s1 s2).
  rewrite <- norm6_sqr. cbv zeta. rewrite Hs.
  cbv [v6 P.fp6_build norm6 nA nB nC fst snd]. ring.
Qed.

(* ================================================================ *)
(** ** Fp12                                                          *)
(* ================================================================ *)

Lemma fp6_eq_dec (a b : Fp6) : {a = b} + {a <> b}.
Proof.
  destruct a as [[a0 a1] a2], b as [[b0 b1] b2].
  destruct (fp2_eq_dec a0 b0); [| right; congruence].
  destruct (fp2_eq_dec a1 b1); [| right; congruence].
  destruct (fp2_eq_dec a2 b2); [| right; congruence].
  left; subst; reflexivity.
Defined.

Theorem fp12_inv_ok (f : Fp12) : f <> P.fp12_zero p -> fp12_mul f (P.fp12_inv p f) = fp12_one.
Proof.
  destruct f as [a0 a1]. intros Hf.
  set (n := P.fp6_sub p (fp6_mul a0 a0) (fp6_mul v6 (fp6_mul a1 a1))).
  assert (Hn : n <> fp6_zero).
  { intro Hn. destruct (fp6_eq_dec a1 fp6_zero) as [Z1 | Z1].
    - subst a1. apply Hf.
      destruct (fp6_eq_dec a0 fp6_zero) as [Z0 | Z0]; [subst; reflexivity |].
      exfalso. apply (fp6_mul_nonzero a0 a0 Z0 Z0). rewrite <- Hn. subst n. ring.
    - apply v_nonsquare. exists (fp6_mul a0 (P.fp6_inv p a1)).
      pose proof (fp6_inv_ok a1 Z1) as I1.
      transitivity (fp6_mul (fp6_mul v6 (fp6_mul a1 a1))
                            (fp6_mul (P.fp6_inv p a1) (P.fp6_inv p a1))).
      + replace (fp6_mul v6 (fp6_mul a1 a1)) with (fp6_mul a0 a0)
          by (transitivity (P.fp6_sub p (fp6_mul a0 a0) n); [rewrite Hn; ring | subst n; ring]).
        ring.
      + transitivity (fp6_mul v6 (fp6_mul (fp6_mul a1 (P.fp6_inv p a1))
                                          (fp6_mul a1 (P.fp6_inv p a1)))); [ring |].
        rewrite I1. ring. }
  cbv [P.fp12_inv P.fp12_mul P.fp12_c0 P.fp12_c1 P.fp12_build P.fp12_one fst snd].
  rewrite ?fp6_sqr_eq, ?fp6_mul_by_v_eq.
  pose proof (fp6_inv_ok n Hn) as In.
  replace (P.fp6_sub p (fp6_mul a0 a0) (fp6_mul v6 (fp6_mul a1 a1))) with n by reflexivity.
  f_equal.
  - rewrite <- In. subst n. ring.
  - ring.
Qed.
