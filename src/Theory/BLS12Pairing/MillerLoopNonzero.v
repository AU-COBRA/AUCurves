(** * The BLS12-381 Miller loop output is nonzero.

    For P on the curve y^2 = x^3 + 4 and not at infinity, [Pairing.miller_loop p381 P Q] is a
    nonzero element of Fp12 (for every Q), hence invertible by [Fp12Field381.fp12_inv_ok].
      (i)   [g1_y_nonzero]: y = 0 would give x^3 = -4, but -4 is not a cube in Fp
            ((-4)^((p-1)/3) <> 1, computed; Fermat via [F.Fq_inv_fermat]).
      (ii)  [make_line_nonzero]: a Miller line has (0, (y_P, 0), 0) as its w-component.
      (iii) [fp12_mul_nonzero]: Fp12 has no zero divisors ([fp12_inv_ok]); the loop invariant
            "f <> 0" is kept by squaring and by multiplication with nonzero lines.
*)

From Stdlib Require Import ZArith NArith BinPos List Bool Znumtheory.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Crypto.Algebra.Field.
Require Theory.BLS12Pairing.Pairing.
Require Import Theory.BLS12Pairing.Fp12Ring.
Require Import Theory.BLS12Pairing.Prime381.
Require Import Theory.BLS12Pairing.Fp12Field381.
Module P := Theory.BLS12Pairing.Pairing.

Local Notation p := p381.
Local Notation F := (F p381).
Local Notation Fp6 := ((F * F) * (F * F) * (F * F))%type.
Local Notation Fp12 := (Fp6 * Fp6)%type.

Local Instance p381_prime_inst_mlnz : prime p381 := p381_prime.

Add Field Fp_field381_mlnz : (Algebra.Field.field_theory_for_stdlib_tactic (T:=F)).
Add Ring fp12_ring381_mlnz : (@fp12_ring_theory p381).

(** On-curve predicate for G1 (BLS12-381: y^2 = x^3 + 4). *)
Definition g1_on_curve (P0 : P.G1Affine p) : Prop :=
  F.mul (P.g1_y p P0) (P.g1_y p P0) =
  F.add (F.mul (P.g1_x p P0) (F.mul (P.g1_x p P0) (P.g1_x p P0))) (F.of_Z p 4).

(* ================================================================ *)
(** ** (i) -4 is not a cube in Fp, so y <> 0 on the curve            *)
(* ================================================================ *)

Lemma Fp_fermat (x : F) : x <> F.zero -> F.pow x (Z.to_N (Z.pos p - 1)) = F.one.
Proof.
  intros Hx.
  assert (H2 : (2 < Z.pos p)%Z) by (vm_compute; reflexivity).
  replace (Z.to_N (Z.pos p - 1)) with (N.succ (Z.to_N (Z.pos p - 2))) by (vm_compute; reflexivity).
  rewrite F.pow_succ_r.
  rewrite <- (@F.Fq_inv_fermat p p381_prime H2 x).
  transitivity (F.mul (F.inv x) x); [ring |].
  apply (@F.inv_nonzero p p381_prime). exact Hx.
Qed.

Definition e3_381 : N := Eval vm_compute in Z.to_N ((Z.pos p - 1) / 3).

(* computed in the VM (a goal-level [vm_compute] leaves a VM cast for the kernel) *)
Lemma neg4_pow_ne_one : F.to_Z (F.pow (F.opp (F.of_Z p 4)) e3_381) <> F.to_Z (F.one : F).
Proof. vm_compute. discriminate. Qed.

Lemma neg4_noncube : ~ exists x : F, F.mul x (F.mul x x) = F.opp (F.of_Z p 4).
Proof.
  intros [x Hx].
  assert (Hx0 : x <> F.zero).
  { intro E. subst x. apply (f_equal F.to_Z) in Hx. vm_compute in Hx. discriminate. }
  assert (Hpow : F.pow (F.opp (F.of_Z p 4)) e3_381 = F.one).
  { rewrite <- Hx.
    replace (F.mul x (F.mul x x)) with (F.pow x 3) by (rewrite F.pow_3_r; ring).
    rewrite F.pow_pow_l.
    replace (3 * e3_381)%N with (Z.to_N (Z.pos p - 1)) by (vm_compute; reflexivity).
    exact (Fp_fermat x Hx0). }
  exact (neg4_pow_ne_one (f_equal F.to_Z Hpow)).
Qed.

Lemma g1_y_nonzero (P0 : P.G1Affine p) : g1_on_curve P0 -> P.g1_y p P0 <> F.zero.
Proof.
  unfold g1_on_curve. intros Hc Hy. rewrite Hy in Hc.
  apply neg4_noncube. exists (P.g1_x p P0).
  transitivity (F.sub (F.add (F.mul (P.g1_x p P0) (F.mul (P.g1_x p P0) (P.g1_x p P0)))
                             (F.of_Z p 4)) (F.of_Z p 4)); [ring |].
  rewrite <- Hc. ring.
Qed.

(* ================================================================ *)
(** ** (ii) Miller lines are nonzero                                  *)
(* ================================================================ *)

Lemma fp12_one_neq_zero : P.fp12_one p <> P.fp12_zero p.
Proof.
  intro H. apply (f_equal (fun x : Fp12 => F.to_Z (fst (fst (fst (fst x)))))) in H.
  vm_compute in H. discriminate.
Qed.

Lemma make_line_nonzero lam xt yt (xp yp : F) :
  yp <> F.zero -> P.make_line p lam xt yt xp yp <> P.fp12_zero p.
Proof.
  intros Hy H.
  apply (f_equal (fun x : Fp12 => fst (snd (fst (snd x))))) in H.
  cbv [P.make_line P.fp12_build P.fp6_build P.fp12_zero P.fp6_zero P.fp_to_fp2 P.fp2_zero
       fst snd] in H.
  exact (Hy H).
Qed.

(* ================================================================ *)
(** ** (iii) No zero divisors; the loop invariant                     *)
(* ================================================================ *)

Lemma fp12_mul_nonzero (x y : Fp12) :
  x <> P.fp12_zero p -> y <> P.fp12_zero p -> P.fp12_mul p x y <> P.fp12_zero p.
Proof.
  intros Hx Hy Hxy. apply Hy.
  transitivity (P.fp12_mul p (P.fp12_mul p x (P.fp12_inv p x)) y).
  { rewrite (fp12_inv_ok x Hx). ring. }
  transitivity (P.fp12_mul p (P.fp12_inv p x) (P.fp12_mul p x y)); [ring |].
  rewrite Hxy. ring.
Qed.

Lemma fp12_sqr_nonzero (x : Fp12) : x <> P.fp12_zero p -> P.fp12_sqr p x <> P.fp12_zero p.
Proof. intros Hx. rewrite fp12_sqr_eq. exact (fp12_mul_nonzero x x Hx Hx). Qed.

Lemma miller_loop_step_nonzero qx qy (xp yp : F) (st : Fp12 * ((F * F) * (F * F))) (b : bool) :
  yp <> F.zero -> fst st <> P.fp12_zero p ->
  fst (P.miller_loop_step p qx qy xp yp st b) <> P.fp12_zero p.
Proof.
  intros Hy Hf. destruct st as [f [tx ty]]. simpl in Hf.
  cbv [P.miller_loop_step].
  destruct (P.ec2_double_with_lambda p tx ty _) as [nx ny].
  destruct b.
  - destruct (P.ec2_add_with_lambda p nx ny qx _) as [ax ay]. simpl fst.
    apply fp12_mul_nonzero; [apply fp12_mul_nonzero |];
      [apply fp12_sqr_nonzero; exact Hf | apply make_line_nonzero; exact Hy
      | apply make_line_nonzero; exact Hy].
  - simpl fst.
    apply fp12_mul_nonzero; [apply fp12_sqr_nonzero; exact Hf | apply make_line_nonzero; exact Hy].
Qed.

Lemma miller_fold_nonzero qx qy (xp yp : F) bits :
  yp <> F.zero -> forall st, fst st <> P.fp12_zero p ->
  fst (fold_left (P.miller_loop_step p qx qy xp yp) bits st) <> P.fp12_zero p.
Proof.
  intros Hy. induction bits as [| b bits IH]; intros st Hst; simpl.
  - exact Hst.
  - apply IH. apply miller_loop_step_nonzero; assumption.
Qed.

Theorem miller_loop_nonzero (P0 : P.G1Affine p) (Q0 : P.G2Affine p) :
  (P.g1_infinity p P0 = false -> P.g1_y p P0 <> F.zero) ->
  P.miller_loop p P0 Q0 <> P.fp12_zero p.
Proof.
  intros Hy. unfold P.miller_loop.
  destruct (P.g1_infinity p P0) eqn:E1; cbn [orb].
  - exact fp12_one_neq_zero.
  - destruct (P.g2_infinity p Q0); cbn [orb]; [exact fp12_one_neq_zero |].
    apply miller_fold_nonzero; [exact (Hy eq_refl) | exact fp12_one_neq_zero].
Qed.

(** The Miller loop output for P on the curve is invertible. *)
Theorem miller_loop_nonzero_on_curve (P0 : P.G1Affine p) (Q0 : P.G2Affine p) :
  g1_on_curve P0 -> P.miller_loop p P0 Q0 <> P.fp12_zero p.
Proof. intros Hc. apply miller_loop_nonzero. intros _. exact (g1_y_nonzero P0 Hc). Qed.

Corollary miller_loop_invertible (P0 : P.G1Affine p) (Q0 : P.G2Affine p) :
  g1_on_curve P0 ->
  P.fp12_mul p (P.miller_loop p P0 Q0) (P.fp12_inv p (P.miller_loop p P0 Q0)) = P.fp12_one p.
Proof. intros Hc. apply fp12_inv_ok. exact (miller_loop_nonzero_on_curve P0 Q0 Hc). Qed.

Print Assumptions miller_loop_nonzero_on_curve.
Print Assumptions miller_loop_invertible.
