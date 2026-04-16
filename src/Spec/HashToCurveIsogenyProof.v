(** * Isogeny correctness proof. *)

From Stdlib Require Import ZArith BinPos List Bool Lia.
Import ListNotations.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Spec.HashToCurve.
Require Import Spec.HashToCurveFieldSetup.
Require Import Spec.HashToCurvePolyArith.
Require Import Spec.HashToCurveIsogenyCompute.
Require Import Spec.HashToCurveSWUProof.

Local Open Scope Z_scope.
Import HashToCurveIsogenyCompute.
Local Notation fpoly cs x := (F.of_Z p_pos (poly_eval_Z cs x)).

Lemma pe_cons2 : forall a b rest x,
  poly_eval_Z (a :: b :: rest) x = a + x * poly_eval_Z (b :: rest) x.
Proof. reflexivity. Qed.

Lemma pe_cons_ne : forall c tail x,
  tail <> [] -> poly_eval_Z (c :: tail) x = c + x * poly_eval_Z tail x.
Proof. intros c [|t ts] x Hne; [contradiction|reflexivity]. Qed.

Lemma poly_add_nonempty : forall p a f b g,
  poly_add_Z p (a :: f) (b :: g) <> [].
Proof. intros. simpl. destruct f, g; discriminate. Qed.

Lemma poly_scale_nonempty : forall p c a f,
  poly_scale_Z p c (a :: f) <> [].
Proof. intros. unfold poly_scale_Z. simpl. discriminate. Qed.

(* ================================================================== *)
(** * Z-level polynomial evaluation correctness                        *)
(* ================================================================== *)

Lemma poly_add_Z_eval : forall f g x,
  poly_eval_Z (poly_add_Z p_Z f g) x mod p_Z =
  (poly_eval_Z f x + poly_eval_Z g x) mod p_Z.
Proof.
  induction f as [|a f' IH]; intros g x; [reflexivity|].
  destruct g as [|b g'];
    [change (poly_eval_Z [] x) with 0; rewrite Z.add_0_r; reflexivity|].
  destruct f' as [|a2 f''], g' as [|b2 g''].
  - simpl. rewrite Zmod_mod. reflexivity.
  - simpl poly_add_Z. rewrite pe_cons2.
    change (poly_eval_Z [a] x) with a. rewrite (pe_cons2 b b2 g'' x).
    set (pe := poly_eval_Z (b2 :: g'') x).
    rewrite Zplus_mod_idemp_l. f_equal. ring_simplify. reflexivity.
  - simpl poly_add_Z. rewrite !pe_cons2.
    change (poly_eval_Z [b] x) with b.
    set (pe := poly_eval_Z (a2 :: f'') x).
    rewrite Zplus_mod_idemp_l. f_equal. ring_simplify. reflexivity.
  - change (poly_add_Z p_Z (a :: a2 :: f'') (b :: b2 :: g''))
      with ((a + b) mod p_Z :: poly_add_Z p_Z (a2 :: f'') (b2 :: g'')).
    rewrite (pe_cons_ne _ _ _ (poly_add_nonempty _ a2 f'' b2 g'')).
    rewrite (pe_cons2 a a2 f'' x), (pe_cons2 b b2 g'' x).
    rewrite Zplus_mod_idemp_l.
    rewrite Zplus_mod, (Zmult_mod x).
    rewrite IH.
    rewrite <- (Zmult_mod x), <- Zplus_mod.
    f_equal.
    set (pf := poly_eval_Z (a2 :: f'') x).
    set (pg := poly_eval_Z (b2 :: g'') x).
    clearbody pf pg. clear -pf pg a b x.
    rewrite Z.mul_add_distr_l. ring_simplify. reflexivity.
Qed.

Lemma poly_scale_Z_eval : forall c f x,
  poly_eval_Z (poly_scale_Z p_Z c f) x mod p_Z =
  (c * poly_eval_Z f x) mod p_Z.
Proof.
  intros c f. induction f as [|a f' IH]; intro x.
  - simpl. rewrite Z.mul_0_r. reflexivity.
  - destruct f' as [|a2 f''].
    + simpl. rewrite Zmod_mod. reflexivity.
    + change (poly_scale_Z p_Z c (a :: a2 :: f''))
        with ((c * a) mod p_Z :: poly_scale_Z p_Z c (a2 :: f'')).
      rewrite (pe_cons_ne _ _ _ (poly_scale_nonempty _ c a2 f'')), (pe_cons2 a a2 f'' x).
      set (pe_s := poly_eval_Z (poly_scale_Z p_Z c (a2 :: f'')) x).
      set (pe := poly_eval_Z (a2 :: f'') x).
      rewrite Zplus_mod, (Zmult_mod x pe_s). subst pe_s. rewrite IH.
      rewrite <- (Zmult_mod x), <- Zplus_mod.
      rewrite Zplus_mod_idemp_l. f_equal. subst pe. ring_simplify. reflexivity.
Qed.

Lemma poly_cons0_eval : forall f x,
  poly_eval_Z (0 :: f) x mod p_Z = (x * poly_eval_Z f x) mod p_Z.
Proof.
  intros f x. destruct f as [|a f'].
  - simpl. rewrite Z.mul_0_r. reflexivity.
  - rewrite pe_cons2. rewrite Z.add_0_l. reflexivity.
Qed.

Lemma poly_mul_Z_eval : forall f g x,
  poly_eval_Z (poly_mul_Z p_Z f g) x mod p_Z =
  (poly_eval_Z f x * poly_eval_Z g x) mod p_Z.
Proof.
  induction f as [|a f' IH]; intros g x.
  - reflexivity.
  - change (poly_mul_Z p_Z (a :: f') g)
      with (poly_add_Z p_Z (poly_scale_Z p_Z a g) (0 :: poly_mul_Z p_Z f' g)).
    rewrite poly_add_Z_eval. rewrite Zplus_mod.
    rewrite poly_scale_Z_eval, poly_cons0_eval.
    set (pe_g := poly_eval_Z g x).
    set (pe_mul := poly_eval_Z (poly_mul_Z p_Z f' g) x).
    rewrite Zplus_mod, (Zmult_mod x pe_mul). subst pe_mul. rewrite IH.
    set (pe_f := poly_eval_Z f' x).
    rewrite <- (Zmult_mod x).
    rewrite !Zplus_mod_idemp_l, !Zplus_mod_idemp_r.
    subst pe_f pe_g.
    f_equal.
    destruct f' as [|a2 f''].
    + simpl poly_eval_Z. set (pg := poly_eval_Z g x).
      clearbody pg. clear -pg a x. ring_simplify. reflexivity.
    + rewrite pe_cons2. set (pe := poly_eval_Z (a2 :: f'') x).
      set (pg := poly_eval_Z g x).
      clearbody pe pg. clear -pe pg a x. ring_simplify. reflexivity.
Qed.

Lemma poly_pow_Z_eval : forall f n x,
  poly_eval_Z (poly_pow_Z p_Z f n) x mod p_Z =
  (Z.pow (poly_eval_Z f x) (Z.of_nat n)) mod p_Z.
Proof.
  intros f n. induction n as [|n' IH]; intro x.
  - simpl. reflexivity.
  - simpl poly_pow_Z. rewrite poly_mul_Z_eval.
    set (pe := poly_eval_Z f x).
    rewrite Zmult_mod. subst pe. rewrite IH.
    set (pe := poly_eval_Z f x).
    rewrite <- Zmult_mod.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. reflexivity.
Qed.

(* ================================================================== *)
(** * F-level bridges                                                   *)
(* ================================================================== *)

Lemma fpoly_add : forall f g x,
  fpoly (poly_add_Z p_Z f g) x = @F.add p_pos (fpoly f x) (fpoly g x).
Proof.
  intros. apply F.eq_to_Z_iff.
  rewrite F.to_Z_add, !F.to_Z_of_Z, Zplus_mod_idemp_l, Zplus_mod_idemp_r.
  exact (poly_add_Z_eval f g x).
Qed.

Lemma fpoly_scale : forall c f x,
  fpoly (poly_scale_Z p_Z c f) x = @F.mul p_pos (F.of_Z p_pos c) (fpoly f x).
Proof.
  intros. apply F.eq_to_Z_iff.
  rewrite F.to_Z_mul, !F.to_Z_of_Z, Zmult_mod_idemp_l, Zmult_mod_idemp_r.
  exact (poly_scale_Z_eval c f x).
Qed.

Lemma fpoly_mul : forall f g x,
  fpoly (poly_mul_Z p_Z f g) x = @F.mul p_pos (fpoly f x) (fpoly g x).
Proof.
  intros. apply F.eq_to_Z_iff.
  rewrite F.to_Z_mul, !F.to_Z_of_Z, Zmult_mod_idemp_l, Zmult_mod_idemp_r.
  exact (poly_mul_Z_eval f g x).
Qed.

Lemma Zpow_mod_idemp : forall a p n, 0 <= n -> (a mod p) ^ n mod p = a ^ n mod p.
Proof.
  intros a p0 n Hn. rewrite <- (Z2Nat.id n Hn).
  set (m := Z.to_nat n). clearbody m. clear.
  induction m as [|m' IH]; [reflexivity|].
  rewrite Nat2Z.inj_succ, !Z.pow_succ_r by lia.
  rewrite Zmult_mod, IH, <- Zmult_mod, Zmult_mod_idemp_l. reflexivity.
Qed.

Lemma fpoly_pow : forall f n x,
  fpoly (poly_pow_Z p_Z f n) x = F.pow (fpoly f x) (N.of_nat n).
Proof.
  intros. apply F.eq_to_Z_iff.
  rewrite F.to_Z_pow, !F.to_Z_of_Z, nat_N_Z.
  rewrite Zpow_mod_idemp by lia.
  exact (poly_pow_Z_eval f n x).
Qed.

(* ================================================================== *)
(** * Coefficient correspondences + isogeny identity                    *)
(* ================================================================== *)

Lemma iso_xnum_Z_eq : iso_xnum = map (F.of_Z p_pos) xnum_Z.
Proof. reflexivity. Qed.
Lemma iso_ynum_Z_eq : iso_ynum = map (F.of_Z p_pos) ynum_Z.
Proof. reflexivity. Qed.
Lemma iso_xden_monic_eq : iso_xden ++ [F.one] = map (F.of_Z p_pos) xden_Z.
Proof. reflexivity. Qed.
Lemma iso_yden_monic_eq : iso_yden ++ [F.one] = map (F.of_Z p_pos) yden_Z.
Proof. reflexivity. Qed.

Lemma curve_eprime_as_horner : forall x' : F p_pos,
  cube x' +f iso_A *f x' +f iso_B =
  horner_eval (map (F.of_Z p_pos) curve_eprime_Z) x'.
Proof.
  intro x'. unfold curve_eprime_Z. simpl map. simpl horner_eval.
  change (F.of_Z p_pos iso_B_Z) with iso_B.
  change (F.of_Z p_pos iso_A_Z) with iso_A.
  Opaque iso_A iso_B. unfold cube, sqr. ring. Transparent iso_A iso_B.
Qed.

Lemma isogeny_identity_F : forall (x' : Fp),
  ((cube x' +f iso_A *f x' +f iso_B) *f
    sqr (horner_eval iso_ynum x') *f
    cube (horner_eval_monic iso_xden x') =
  cube (horner_eval iso_xnum x') *f
    sqr (horner_eval_monic iso_yden x') +f
  F.of_Z p_pos 4 *f
    cube (horner_eval_monic iso_xden x') *f
    sqr (horner_eval_monic iso_yden x'))%F.
Proof.
  intro x'.
  rewrite curve_eprime_as_horner, iso_xnum_Z_eq, iso_ynum_Z_eq.
  unfold horner_eval_monic.
  rewrite iso_xden_monic_eq, iso_yden_monic_eq.
  rewrite !horner_eval_of_Z.
  assert (Hsqr : forall a : Fp, sqr a = F.pow a 2%N).
  { intro a. unfold sqr. rewrite F.pow_2_r. reflexivity. }
  assert (Hcube : forall a : Fp, cube a = F.pow a 3%N).
  { intro a. unfold cube, sqr. rewrite F.pow_3_r. reflexivity. }
  rewrite !Hsqr, !Hcube.
  change 2%N with (N.of_nat 2). change 3%N with (N.of_nat 3).
  rewrite <- (fpoly_pow ynum_Z 2), <- (fpoly_pow yden_Z 2).
  rewrite <- (fpoly_pow xnum_Z 3), <- (fpoly_pow xden_Z 3).
  change (Z.pos p_pos) with HashToCurveIsogenyCompute.p_Z.
  rewrite <- ynum2_eq, <- yden2_eq, <- xnum3_eq, <- xden3_eq.
  rewrite <- (fpoly_mul curve_eprime_Z ynum2_Z), <- curve_ynum2_eq.
  rewrite <- (fpoly_mul curve_ynum2_Z xden3_Z), <- lhs_eq.
  rewrite <- (fpoly_mul xnum3_Z yden2_Z), <- xnum3_yden2_eq.
  rewrite <- (fpoly_scale 4 xden3_Z), <- scale4_xden3_eq.
  rewrite <- (fpoly_mul scale4_xden3_Z yden2_Z), <- scale4_xden3_yden2_eq.
  rewrite <- (fpoly_add xnum3_yden2_Z scale4_xden3_yden2_Z), <- rhs_eq.
  apply poly_eval_mod_ext.
  exact isogeny_poly_identity.
Qed.

(* ================================================================== *)
(** * Isogeny maps ALL E' points to E                                  *)
(* ================================================================== *)

(** With the projective iso_map (which returns (0, 2) at kernel points),
    the isogeny is correct for ALL E' points, not just non-kernel ones. *)
Theorem iso_map_on_curve : forall (x' y' : Fp),
  on_curve_Eprime (x', y') ->
  on_curve_E (iso_map (x', y')).
Proof.
  intros x' y' Hcurve.
  unfold on_curve_Eprime in Hcurve.
  unfold on_curve_E, iso_map.
  set (xn := horner_eval iso_xnum x').
  set (xd := horner_eval_monic iso_xden x').
  set (yn := horner_eval iso_ynum x').
  set (yd := horner_eval_monic iso_yden x').
  set (z := xd *f yd).
  destruct (fp_eqb z 0f) eqn:Hz.
  - (* Kernel case: z = 0 → output is (0, of_Z 2), which is on E *)
    (* (of_Z 2)^2 = of_Z 4 = 0^3 + 4 *)
    unfold sqr, cube, bls12_b.
    apply F.eq_to_Z_iff. vm_compute. reflexivity.
  - (* Normal case: z ≠ 0 *)
    apply fp_eqb_false_iff in Hz.
    assert (Hxd : xd <> 0f).
    { intro Habs. apply Hz. subst z. rewrite Habs. ring. }
    assert (Hyd : yd <> 0f).
    { intro Habs. apply Hz. subst z. rewrite Habs. ring. }
    assert (Hident := isogeny_identity_F x').
    fold xn xd yn yd in Hident.
    rewrite <- Hcurve in Hident.
    unfold sqr, cube, bls12_b in *.
    subst z. clearbody xn xd yn yd.
    clear Hcurve x'.
    Opaque F.of_Z.
    field_simplify_eq; try assumption;
      try (apply mul_nonzero; assumption);
      try (apply mul_nonzero; [apply mul_nonzero|]; assumption).
    field_simplify_eq in Hident; try assumption;
      try (apply mul_nonzero; assumption);
      try (apply mul_nonzero; [apply mul_nonzero|]; assumption).
    etransitivity; [exact Hident|].
    Transparent F.of_Z.
    set (four := F.of_Z p_pos 4). clearbody four.
    ring_simplify. reflexivity.
    Unshelve. all: try split; assumption.
Qed.
