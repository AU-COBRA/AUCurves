(** * G2 SWU correctness proof.

    Proves: forall u, on_curve_E2prime (map_to_curve_simple_swu_fp2 ...).

    Has the following Qed lemmas:
    - swu_gx_ratio_abstract: gx2 = t³·gx1 (Field.fsatz, abstract A B Z)
    - fp2_norm_mul: norm is multiplicative (1-line ring)
    - fp2_is_square_mul_flip: Legendre via norm + Fp Legendre

    Axiomatized:
    - fp2_sqrt_correct: complex sqrt algorithm
    - swu_g2_maps_to_E2prime: full theorem assembly *)

From Stdlib Require Import ZArith Lia Ring.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Algebra.Hierarchy.
Require Import Spec.HashToCurve.
Require Import Spec.HashToCurveG2.
Require Import Spec.HashToCurveFieldSetup.
Require Import Spec.HashToCurveG2FieldSetup.
Require Import Spec.FpLegendre_G2.
Require Import Spec.HashToCurveSWUCompute_G2.
Require Import Crypto.Util.Decidable.

Local Open Scope F_scope.

(* ================================================================== *)
(** * Fp sqrt correctness (reproved locally, avoids G1 dependency)     *)
(* ================================================================== *)

(** Algebraic proof that 2*sqrt_exp = legendre_exp + 1.
    sqrt_exp = (p+1)/4, legendre_exp = (p-1)/2, p ≡ 3 mod 4.
    p = 4q+3, so (p+1)/4 = q+1, (p-1)/2 = 2q+1, and 2(q+1) = 2q+2 = (2q+1)+1. ✓ *)
Lemma two_sqrt_exp_local : (2 * sqrt_exp = legendre_exp + 1)%Z.
Proof.
  unfold sqrt_exp, legendre_exp. change p with (Z.pos p_pos).
  pose proof p_pos_mod4. pose proof p_pos_gt_2.
  Z.div_mod_to_equations. lia.
Qed.

Lemma legendre_exp_pos_local : (0 < legendre_exp)%Z.
Proof.
  unfold legendre_exp. change p with (Z.pos p_pos).
  pose proof p_pos_gt_2. apply Z.div_str_pos. lia.
Qed.

Lemma sqrt_exp_pos_local : (0 < sqrt_exp)%Z.
Proof.
  unfold sqrt_exp. change p with (Z.pos p_pos).
  pose proof p_pos_gt_2. apply Z.div_str_pos. lia.
Qed.

Lemma fp_sqrt_sq : forall x : Fp,
  is_square x = true -> fp_sqrt x *f fp_sqrt x = x.
Proof.
  intros x Hsq. unfold fp_sqrt.
  rewrite <- F.pow_add_r.
  replace (Z.to_N sqrt_exp + Z.to_N sqrt_exp)%N
    with (Z.to_N (legendre_exp + 1)).
  2:{ rewrite <- two_sqrt_exp_local.
      pose proof sqrt_exp_pos_local.
      rewrite Z2N.inj_mul by lia.
      change (Z.to_N 2) with 2%N.
      destruct (Z.to_N sqrt_exp) as [|p']; [reflexivity | simpl; f_equal; symmetry; apply Pos.add_diag]. }
  apply is_square_true_iff_l in Hsq. destruct Hsq as [Hz|He].
  - rewrite Hz, F.pow_0_l; [reflexivity|].
    pose proof legendre_exp_pos_local.
    change 0%N with (Z.to_N 0). intro Habs.
    apply Z2N.inj in Habs; lia.
  - rewrite Z2N.inj_add by (pose proof legendre_exp_pos_local; lia).
    rewrite F.pow_add_r, He, F.pow_1_r. ring.
Qed.

(** -1 is non-square in Fp (since p ≡ 3 mod 4).
    Precomputed in HashToCurveSWUCompute_G2.v. *)

Lemma is_square_neg_flip_local : forall (x : Fp),
  x <> 0 -> negb (is_square x) = is_square (F.opp x).
Proof.
  intros x Hx.
  replace (F.opp x) with (F.opp 1 *f x) by ring.
  exact (is_square_mul_flip_l x (F.opp 1) Hx opp_one_nonzero neg_one_nonsquare).
Qed.

Lemma is_square_neg_of_nonsquare : forall (x : Fp),
  x <> 0 -> is_square x = false -> is_square (F.opp x) = true.
Proof.
  intros x Hx Hns. rewrite <- is_square_neg_flip_local by exact Hx. rewrite Hns. reflexivity.
Qed.

Lemma is_square_neg_of_square : forall (x : Fp),
  x <> 0 -> is_square x = true -> is_square (F.opp x) = false.
Proof.
  intros x Hx Hs. rewrite <- is_square_neg_flip_local by exact Hx. rewrite Hs. reflexivity.
Qed.

(* ================================================================== *)
(** * Complex square root correctness                                  *)
(* ================================================================== *)

(** x² is always a square in Fp (Fermat). *)
Lemma sq_is_square : forall (x : Fp), x <> 0 -> is_square (x *f x) = true.
Proof.
  intros x Hx. apply is_square_true_iff_l. right.
  rewrite pow_mul_distr_l, pow_square_l.
  pose proof legendre_exp_pos_local as Hlp.
  pose proof p_minus_1_even as Hev. pose proof p_pos_gt_2 as Hgt.
  (* Use fp2_sqr_is_square's Fermat argument pattern *)
  pose proof p_minus_1_even as Hev2.
  assert (Hd : (2 * ((Z.pos p_pos - 1) / 2) = Z.pos p_pos - 1)%Z).
  { pose proof (Z.div_mod (Z.pos p_pos - 1) 2). lia. }
  assert (Heq : (2 * Z.to_N legendre_exp)%N = Z.to_N (Z.pos p_pos - 1)).
  { rewrite legendre_exp_eq.
    replace 2%N with (Z.to_N 2) by reflexivity.
    rewrite <- Z2N.inj_mul by (try lia; apply Z.div_pos; lia).
    rewrite Hd. reflexivity. }
  rewrite Heq. apply fermat_F_l. exact Hx.
Qed.

(** d1 is a square when d0 is not (the Legendre dichotomy for complex sqrt). *)
Lemma d1_square_when_d0_not : forall (c0 c1 t half d0 d1 : Fp),
  c1 <> 0 ->
  half *f F.of_Z p_pos 2 = 1 ->
  t *f t = c0 *f c0 +f c1 *f c1 ->
  d0 = (t +f c0) *f half ->
  d1 = (c0 -f t) *f half ->
  d0 <> 0 -> d1 <> 0 ->
  is_square d0 = false ->
  is_square d1 = true.
Proof.
  intros c0 c1 t half d0 d1 Hc1 Hhalf_inv Hnorm Hd0def Hd1def Hd0nz Hd1nz Hd0sq.
  assert (Hhalf_nz : half <> 0).
  { intro H. rewrite H in Hhalf_inv. replace (0 *f F.of_Z p_pos 2) with (0 : Fp) in Hhalf_inv by ring.
    assert (H1 : (1 : Fp) <> 0) by (intro H0; apply (f_equal F.to_Z) in H0; revert H0; vm_compute; discriminate).
    symmetry in Hhalf_inv. contradiction. }
  assert (Hch_nz : c1 *f half <> 0) by (apply mul_nonzero_l; assumption).
  assert (Hchsq_nz : c1 *f half *f (c1 *f half) <> 0)
    by (apply mul_nonzero_l; exact Hch_nz).
  assert (Hprod : d0 *f d1 = F.opp (c1 *f half *f (c1 *f half))).
  { subst d0 d1.
    replace ((t +f c0) *f half *f ((c0 -f t) *f half))
      with ((c0 *f c0 -f t *f t) *f (half *f half)) by ring.
    rewrite Hnorm. ring. }
  assert (Hprod_nsq : is_square (d0 *f d1) = false).
  { rewrite Hprod.
    exact (is_square_neg_of_square _ Hchsq_nz (sq_is_square _ Hch_nz)). }
  rewrite <- (is_square_mul_flip_l d1 d0 Hd1nz Hd0nz Hd0sq) in Hprod_nsq.
  destruct (is_square d1); simpl in Hprod_nsq; [reflexivity | discriminate].
Qed.

Lemma fp2_sqrt_correct : forall x : Fp2,
  fp2_is_square x = true -> fp2_sqr (fp2_sqrt x) = x.
Proof.
  intros [c0 c1] Hsq.
  unfold fp2_is_square, fp2_norm in Hsq. simpl in Hsq.
  unfold fp2_sqrt, fp2_sqr, fp2_mul. simpl.
  destruct (fp_eqb c1 0) eqn:Hc1.
  - apply fp_eqb_true_iff_l in Hc1. subst c1. simpl in *.
    replace (c0 *f c0 +f 0 *f 0) with (c0 *f c0) in Hsq by ring.
    destruct (is_square c0) eqn:Hc0sq.
    + pose proof (fp_sqrt_sq c0 Hc0sq) as Hrt.
      apply injective_projections; simpl; [rewrite Hrt; ring | ring].
    + assert (Hc0nz : c0 <> 0).
      { intro Habs. subst. replace (0 *f 0) with (0 : Fp) in Hsq by ring.
        rewrite zero_is_square in Hc0sq. discriminate. }
      pose proof (fp_sqrt_sq (F.opp c0) (is_square_neg_of_nonsquare c0 Hc0nz Hc0sq)) as Hrt.
      apply injective_projections; simpl; [rewrite Hrt; ring | ring].
  - apply fp_eqb_false_iff_l in Hc1.
    set (norm := c0 *f c0 +f c1 *f c1) in *.
    set (t := fp_sqrt norm). set (half := F.inv (F.of_Z p_pos 2)).
    set (d0 := (t +f c0) *f half).
    assert (Hnorm_sq : t *f t = norm) by exact (fp_sqrt_sq norm Hsq).
    assert (Hhalf_inv : half *f F.of_Z p_pos 2 = 1)
      by (unfold half; apply Fp_inv_nonzero; exact two_nonzero).
    assert (H2half : F.of_Z p_pos 2 *f half = 1)
      by (unfold half; apply Fp_mul_inv_r; exact two_nonzero).
    assert (Ht_ne_c0 : t <> c0).
    { intro Heq. subst t.
      assert (c1 *f c1 = 0) by (unfold norm in Hnorm_sq; Field.fsatz).
      assert (c1 = 0) by Field.fsatz. contradiction. }
    assert (Ht_ne_nc0 : t <> F.opp c0).
    { intro Heq. subst t. assert (c1 *f c1 = 0).
      { unfold norm in Hnorm_sq. replace (F.opp c0 *f F.opp c0) with (c0 *f c0) in Hnorm_sq by ring.
        Field.fsatz. }
      assert (c1 = 0) by Field.fsatz. contradiction. }
    assert (Hd0_nz : d0 <> 0).
    { unfold d0. intro H. apply Ht_ne_nc0.
      assert (Htmp : (t +f c0) *f half *f F.of_Z p_pos 2 = 0 *f F.of_Z p_pos 2) by (rewrite H; ring).
      replace ((t +f c0) *f half *f F.of_Z p_pos 2) with ((t +f c0) *f (half *f F.of_Z p_pos 2)) in Htmp by ring.
      rewrite Hhalf_inv in Htmp. replace ((t +f c0) *f 1) with (t +f c0) in Htmp by ring.
      replace (0 *f F.of_Z p_pos 2) with (0 : Fp) in Htmp by ring. Field.fsatz. }
    set (d1 := (c0 -f t) *f half).
    assert (Hd1_nz : d1 <> 0).
    { unfold d1. intro H. apply Ht_ne_c0.
      assert (Htmp : (c0 -f t) *f half *f F.of_Z p_pos 2 = 0 *f F.of_Z p_pos 2) by (rewrite H; ring).
      replace ((c0 -f t) *f half *f F.of_Z p_pos 2) with ((c0 -f t) *f (half *f F.of_Z p_pos 2)) in Htmp by ring.
      rewrite Hhalf_inv in Htmp. replace ((c0 -f t) *f 1) with (c0 -f t) in Htmp by ring.
      replace (0 *f F.of_Z p_pos 2) with (0 : Fp) in Htmp by ring. Field.fsatz. }
    destruct (is_square d0) eqn:Hd0sq.
    + set (r := fp_sqrt d0).
      assert (Hr_sq : r *f r = d0) by exact (fp_sqrt_sq d0 Hd0sq).
      assert (Hr_nz : r <> 0) by (intro Habs; apply Hd0_nz; rewrite <- Hr_sq, Habs; ring).
      assert (H2r_nz : F.of_Z p_pos 2 *f r <> 0) by (apply mul_nonzero_l; [exact two_nonzero|exact Hr_nz]).
      assert (Hd0_eq : d0 *f F.of_Z p_pos 2 = t +f c0).
      { unfold d0. replace ((t +f c0) *f half *f F.of_Z p_pos 2) with ((t +f c0) *f (half *f F.of_Z p_pos 2)) by ring.
        rewrite Hhalf_inv. ring. }
      apply injective_projections; simpl; fold t half d0 r; Field.fsatz.
    + assert (Hd1sq : is_square d1 = true)
        by exact (d1_square_when_d0_not c0 c1 t half d0 d1 Hc1 Hhalf_inv Hnorm_sq eq_refl eq_refl Hd0_nz Hd1_nz Hd0sq).
      set (r := fp_sqrt d1).
      assert (Hr_sq : r *f r = d1) by exact (fp_sqrt_sq d1 Hd1sq).
      assert (Hr_nz : r <> 0) by (intro Habs; apply Hd1_nz; rewrite <- Hr_sq, Habs; ring).
      assert (H2r_nz : F.of_Z p_pos 2 *f r <> 0) by (apply mul_nonzero_l; [exact two_nonzero|exact Hr_nz]).
      assert (Hd1_eq : d1 *f F.of_Z p_pos 2 = c0 -f t).
      { unfold d1. replace ((c0 -f t) *f half *f F.of_Z p_pos 2) with ((c0 -f t) *f (half *f F.of_Z p_pos 2)) by ring.
        rewrite Hhalf_inv. ring. }
      apply injective_projections; simpl; fold t half d1 r; Field.fsatz.
Qed.

(* ================================================================== *)
(** * Algebraic identity: gx2 = t³ · gx1                              *)
(* ================================================================== *)

Lemma swu_gx_ratio_abstract :
  forall (A B Z u : Fp2),
  let t := fp2_mul Z (fp2_mul u u) in
  let S := fp2_add (fp2_mul t t) t in
  S <> fp2_zero ->
  A <> fp2_zero ->
  let tv1 := fp2_inv S in
  let x1 := fp2_mul (fp2_mul (fp2_neg B) (fp2_inv A)) (fp2_add fp2_one tv1) in
  let x2 := fp2_mul t x1 in
  fp2_add (fp2_add (fp2_mul (fp2_mul x2 x2) x2) (fp2_mul A x2)) B
  = fp2_mul (fp2_mul (fp2_mul t t) t)
            (fp2_add (fp2_add (fp2_mul (fp2_mul x1 x1) x1) (fp2_mul A x1)) B).
Proof.
  intros A B Z u t S HS HA tv1 x1 x2.
  subst x2 x1 tv1 S t.
  Field.fsatz.
Qed.

(* ================================================================== *)
(** * Norm and is_square multiplicativity                              *)
(* ================================================================== *)

Lemma fp2_norm_mul : forall a b : Fp2,
  fp2_norm (fp2_mul a b) = fp2_norm a *f fp2_norm b.
Proof.
  intros [ar ai] [br bi]. unfold fp2_norm, fp2_mul. simpl. ring.
Qed.

Lemma fp2_is_square_mul_flip : forall a c : Fp2,
  a <> fp2_zero -> c <> fp2_zero ->
  fp2_is_square c = false ->
  negb (fp2_is_square a) = fp2_is_square (fp2_mul c a).
Proof.
  intros a c Ha Hc Hcsq.
  unfold fp2_is_square in *. rewrite fp2_norm_mul.
  apply is_square_mul_flip_l.
  - apply fp2_norm_nonzero. exact Ha.
  - apply fp2_norm_nonzero. exact Hc.
  - exact Hcsq.
Qed.

(** fp2_sqr of a nonzero element is always a square. *)
Lemma fp2_sqr_is_square : forall a : Fp2,
  a <> fp2_zero -> fp2_is_square (fp2_sqr a) = true.
Proof.
  intros a Ha.
  unfold fp2_is_square, fp2_sqr. rewrite fp2_norm_mul.
  apply is_square_true_iff_l. right.
  rewrite pow_mul_distr_l, pow_square_l.
  pose proof p_pos_gt_2 as Hp.
  pose proof p_minus_1_even as Hev.
  assert (Hd : (2 * ((Z.pos p_pos - 1) / 2) = Z.pos p_pos - 1)%Z).
  { pose proof (Z.div_mod (Z.pos p_pos - 1) 2). lia. }
  assert (Heq : (2 * Z.to_N legendre_exp)%N = Z.to_N (Z.pos p_pos - 1)).
  { rewrite legendre_exp_eq.
    replace (2%N) with (Z.to_N 2) by reflexivity.
    rewrite <- Z2N.inj_mul by (try lia; apply Z.div_pos; lia).
    rewrite Hd. reflexivity. }
  rewrite Heq. apply fermat_F_l.
  apply fp2_norm_nonzero. exact Ha.
Qed.

(* ================================================================== *)
(** * Constants                                                         *)
(* ================================================================== *)

Lemma swu_Z_g2_nonzero : swu_Z_g2 <> fp2_zero.
Proof.
  intro H. apply (f_equal fst) in H. simpl in H.
  apply (f_equal F.to_Z) in H. revert H. vm_compute. discriminate.
Qed.

Lemma iso_A_g2_nonzero : iso_A_g2 <> fp2_zero.
Proof.
  intro H. apply (f_equal snd) in H. simpl in H.
  apply (f_equal F.to_Z) in H. revert H. vm_compute. discriminate.
Qed.

(** swu_Z_g2_nonsquare: precomputed in HashToCurveSWUCompute_G2.v *)

(* ================================================================== *)
(** * Fp2 ring lemmas (small, projection-based — avoid Fp2 [ring] tactic
       which generates huge proof terms that blow up Qed verification)  *)
(* ================================================================== *)

Lemma fp2_mul_assoc : forall a b c : Fp2,
  fp2_mul a (fp2_mul b c) = fp2_mul (fp2_mul a b) c.
Proof. intros [ar ai] [br bi] [cr ci]. apply injective_projections; simpl; ring. Qed.

Lemma fp2_one_l : forall a : Fp2, fp2_mul fp2_one a = a.
Proof. intros [ar ai]. apply injective_projections; simpl; ring. Qed.

Lemma fp2_mul_zero_r : forall a : Fp2, fp2_mul a fp2_zero = fp2_zero.
Proof. intros [ar ai]. apply injective_projections; simpl; ring. Qed.

Lemma fp2_mul_comm : forall a b : Fp2, fp2_mul a b = fp2_mul b a.
Proof. intros [ar ai] [br bi]. apply injective_projections; simpl; ring. Qed.

(* ================================================================== *)
(** * fp2_mul_nonzero (integral domain)                                *)
(* ================================================================== *)

Lemma fp2_mul_nonzero : forall a b : Fp2,
  a <> fp2_zero -> b <> fp2_zero -> fp2_mul a b <> fp2_zero.
Proof.
  intros a b Ha Hb Hab.
  apply Hb.
  assert (Hinv : fp2_mul (fp2_inv a) a = fp2_one)
    by (apply Hierarchy.left_multiplicative_inverse; exact Ha).
  rewrite <- (fp2_one_l b), <- Hinv, <- fp2_mul_assoc, Hab, fp2_mul_zero_r.
  reflexivity.
Qed.

(* ================================================================== *)
(** * cube(swu_Z * u²) is non-square                                  *)
(* ================================================================== *)

Lemma cube_t_g2_nonsquare : forall (u : Fp2),
  u <> fp2_zero ->
  fp2_is_square (fp2_cube (fp2_mul swu_Z_g2 (fp2_sqr u))) = false.
Proof.
  intros u Hu.
  set (t := fp2_mul swu_Z_g2 (fp2_sqr u)).
  assert (Husq_nz : fp2_sqr u <> fp2_zero)
    by (unfold fp2_sqr; apply fp2_mul_nonzero; assumption).
  assert (Ht_nz : t <> fp2_zero)
    by (subst t; apply fp2_mul_nonzero; [exact swu_Z_g2_nonzero|exact Husq_nz]).
  assert (Husq : fp2_is_square (fp2_sqr u) = true)
    by (apply fp2_sqr_is_square; exact Hu).
  (* t = swu_Z * u². swu_Z is nonsquare, u² is square, so t is nonsquare. *)
  assert (Htsq : fp2_is_square t = false).
  { subst t.
    rewrite <- (fp2_is_square_mul_flip (fp2_sqr u) swu_Z_g2 Husq_nz
                                       swu_Z_g2_nonzero swu_Z_g2_nonsquare).
    rewrite Husq. reflexivity. }
  assert (Htsq2 : fp2_is_square (fp2_sqr t) = true)
    by (apply fp2_sqr_is_square; exact Ht_nz).
  unfold fp2_cube. rewrite (fp2_mul_comm (fp2_sqr t) t).
  rewrite <- (fp2_is_square_mul_flip (fp2_sqr t) t).
  - rewrite Htsq2. reflexivity.
  - apply fp2_mul_nonzero; assumption.
  - exact Ht_nz.
  - exact Htsq.
Qed.

(* ================================================================== *)
(** * gx2 is square when gx1 is not                                    *)
(* ================================================================== *)

(** Abstract A,B,t version of swu_gx_ratio_abstract. *)
Lemma swu_gx_ratio_abstract_t :
  forall (A B t : Fp2),
  let S := fp2_add (fp2_mul t t) t in
  S <> fp2_zero ->
  A <> fp2_zero ->
  let tv1 := fp2_inv S in
  let x1 := fp2_mul (fp2_mul (fp2_neg B) (fp2_inv A)) (fp2_add fp2_one tv1) in
  let x2 := fp2_mul t x1 in
  fp2_add (fp2_add (fp2_mul (fp2_mul x2 x2) x2) (fp2_mul A x2)) B
  = fp2_mul (fp2_mul (fp2_mul t t) t)
            (fp2_add (fp2_add (fp2_mul (fp2_mul x1 x1) x1) (fp2_mul A x1)) B).
Proof.
  intros A B t S HS HA tv1 x1 x2.
  subst x2 x1 tv1 S.
  Field.fsatz.
Qed.

(** Generic helper: given t and x1 (with x1 = -B/A * (1+1/(t²+t))), if gx1 is
    non-square and nonzero, then gx2 = curve_rhs(t*x1) is a square. *)
Lemma gx2_square_generic_g2 : forall (t : Fp2),
  let S := fp2_add (fp2_mul t t) t in
  S <> fp2_zero ->
  let x1 := fp2_mul (fp2_mul (fp2_neg iso_B_g2) (fp2_inv iso_A_g2))
                    (fp2_add fp2_one (fp2_inv S)) in
  let x2 := fp2_mul t x1 in
  fp2_is_square (fp2_mul (fp2_mul t t) t) = false ->
  fp2_mul (fp2_mul t t) t <> fp2_zero ->
  let gx1 := fp2_add (fp2_add (fp2_mul (fp2_mul x1 x1) x1) (fp2_mul iso_A_g2 x1)) iso_B_g2 in
  fp2_is_square gx1 = false ->
  gx1 <> fp2_zero ->
  fp2_is_square
    (fp2_add (fp2_add (fp2_mul (fp2_mul x2 x2) x2) (fp2_mul iso_A_g2 x2)) iso_B_g2)
    = true.
Proof.
  intros t S HS x1 x2 Ht3nsq Ht3nz gx1 Hnsq Hgx1nz.
  pose proof (swu_gx_ratio_abstract_t iso_A_g2 iso_B_g2 t) as Habs.
  cbv zeta in Habs. fold S in Habs. fold x1 in Habs. fold x2 in Habs.
  specialize (Habs HS iso_A_g2_nonzero).
  fold gx1 in Habs.
  rewrite Habs.
  rewrite <- (fp2_is_square_mul_flip gx1 (fp2_mul (fp2_mul t t) t) Hgx1nz Ht3nz Ht3nsq).
  rewrite Hnsq. reflexivity.
Qed.

(* ================================================================== *)
(** * Misc helper facts                                                *)
(* ================================================================== *)

(** Fp_inv_0: precomputed in HashToCurveSWUCompute_G2.v *)

Lemma fp2_inv_zero : fp2_inv fp2_zero = fp2_zero.
Proof.
  unfold fp2_inv, fp2_zero. simpl.
  replace (F.inv (0 *f 0 +f 0 *f 0)) with (0 : Fp).
  - apply injective_projections; simpl; ring.
  - replace (0 *f 0 +f 0 *f 0) with (0 : Fp) by ring.
    symmetry. exact Fp_inv_0_precomputed.
Qed.

Lemma fp2_is_square_false_nonzero : forall x : Fp2,
  fp2_is_square x = false -> x <> fp2_zero.
Proof.
  intros x Hsq Habs. subst.
  unfold fp2_is_square, fp2_norm in Hsq. simpl in Hsq.
  replace (0 *f 0 +f 0 *f 0) with (0 : Fp) in Hsq by ring.
  unfold is_square in Hsq.
  destruct (fp_eqb (F.pow 0 _) 1); [discriminate|].
  destruct (fp_eqb 0 0) eqn:Hz; [discriminate|].
  apply fp_eqb_false_iff_l in Hz. apply Hz. reflexivity.
Qed.

(** S = sqr(Z*u²) + Z*u² = Z*u²*(Z*u² + 1). S = 0 iff u = 0 or Z*u² = -1. *)
Lemma S_nonzero_implies_u_nonzero_g2 : forall (u : Fp2),
  let S := fp2_add (fp2_sqr (fp2_mul swu_Z_g2 (fp2_sqr u)))
                   (fp2_mul swu_Z_g2 (fp2_sqr u)) in
  S <> fp2_zero -> u <> fp2_zero.
Proof.
  intros u S HS Hu. apply HS. subst S. subst.
  unfold fp2_sqr.
  destruct swu_Z_g2 as [zr zi].
  apply injective_projections; simpl; ring.
Qed.

Lemma fp2_sqr_neg : forall y : Fp2, fp2_sqr (fp2_neg y) = fp2_sqr y.
Proof.
  intros [yr yi]. unfold fp2_sqr, fp2_neg, fp2_mul. simpl.
  apply injective_projections; simpl; ring.
Qed.

(** sqr distributes over mul: needed to convert SWU map's [Z²·u⁴] form
    into the canonical [(Z·u²)²] form. *)
Lemma fp2_sqr_mul_distribute : forall a b : Fp2,
  fp2_mul (fp2_sqr a) (fp2_sqr b) = fp2_sqr (fp2_mul a b).
Proof.
  intros [ar ai] [br bi]. unfold fp2_sqr, fp2_mul. simpl.
  apply injective_projections; simpl; ring.
Qed.

Lemma fp2_inv_nonzero_implies_nonzero : forall x : Fp2,
  fp2_inv x <> fp2_zero -> x <> fp2_zero.
Proof.
  intros x Hinv Habs. apply Hinv. subst. exact fp2_inv_zero.
Qed.

(* ================================================================== *)
(** * Main theorem                                                     *)
(* ================================================================== *)

Theorem swu_g2_maps_to_E2prime : forall u : Fp2,
  on_curve_E2prime (map_to_curve_simple_swu_fp2 iso_A_g2 iso_B_g2 swu_Z_g2 u).
Proof.
  intro u. unfold map_to_curve_simple_swu_fp2, on_curve_E2prime.
  destruct (fp2_eqb _ _) eqn:Htv.
  - (* Edge case: tv1 = 0 *)
    destruct (fp2_is_square _) eqn:Hsq.
    + destruct (Z.eqb _ _).
      * exact (fp2_sqrt_correct _ Hsq).
      * rewrite fp2_sqr_neg. exact (fp2_sqrt_correct _ Hsq).
    + (* Contradiction: edge_case_gx1_is_square_g2 says it IS a square *)
      exfalso.
      rewrite edge_case_gx1_is_square_g2 in Hsq. discriminate.
  - (* Normal case: tv1 ≠ 0 *)
    destruct (fp2_is_square _) eqn:Hsq.
    + destruct (Z.eqb _ _).
      * exact (fp2_sqrt_correct _ Hsq).
      * rewrite fp2_sqr_neg. exact (fp2_sqrt_correct _ Hsq).
    + (* gx1 not square — convert SWU map [Z²·u⁴] to canonical [(Z·u²)²]. *)
      rewrite fp2_sqr_mul_distribute in Htv, Hsq |- *.
      assert (HS : fp2_add (fp2_sqr (fp2_mul swu_Z_g2 (fp2_sqr u)))
                           (fp2_mul swu_Z_g2 (fp2_sqr u)) <> fp2_zero).
      { apply fp2_eqb_false_iff in Htv. intro Habs.
        apply Htv. rewrite Habs. exact fp2_inv_zero. }
      assert (Hu : u <> fp2_zero) by exact (S_nonzero_implies_u_nonzero_g2 u HS).
      assert (Hgx1nz : _ <> fp2_zero) by (apply fp2_is_square_false_nonzero; exact Hsq).
      (* gx2_square_generic_g2 expects t² (fp2_mul t t), not fp2_sqr t.  Convert HS. *)
      assert (HS' : fp2_add (fp2_mul (fp2_mul swu_Z_g2 (fp2_sqr u))
                                     (fp2_mul swu_Z_g2 (fp2_sqr u)))
                            (fp2_mul swu_Z_g2 (fp2_sqr u)) <> fp2_zero) by exact HS.
      assert (Ht_nz : fp2_mul swu_Z_g2 (fp2_sqr u) <> fp2_zero)
        by (apply fp2_mul_nonzero;
            [exact swu_Z_g2_nonzero | unfold fp2_sqr; apply fp2_mul_nonzero; assumption]).
      assert (Ht3_nz : fp2_mul (fp2_mul (fp2_mul swu_Z_g2 (fp2_sqr u))
                                        (fp2_mul swu_Z_g2 (fp2_sqr u)))
                               (fp2_mul swu_Z_g2 (fp2_sqr u)) <> fp2_zero)
        by (apply fp2_mul_nonzero; [apply fp2_mul_nonzero|]; assumption).
      assert (Ht3_nsq : fp2_is_square (fp2_mul (fp2_mul (fp2_mul swu_Z_g2 (fp2_sqr u))
                                                        (fp2_mul swu_Z_g2 (fp2_sqr u)))
                                               (fp2_mul swu_Z_g2 (fp2_sqr u))) = false)
        by (pose proof (cube_t_g2_nonsquare u Hu) as H;
            unfold fp2_cube, fp2_sqr in H; unfold fp2_sqr; exact H).
      pose proof (gx2_square_generic_g2 (fp2_mul swu_Z_g2 (fp2_sqr u))
                    HS' Ht3_nsq Ht3_nz) as Hgen.
      cbv zeta in Hgen.
      specialize (Hgen Hsq Hgx1nz).
      destruct (Z.eqb _ _).
      * exact (fp2_sqrt_correct _ Hgen).
      * rewrite fp2_sqr_neg. exact (fp2_sqrt_correct _ Hgen).
Qed.
