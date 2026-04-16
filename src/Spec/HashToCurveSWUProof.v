(** * SWU map correctness: the output is always on the isogenous curve E'.

    Proves [swu_maps_to_Eprime] from HashToCurve.v:
      forall u, on_curve_Eprime (map_to_curve_simple_swu iso_A iso_B swu_Z u).

    Key identity:  gx₂ = t³ · gx₁   where t = Z·u².
    Consequence:   Legendre(gx₂) = -Legendre(gx₁)  (since Z is nonsquare).
    Therefore at least one of {gx₁, gx₂} is always a QR.
*)

From Stdlib Require Import ZArith BinPos List Bool.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Spec.HashToCurve.
Require Import Spec.HashToCurveFieldSetup.
Require Import Spec.HashToCurveSWUCompute.

Local Open Scope F_scope.

(* ================================================================== *)
(** * Z-level arithmetic identities (native_compute)                   *)
(* ================================================================== *)

Local Open Scope Z_scope.

Lemma two_sqrt_exp : 2 * sqrt_exp = legendre_exp + 1.
Proof. native_compute. reflexivity. Qed.

Lemma two_legendre_exp : 2 * legendre_exp + 1 = Z.pos p_pos.
Proof. native_compute. reflexivity. Qed.

Lemma two_legendre_exp' : 2 * legendre_exp = Z.pos p_pos - 1.
Proof. native_compute. reflexivity. Qed.

Lemma legendre_exp_pos : (0 < legendre_exp)%Z.
Proof. native_compute. reflexivity. Qed.

Lemma sqrt_exp_pos : (0 < sqrt_exp)%Z.
Proof. native_compute. reflexivity. Qed.

Lemma legendre_exp_nonneg : (0 <= legendre_exp)%Z.
Proof. pose proof legendre_exp_pos. lia. Qed.

Local Close Scope Z_scope.

(* ================================================================== *)
(** * fp_eqb reflection                                                 *)
(* ================================================================== *)

Lemma fp_eqb_true_iff : forall (a b : Fp),
  fp_eqb a b = true <-> a = b.
Proof.
  intros a b. unfold fp_eqb.
  rewrite Z.eqb_eq. split; apply F.eq_to_Z_iff.
Qed.

Lemma fp_eqb_false_iff : forall (a b : Fp),
  fp_eqb a b = false <-> a <> b.
Proof.
  intros a b. unfold fp_eqb.
  rewrite Z.eqb_neq. split.
  - intros H Habs. apply H. apply F.eq_to_Z_iff in Habs. exact Habs.
  - intros H Habs. apply H. apply F.eq_to_Z_iff. exact Habs.
Qed.

(* ================================================================== *)
(** * Product nonzero in a field                                        *)
(* ================================================================== *)

Lemma mul_nonzero : forall (a b : Fp), a <> 0 -> b <> 0 -> a * b <> 0.
Proof.
  intros a b Ha Hb Hab. apply Ha.
  cut (a * (b * F.inv b) = (a * b) * F.inv b). { intro Hassoc.
  cut (b * F.inv b = 1). { intro Hinv.
  cut (a * 1 = a). { intro Hmul1. rewrite <- Hmul1, <- Hinv, Hassoc, Hab. ring. }
  ring. } exact (Fp_mul_inv_r b Hb). } ring.
Qed.

(* ================================================================== *)
(** * Fermat's little theorem for F p_pos                               *)
(* ================================================================== *)

(** x^(p-1) = 1 for nonzero x in F_p.
    Derived from Fq_inv_fermat: inv(x) = x^(p-2),
    and inv(x) * x = 1. *)
Lemma fermat_F : forall (x : Fp),
  x <> 0 -> F.pow x (Z.to_N (Z.pos p_pos - 1)) = 1.
Proof.
  intros x Hx.
  (* inv(x) * x = 1, and inv(x) = x^(p-2) *)
  assert (Hinv : F.inv x * x = 1) by (apply Fp_inv_nonzero; exact Hx).
  assert (Hfermat_inv : F.inv x = F.pow x (Z.to_N (Z.pos p_pos - 2)))
    by (apply (@F.Fq_inv_fermat p_pos p_pos_prime p_pos_gt_2 x)).
  rewrite Hfermat_inv in Hinv.
  (* Hinv : x^(p-2) * x = 1 *)
  (* Rewrite x as x^1 to use pow_add_r *)
  replace (F.pow x (Z.to_N (Z.pos p_pos - 2)) * x)
    with (F.pow x (Z.to_N (Z.pos p_pos - 2)) * F.pow x 1) in Hinv
    by (rewrite F.pow_1_r; reflexivity).
  rewrite <- F.pow_add_r in Hinv.
  replace (Z.to_N (Z.pos p_pos - 2) + 1)%N with (Z.to_N (Z.pos p_pos - 1)) in Hinv
    by (native_compute; reflexivity).
  exact Hinv.
Qed.

(** (x^e)^2 = x^(2e) *)
Lemma pow_square : forall (x : Fp) (e : N),
  F.pow x e * F.pow x e = F.pow x (2 * e).
Proof.
  intros. rewrite <- F.pow_add_r. f_equal. lia.
Qed.

(** The Euler test value x^legendre_exp satisfies v^2 = 1 (when x ≠ 0). *)
Lemma euler_test_sq_one : forall (x : Fp),
  x <> 0 ->
  let v := F.pow x (Z.to_N legendre_exp) in
  v * v = 1.
Proof.
  intros x Hx v. subst v.
  rewrite pow_square.
  replace (2 * Z.to_N legendre_exp)%N with (Z.to_N (Z.pos p_pos - 1))
    by (native_compute; reflexivity).
  exact (fermat_F x Hx).
Qed.

(** In F_p, x*x = 1 implies x = 1 or x = -1. *)
Lemma sq_one_cases : forall (x : Fp),
  x * x = 1 -> x = 1 \/ x = F.opp 1.
Proof.
  intros x Hsq.
  (* (x-1)(x+1) = x²-1 = 0 *)
  assert (H : (x - 1) * (x + 1) = 0).
  { replace ((x - 1) * (x + 1)) with (x * x - 1) by ring.
    rewrite Hsq. ring. }
  destruct (F.eq_dec (x - 1) 0) as [Hl|Hl].
  - left. replace x with (x - 1 + 1) by ring. rewrite Hl. ring.
  - right.
    assert (Hx1 : x + 1 = 0).
    { (* From H: (x-1)*(x+1) = 0 and x-1 ≠ 0 *)
      (* Multiply both sides of H by inv(x-1): inv(x-1)*((x-1)*(x+1)) = 0 *)
      assert (Hstep : F.inv (x - 1) * ((x - 1) * (x + 1)) = 0).
      { rewrite H. ring. }
      (* Rearrange: (inv(x-1)*(x-1)) * (x+1) = 0 *)
      replace (F.inv (x - 1) * ((x - 1) * (x + 1)))
        with (F.inv (x - 1) * (x - 1) * (x + 1)) in Hstep by ring.
      rewrite Fp_inv_nonzero in Hstep by exact Hl.
      replace (1 * (x + 1)) with (x + 1) in Hstep by ring.
      exact Hstep. }
    replace x with ((x + 1) - 1) by ring. rewrite Hx1. ring.
Qed.

(** The Euler test: x^legendre_exp is either 1 or -1 (when x ≠ 0). *)
Lemma euler_test_cases : forall (x : Fp),
  x <> 0 ->
  F.pow x (Z.to_N legendre_exp) = 1 \/ F.pow x (Z.to_N legendre_exp) = F.opp 1.
Proof.
  intros x Hx. apply sq_one_cases. exact (euler_test_sq_one x Hx).
Qed.

(* ================================================================== *)
(** * is_square characterization via F.pow                              *)
(* ================================================================== *)

(** is_square x = true iff x = 0 or x^legendre_exp = 1 *)
Lemma is_square_true_iff : forall (x : Fp),
  is_square x = true <-> (x = 0 \/ F.pow x (Z.to_N legendre_exp) = 1).
Proof.
  intros x. unfold is_square. split.
  - intro H.
    destruct (fp_eqb (F.pow x (Z.to_N legendre_exp)) 1) eqn:He.
    + right. apply fp_eqb_true_iff in He. exact He.
    + destruct (fp_eqb x 0) eqn:Hz; [|discriminate].
      left. apply fp_eqb_true_iff in Hz. exact Hz.
  - intros [Hz | He].
    + rewrite Hz. unfold is_square.
      destruct (fp_eqb (F.pow 0 (Z.to_N legendre_exp)) 1) eqn:He'.
      * reflexivity.
      * destruct (fp_eqb 0 0) eqn:Hz'.
        -- reflexivity.
        -- apply fp_eqb_false_iff in Hz'. exfalso. apply Hz'. reflexivity.
    + rewrite (proj2 (fp_eqb_true_iff _ _) He). reflexivity.
Qed.

(** is_square x = false iff x ≠ 0 and x^legendre_exp ≠ 1
    (which in a prime field means x^legendre_exp = -1). *)
Lemma is_square_false_iff : forall (x : Fp),
  is_square x = false <-> (x <> 0 /\ F.pow x (Z.to_N legendre_exp) <> 1).
Proof.
  intros x.
  rewrite <- Bool.not_true_iff_false, is_square_true_iff.
  split.
  - intro H. split.
    + intro Hz. apply H. left. exact Hz.
    + intro He. apply H. right. exact He.
  - intros [Hx He] [Hz | He']; [exact (Hx Hz) | exact (He He')].
Qed.

(* ================================================================== *)
(** * Legendre multiplicativity via F.pow                               *)
(* ================================================================== *)

(** Key: (a*b)^e = a^e * b^e *)
Lemma pow_mul_distr : forall (a b : Fp) (n : N),
  F.pow (a * b) n = F.pow a n * F.pow b n.
Proof. intros. apply F.pow_mul_l. Qed.

(** Multiplying by a nonsquare flips the is_square predicate. *)
Lemma is_square_mul_flip : forall (a c : Fp),
  a <> 0 -> c <> 0 ->
  is_square c = false ->
  negb (is_square a) = is_square (c * a).
Proof.
  intros a c Ha Hc Hcsq.
  apply is_square_false_iff in Hcsq. destruct Hcsq as [_ Hce].
  (* c^e ≠ 1 and c ≠ 0, so c^e = -1 *)
  assert (Hcm1 : F.pow c (Z.to_N legendre_exp) = F.opp 1).
  { destruct (euler_test_cases c Hc) as [H1|Hm1]; [contradiction | exact Hm1]. }
  (* (c*a)^e = c^e * a^e = (-1) * a^e *)
  assert (Hca : F.pow (c * a) (Z.to_N legendre_exp) =
                F.opp 1 * F.pow a (Z.to_N legendre_exp)).
  { rewrite pow_mul_distr. rewrite Hcm1. reflexivity. }
  assert (Hca_nz : c * a <> 0) by (apply mul_nonzero; assumption).
  destruct (is_square a) eqn:Hasq; simpl negb.
  - (* is_square a = true: a^e = 1 (or a = 0, excluded) *)
    apply is_square_true_iff in Hasq. destruct Hasq as [Hz|Hae].
    { exfalso. exact (Ha Hz). }
    (* (c*a)^e = -1 * 1 = -1 ≠ 1 → is_square(c*a) = false *)
    symmetry. apply is_square_false_iff. split; [exact Hca_nz|].
    rewrite Hca, Hae. replace (F.opp 1 * 1) with (F.opp 1 : Fp) by ring.
    intro Habs.
    (* -1 = 1 contradicts p > 2 *)
    assert (Hbad : F.to_Z (F.opp (1 : Fp)) = F.to_Z (1 : Fp)).
    { f_equal. exact Habs. }
    revert Hbad. vm_compute. discriminate.
  - (* is_square a = false: a^e = -1 *)
    apply is_square_false_iff in Hasq. destruct Hasq as [_ Hane].
    assert (Ham1 : F.pow a (Z.to_N legendre_exp) = F.opp 1).
    { destruct (euler_test_cases a Ha) as [H1|Hm1]; [contradiction | exact Hm1]. }
    (* (c*a)^e = -1 * -1 = 1 *)
    symmetry. apply is_square_true_iff. right.
    rewrite Hca, Ham1. ring.
Qed.

(* ================================================================== *)
(** * cube(Z·u²) is a nonsquare                                        *)
(* ================================================================== *)

Lemma cube_t_nonsquare : forall (u : Fp),
  u <> 0 ->
  is_square (cube (swu_Z * sqr u)) = false.
Proof.
  intros u Hu.
  set (t := swu_Z * sqr u).
  assert (Ht_nz : t <> 0).
  { subst t. apply mul_nonzero; [exact swu_Z_nonzero | unfold sqr; apply mul_nonzero; exact Hu]. }
  (* cube(t) = t * t² = t * (t*t). Since t*t is a square (exists y=t, y*y=t*t),
     is_square(t*t) = true. So is_square(cube(t)) = is_square(t * sq) where sq is square.
     By is_square_mul_flip: negb(is_square(t*t)) = is_square(t * (t*t)) when t nonsquare.
     But we need t to be nonsquare first. *)
  (* Actually: cube(t) = t * (sqr t).
     is_square(sqr t) = true (since sqr t = t*t, witnessed by t).
     If is_square t = false, then is_square(cube t) = is_square(t * sqr t) =
       negb(is_square(sqr t)) via is_square_mul_flip reversed...
     Actually is_square_mul_flip says: negb(is_square(sqr t)) = is_square(t * sqr t).
     So is_square(cube t) = negb(is_square(sqr t)) = negb(true) = false.
     But we need is_square(t) = false first. *)
  (* t = Z*u². We need is_square(Z*u²) = false.
     is_square(u²) = true (exists u). By is_square_mul_flip with c = Z:
     negb(is_square(u²)) = is_square(Z * u²) = is_square(Z*u²).
     is_square(u²) = true, so is_square(Z*u²) = negb(true) = false. *)

  (* Step 1: is_square(sqr u) = true *)
  assert (Hu2sq : is_square (sqr u) = true).
  { apply is_square_true_iff. right. unfold sqr.
    rewrite pow_mul_distr, pow_square.
    replace (2 * Z.to_N legendre_exp)%N with (Z.to_N (Z.pos p_pos - 1))
      by (native_compute; reflexivity).
    exact (fermat_F u Hu). }

  (* Step 2: is_square(t) = is_square(Z * sqr u) = false *)
  assert (Htsq : is_square t = false).
  { subst t.
    rewrite <- (is_square_mul_flip (sqr u) swu_Z).
    - rewrite Hu2sq. reflexivity.
    - unfold sqr. apply mul_nonzero; exact Hu.
    - exact swu_Z_nonzero.
    - exact swu_Z_nonsquare. }

  (* Step 3: is_square(sqr t) = true *)
  assert (Ht2sq : is_square (sqr t) = true).
  { apply is_square_true_iff. right. unfold sqr.
    rewrite pow_mul_distr, pow_square.
    replace (2 * Z.to_N legendre_exp)%N with (Z.to_N (Z.pos p_pos - 1))
      by (native_compute; reflexivity).
    exact (fermat_F t Ht_nz). }

  (* Step 4: cube(t) = t * sqr(t), so is_square(cube t) = negb(is_square(sqr t)) = false *)
  assert (Hcube_eq : cube t = t * sqr t).
  { unfold cube, sqr. ring. }
  rewrite Hcube_eq.
  rewrite <- (is_square_mul_flip (sqr t) t).
  - rewrite Ht2sq. reflexivity.
  - unfold sqr. apply mul_nonzero; exact Ht_nz.
  - exact Ht_nz.
  - exact Htsq.
Qed.

(* ================================================================== *)
(** * Square root correctness                                           *)
(* ================================================================== *)

(** is_square x = true implies existence of a square root. *)
Lemma is_square_exists : forall x : Fp,
  is_square x = true -> exists y : Fp, y * y = x.
Proof.
  intros x Hsq.
  apply is_square_true_iff in Hsq. destruct Hsq as [Hz | He].
  - exists 0. rewrite Hz. ring.
  - (* x^e = 1 where e = legendre_exp = (p-1)/2.
       We claim y = x^((p+1)/4) = x^sqrt_exp works.
       y*y = x^(2*sqrt_exp) = x^(e+1) = x^e * x = 1 * x = x. *)
    exists (F.pow x (Z.to_N sqrt_exp)).
    rewrite <- F.pow_add_r.
    replace (Z.to_N sqrt_exp + Z.to_N sqrt_exp)%N
      with (Z.to_N (legendre_exp + 1))
      by (native_compute; reflexivity).
    rewrite Z2N.inj_add by (pose proof legendre_exp_pos; lia).
    rewrite F.pow_add_r, He, F.pow_1_r. ring.
Qed.

(** Square root correctness: if is_square x = true, then (fp_sqrt x)² = x. *)
Lemma fp_sqrt_correct_F : forall x : Fp,
  is_square x = true -> sqr (fp_sqrt x) = x.
Proof.
  intros x Hsq.
  (* fp_sqrt x = x^sqrt_exp, sqr y = y*y *)
  unfold sqr, fp_sqrt.
  destruct (is_square_exists x Hsq) as [y Hy].
  (* We have y*y = x and need x^sqrt_exp * x^sqrt_exp = x *)
  rewrite <- F.pow_add_r.
  replace (Z.to_N sqrt_exp + Z.to_N sqrt_exp)%N
    with (Z.to_N (legendre_exp + 1))
    by (native_compute; reflexivity).
  apply is_square_true_iff in Hsq. destruct Hsq as [Hz|He].
  - rewrite Hz. rewrite F.pow_0_l.
    + reflexivity.
    + change 0%N with (Z.to_N 0). rewrite Z2N.inj_iff;
        [| pose proof legendre_exp_pos; lia | lia].
      pose proof legendre_exp_pos. lia.
  - rewrite Z2N.inj_add by (pose proof legendre_exp_pos; lia).
    rewrite F.pow_add_r, He, F.pow_1_r. ring.
Qed.

(* ================================================================== *)
(** * Key identity: gx₂ = t³ · gx₁                                    *)
(* ================================================================== *)

Lemma swu_gx_ratio : forall (u : Fp),
  let t := swu_Z * sqr u in
  let S := sqr t + t in
  S <> 0 ->
  let tv1 := F.inv S in
  let x1 := F.opp iso_B * F.inv iso_A * (1 + tv1) in
  let x2 := t * x1 in
  curve_rhs iso_A iso_B x2 = cube t * curve_rhs iso_A iso_B x1.
Proof.
  intros u t S HS tv1 x1 x2.
  subst x2 tv1 x1 S t.
  unfold curve_rhs, cube, sqr.
  field.
  split; [exact HS | exact iso_A_nonzero].
Qed.

(* ================================================================== *)
(** * Derived field facts                                               *)
(* ================================================================== *)

Lemma cube_nonzero : forall (x : Fp), x <> 0 -> cube x <> 0.
Proof.
  intros x Hx. unfold cube, sqr.
  apply mul_nonzero; [apply mul_nonzero; exact Hx | exact Hx].
Qed.

Lemma Zu2_nonzero : forall (u : Fp), u <> 0 -> swu_Z * sqr u <> 0.
Proof.
  intros u Hu. unfold sqr.
  apply mul_nonzero; [exact swu_Z_nonzero | apply mul_nonzero; exact Hu].
Qed.

Lemma opp_on_curve_Eprime : forall x y : Fp,
  on_curve_Eprime (x, y) -> on_curve_Eprime (x, F.opp y).
Proof.
  intros x y H. unfold on_curve_Eprime, sqr in *.
  replace (F.opp y * F.opp y) with (y * y) by ring. exact H.
Qed.

(* ================================================================== *)
(** * Main dichotomy: gx₁ not QR implies gx₂ is QR                    *)
(* ================================================================== *)

Lemma gx2_is_square_when_gx1_not : forall (u : Fp),
  let t := swu_Z * sqr u in
  let S := sqr t + t in
  S <> 0 ->
  u <> 0 ->
  let tv1 := F.inv S in
  let x1 := F.opp iso_B * F.inv iso_A * (1 + tv1) in
  let gx1 := curve_rhs iso_A iso_B x1 in
  let x2 := t * x1 in
  let gx2 := curve_rhs iso_A iso_B x2 in
  is_square gx1 = false ->
  gx1 <> 0 ->
  is_square gx2 = true.
Proof.
  intros u t S HS Hu tv1 x1 gx1 x2 gx2 Hnsq Hgx1nz.
  assert (Hratio := swu_gx_ratio u HS).
  subst gx2 gx1 x2 x1 tv1 S t.
  rewrite Hratio.
  rewrite <- (is_square_mul_flip
    (curve_rhs iso_A iso_B _) (cube (swu_Z * sqr u))
    Hgx1nz (cube_nonzero _ (Zu2_nonzero u Hu))
    (cube_t_nonsquare u Hu)).
  rewrite Hnsq. reflexivity.
Qed.

(* ================================================================== *)
(** * Helper lemmas for main theorem assembly                           *)
(* ================================================================== *)

(** is_square false implies nonzero. *)
Lemma is_square_false_nonzero : forall x : Fp,
  is_square x = false -> x <> 0.
Proof.
  intros x H Habs. subst. rewrite zero_is_square in H. discriminate.
Qed.

(** inv(0) = 0 in our field (verified by vm_compute on F.to_Z). *)
Lemma Fp_inv_0 : F.inv (0 : Fp) = 0.
Proof.
  apply F.eq_to_Z_iff. vm_compute. reflexivity.
Qed.

(** inv(S) ≠ 0 implies S ≠ 0 (since inv(0) = 0). *)
Lemma inv_nonzero_implies_nonzero : forall (x : Fp),
  F.inv x <> 0 -> x <> 0.
Proof.
  intros x Hinv Habs. apply Hinv. subst. exact Fp_inv_0.
Qed.

(** S ≠ 0 implies u ≠ 0. S = Z²u⁴ + Zu² = Zu²(Zu²+1), so S=0 when u=0. *)
Lemma S_nonzero_implies_u_nonzero : forall (u : Fp),
  let S := sqr (swu_Z * sqr u) + swu_Z * sqr u in
  S <> 0 -> u <> 0.
Proof.
  intros u S HS Hu. apply HS. subst S. rewrite Hu. unfold sqr. ring.
Qed.

(** edge_case_gx1_is_square imported from HashToCurveSWUCompute.v *)

(** From sqrt correctness: if is_square(curve_rhs x) = true,
    then (x, fp_sqrt(curve_rhs x)) is on E'. *)
Lemma on_curve_from_sqrt : forall x : Fp,
  is_square (curve_rhs iso_A iso_B x) = true ->
  on_curve_Eprime (x, fp_sqrt (curve_rhs iso_A iso_B x)).
Proof. intros x H. unfold on_curve_Eprime. exact (fp_sqrt_correct_F _ H). Qed.

(** Sign correction preserves curve membership. *)
Lemma on_curve_sign_fix : forall (x y u : Fp),
  on_curve_Eprime (x, y) ->
  on_curve_Eprime (x, if Z.eqb (sgn0 u) (sgn0 y) then y else F.opp y).
Proof.
  intros x y u Hoc. destruct (Z.eqb _ _).
  - exact Hoc.
  - exact (opp_on_curve_Eprime x y Hoc).
Qed.

(** Syntactic lemma: sqr distributes over mul (for matching unfolded map). *)
Lemma sqr_mul_distribute : forall (a b : Fp),
  sqr a * sqr b = sqr (a * b).
Proof. intros. unfold sqr. ring. Qed.

(* ================================================================== *)
(** * Main theorem                                                      *)
(* ================================================================== *)

(** The main theorem: for all u, map_to_curve produces a point on E'.

    Strategy: The proof proceeds by analyzing the SWU map output.
    The map computes gx₁ = curve_rhs(x₁) and either returns
    (x₁, ±√gx₁) or (x₂, ±√gx₂). In both cases, the output (x, y)
    satisfies y² = curve_rhs(x) because √(gx)² = gx when gx is a QR.

    The sign correction (negating y) preserves y² = curve_rhs(x)
    because (-y)² = y².

    The key is showing that the chosen gx is always a QR:
    - If is_square(gx₁) = true, we use gx₁ (trivially QR).
    - If is_square(gx₁) = false, we use gx₂, which is QR by
      gx2_is_square_when_gx1_not (in the normal case) or by
      edge_case_gx1_is_square (the false branch is unreachable
      in the edge case).
*)
(** Main theorem. All mathematical prerequisites are proved above.
    The assembly requires matching the unfolded SWU map expressions
    to our lemma statements. The key steps are:
    1. Destruct on fp_eqb tv1 0 (edge vs normal case)
    2. Destruct on is_square gx1 (which branch)
    3. Destruct on Z.eqb sgn0 (sign correction)
    4. Apply fp_sqrt_correct_F for the chosen branch
    5. Apply opp_on_curve_Eprime for sign-corrected cases
    6. Edge case: contradiction via edge_case_gx1_is_square
    7. Normal case with gx1 false: apply gx2_is_square_when_gx1_not *)
Theorem swu_maps_to_Eprime_proof : swu_maps_to_Eprime.
Proof.
  unfold swu_maps_to_Eprime. intro u.
  unfold map_to_curve_simple_swu, on_curve_Eprime.
  destruct (fp_eqb _ _) eqn:Htv.
  - (* Edge case: tv1 = 0. x1 = B/(Z*A). *)
    destruct (is_square _) eqn:Hsq.
    + destruct (Z.eqb _ _).
      * exact (fp_sqrt_correct_F _ Hsq).
      * unfold sqr at 1. rewrite opp_sqr. exact (fp_sqrt_correct_F _ Hsq).
    + exfalso. rewrite edge_case_gx1_is_square in Hsq. discriminate.
  - (* Normal case: tv1 ≠ 0 *)
    destruct (is_square _) eqn:Hsq.
    + destruct (Z.eqb _ _).
      * exact (fp_sqrt_correct_F _ Hsq).
      * unfold sqr at 1. rewrite opp_sqr. exact (fp_sqrt_correct_F _ Hsq).
    + (* is_square gx1 = false. Need is_square gx2 = true. *)
      (* Rewrite S = z2*u4 + Z*u2 to sqr(Z*u²) + Z*u² *)
      rewrite sqr_mul_distribute in Htv, Hsq |- *.
      (* Now S has the form sqr(swu_Z * sqr u) + swu_Z * sqr u *)
      assert (HS : sqr (swu_Z * sqr u) + swu_Z * sqr u <> 0).
      { apply fp_eqb_false_iff in Htv. intro Habs.
        apply Htv. rewrite Habs. exact Fp_inv_0. }
      assert (Hu : u <> 0) by exact (S_nonzero_implies_u_nonzero u HS).
      assert (Hgx1nz : curve_rhs iso_A iso_B
        (F.opp iso_B * F.inv iso_A *
         (1 + F.inv (sqr (swu_Z * sqr u) + swu_Z * sqr u))) <> 0)
        by (apply is_square_false_nonzero; exact Hsq).
      assert (Hgx2sq := gx2_is_square_when_gx1_not u HS Hu Hsq Hgx1nz).
      destruct (Z.eqb _ _).
      * exact (fp_sqrt_correct_F _ Hgx2sq).
      * unfold sqr at 1. rewrite opp_sqr. exact (fp_sqrt_correct_F _ Hgx2sq).
Qed.
