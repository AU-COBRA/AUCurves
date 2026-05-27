(** Development scratch for the ristretto injectivity residual
    (encode_decode_equiv).  Strengthened with the on-curve hypothesis on
    pP (REQUIRED: an off-curve pP whose encoding decodes would give a
    false E[4] conclusion).  Imports the built RoundTrip.vo. *)

From Stdlib Require Import ZArith NArith.
From Stdlib Require Import micromega.Lia Bool.Bool.
From Stdlib Require Import Init.Byte Lists.List.
Require Import coqutil.Byte coqutil.Word.LittleEndianList.
Require Import Crypto.Spec.ModularArithmetic Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.PrimeFieldTheorems Crypto.Algebra.Hierarchy Crypto.Algebra.Field.
Require Import Crypto.Spec.Curve25519.
Require Import Crypto.Spec.CompleteEdwardsCurve.
Require Import Crypto.Curves.Edwards.AffineProofs.
Require Import Bedrock.Field.Synthesis.Examples.Ristretto255_Encode.
Require Import Bedrock.Field.Synthesis.Examples.Ristretto255_Decode.
Require Import Bedrock.Field.Synthesis.Examples.Ristretto255_RoundTrip.
Require Bedrock.Field.Synthesis.Examples.Ristretto255_Sqrt.
Require Bedrock.Field.Synthesis.Examples.Ristretto255_CaseScratch.
Require Bedrock.Field.Synthesis.Examples.Ristretto255_JacobiQuartic.
Require Import Bedrock.Field.Synthesis.Examples.Ristretto255_MainSubgroup.
Import ListNotations.
Local Open Scope F_scope.
Local Notation Fp := (F.F (2^255 - 19)).
Local Notation Fzero := (F.of_Z _ 0).
Local Notation Fone  := (F.of_Z _ 1).
Local Existing Instance Curve25519.field.
Local Existing Instance Curve25519.char_ge_3.
Add Field _f : (Algebra.Field.field_theory_for_stdlib_tactic(T:=F (2^255-19)%positive))
  (morphism (F.ring_morph (2^255-19)%positive), constants [F.is_constant],
   div (F.morph_div_theory (2^255-19)%positive),
   power_tac (F.power_theory (2^255-19)%positive) [F.is_pow_constant]).

(* a = -1 in Curve25519. *)
Lemma HaQ : Curve25519.E.a = F.opp Fone.
Proof. unfold Curve25519.E.a. apply ModularArithmeticTheorems.F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

(* a/b = c whenever a = c*b and b<>0. *)
Lemma div_eq : forall (a b c : Fp), b <> Fzero -> a = (c * b)%F -> (a / b)%F = c.
Proof. intros a b c Hb Ha. rewrite Ha. field. exact Hb. Qed.

(* ===================== Edwards-completeness denominators =====================
   For any two on-curve affine points, the two [sub_affine] denominators are
   nonzero.  These are exactly the side conditions [step1_reduction] requires.
   Both follow from Edwards-curve completeness ([d] a non-square): see
   [Crypto.Curves.Edwards.Pre.denominator_nonzero_{x,y}].  Pure, reusable. *)
Lemma denomx_nz : forall (x1 y1 x2 y2 : Fp),
  (Curve25519.E.a * (x1 * x1) + y1 * y1 = Fone + Curve25519.E.d * (x1 * x1) * (y1 * y1))%F ->
  (Curve25519.E.a * (x2 * x2) + y2 * y2 = Fone + Curve25519.E.d * (x2 * x2) * (y2 * y2))%F ->
  (Fone + Curve25519.E.d * x1 * x2 * y1 * y2)%F <> Fzero.
Proof.
  intros x1 y1 x2 y2 H1 H2.
  exact (Crypto.Curves.Edwards.Pre.denominator_nonzero_x _ Curve25519.E.nonzero_a
           Curve25519.E.square_a _ Curve25519.E.nonsquare_d _ _ H1 _ _ H2).
Qed.

Lemma denomy_nz : forall (x1 y1 x2 y2 : Fp),
  (Curve25519.E.a * (x1 * x1) + y1 * y1 = Fone + Curve25519.E.d * (x1 * x1) * (y1 * y1))%F ->
  (Curve25519.E.a * (x2 * x2) + y2 * y2 = Fone + Curve25519.E.d * (x2 * x2) * (y2 * y2))%F ->
  (Fone - Curve25519.E.d * x1 * x2 * y1 * y2)%F <> Fzero.
Proof.
  intros x1 y1 x2 y2 H1 H2.
  exact (Crypto.Curves.Edwards.Pre.denominator_nonzero_y _ Curve25519.E.nonzero_a
           Curve25519.E.square_a _ Curve25519.E.nonsquare_d _ _ H1 _ _ H2).
Qed.

(* ===================== STEP 1 reduction (pure field algebra) =====================
   If the Edwards difference numerators/denominators of (x,y) and (x',y') satisfy one
   of the four polynomial systems below (with both sub_affine denominators nonzero),
   then sub_affine (x,y) (x',y') is one of the four 4-torsion points. *)
Lemma step1_reduction : forall (x y x' y' : Fp),
  (Fone + Curve25519.E.d * x * F.opp x' * y * y') <> Fzero ->
  (Fone - Curve25519.E.d * x * F.opp x' * y * y') <> Fzero ->
  (   ((x * y' - y * x' = Fzero) /\ (y * y' - x * x' = Fone + Curve25519.E.d * x * x' * y * y'))
   \/ ((x * y' - y * x' = Fzero) /\ (y * y' - x * x' = F.opp (Fone + Curve25519.E.d * x * x' * y * y')))
   \/ ((y * y' - x * x' = Fzero) /\ (x * y' - y * x' = SQRT_M1 * (Fone - Curve25519.E.d * x * x' * y * y')))
   \/ ((y * y' - x * x' = Fzero) /\ (x * y' - y * x' = F.opp SQRT_M1 * (Fone - Curve25519.E.d * x * x' * y * y'))))%F ->
  is_4torsion_affine (sub_affine (x, y) (x', y')).
Proof.
  intros x y x' y' Hdx Hdy Hcases.
  rewrite sub_affine_eq_pair. unfold is_4torsion_affine, sub_affine_x, sub_affine_y, opp_affine.
  rewrite HaQ.
  destruct Hcases as [[Ha Hb]|[[Ha Hb]|[[Ha Hb]|[Ha Hb]]]];
  [ left | right; left | right; right; left | right; right; right ];
  split.
  - apply (div_eq _ _ Fzero Hdx). transitivity (x * y' - y * x'); [ ring | rewrite Ha; ring ].
  - apply (div_eq _ _ Fone Hdy). transitivity (y * y' - x * x'); [ ring | rewrite Hb; ring ].
  - apply (div_eq _ _ Fzero Hdx). transitivity (x * y' - y * x'); [ ring | rewrite Ha; ring ].
  - apply (div_eq _ _ (F.opp Fone) Hdy). transitivity (y * y' - x * x'); [ ring | rewrite Hb; ring ].
  - apply (div_eq _ _ SQRT_M1 Hdx). transitivity (x * y' - y * x'); [ ring | rewrite Hb; ring ].
  - apply (div_eq _ _ Fzero Hdy). transitivity (y * y' - x * x'); [ ring | rewrite Ha; ring ].
  - apply (div_eq _ _ (F.opp SQRT_M1) Hdx). transitivity (x * y' - y * x'); [ ring | rewrite Hb; ring ].
  - apply (div_eq _ _ Fzero Hdy). transitivity (y * y' - x * x'); [ ring | rewrite Ha; ring ].
Qed.

(* ===================== STEP 2 partial: principal-branch y-determination =====================
   In the encoder's non-rotate / non-flip / was_square branch, the encoded s satisfies
   s^2 = (invsqrtE * x*y * (1-y))^2 with the sqrt invariant (1+y)(1-y)(xy)^2 invsqrtE^2 = 1.
   Combined with the decoder relation s^2 (1+y') = 1-y', this forces y = y' (sign-free).
   This is the cleanest piece of the encoder inversion and is reused by the principal
   (identity, system (i)) torsion case. *)
Lemma yeq_noflip : forall (s x y y' invsqrtE : Fp),
  (s * s * (Fone + y') = Fone - y')%F ->
  (Fone + s * s <> Fzero)%F ->
  (s * s = invsqrtE * (x * y) * (Fone - y) * (invsqrtE * (x * y) * (Fone - y)))%F ->
  ((Fone + y) * (Fone - y) * (x * y * (x * y)) * (invsqrtE * invsqrtE) = Fone)%F ->
  (Fone - y <> Fzero)%F ->
  y = y'.
Proof.
  intros s x y y' invsqrtE Hs2y' Hu2nz Hs2enc Hinv H1y.
  assert (Hs2y : (s * s * (Fone + y) = Fone - y)%F).
  { apply (Ristretto255_Sqrt.mul_cancel_l (Fone - y) _ _ H1y).
    transitivity ((Fone + y) * (Fone - y) * (x * y * (x * y)) * (invsqrtE * invsqrtE) * ((Fone - y) * (Fone - y)))%F.
    - rewrite Hs2enc. ring.
    - rewrite Hinv. ring. }
  apply (Ristretto255_Sqrt.mul_cancel_l (Fone + s * s) _ _ Hu2nz).
  transitivity (Fone - s * s).
  - replace ((Fone + s * s) * y)%F with (y + (s * s * (Fone + y)) - s * s)%F by ring.
    rewrite Hs2y. ring.
  - replace ((Fone + s * s) * y')%F with (y' + (s * s * (Fone + y')) - s * s)%F by ring.
    rewrite Hs2y'. ring.
Qed.

(* ===================== Degenerate-case (arg = 0) helpers =====================
   When the encoder's sqrt argument [(1+y)(1-y)(xy)^2] vanishes, the
   inner [invsqrt] is 0, so [s = 0]; the decoder then pins [(x',y')=(0,1)]
   and [sub_affine (x,y) (0,1) = (x,y)], with [(x,y)] itself in E[4]. *)

(* [s = 0] whenever the sqrt argument is 0 (invsqrt of 0 is 0). *)
Lemma enc_arg0_s0 : forall (x y : Fp),
  ((Fone + y) * (Fone - y) * (x * y * (x * y)))%F = Fzero ->
  ristretto_encode_aux x y Fone (x * y) = Fzero.
Proof.
  intros x y Harg0.
  unfold ristretto_encode_aux.
  assert (Hu2 : ((Fone + y) * (Fone - y) * (x * y * (x * y)))%F = Fzero) by exact Harg0.
  rewrite Harg0.
  assert (Hsr0 : snd (sqrt_ratio_m1 Fone Fzero) = Fzero).
  { unfold sqrt_ratio_m1. cbv zeta. cbn [snd].
    set (r0 := (Fone * (Fzero * Fzero * Fzero) *
      (Fone * (Fzero * Fzero * Fzero * (Fzero * Fzero * Fzero) * Fzero))
      ^ Z.to_N ((2 ^ 255 - 19 - 5) / 8))%F).
    assert (Hr0 : r0 = Fzero) by (unfold r0; field). rewrite Hr0.
    destruct (F.to_Z (Fzero * Fzero * Fzero) =? F.to_Z Fone)%Z;
      [ unfold abs; rewrite Ristretto255_CaseScratch.is_negative_zero; reflexivity
      | destruct (F.to_Z (Fzero * Fzero * Fzero) =? F.to_Z (F.opp Fone))%Z;
        [ assert (Hz : (Fzero * SQRT_M1)%F = Fzero) by field; rewrite Hz;
          unfold abs; rewrite Ristretto255_CaseScratch.is_negative_zero; reflexivity
        | destruct (F.to_Z (Fzero * Fzero * Fzero)
                     =? F.to_Z (F.opp (SQRT_M1 * Fone)))%Z;
          [ assert (Hz : (Fzero * SQRT_M1)%F = Fzero) by field; rewrite Hz;
            unfold abs; rewrite Ristretto255_CaseScratch.is_negative_zero; reflexivity
          | unfold abs; rewrite Ristretto255_CaseScratch.is_negative_zero; reflexivity ] ] ]. }
  destruct (sqrt_ratio_m1 Fone Fzero) as [bb invsqrt] eqn:Esr.
  cbn [snd] in Hsr0. subst invsqrt.
  unfold abs; repeat (destruct (is_negative _)); field.
Qed.

(* On the curve, the sqrt argument vanishing forces [(x,y)] itself into E[4]. *)
Lemma deg_oncurve_torsion : forall (x y : Fp),
  (Curve25519.E.a * (x * x) + y * y = Fone + Curve25519.E.d * (x * x) * (y * y))%F ->
  ((Fone + y) * (Fone - y) * (x * y * (x * y)))%F = Fzero ->
  is_4torsion_affine (x, y).
Proof.
  intros x y Hc Harg0.
  assert (Hfac : ((Fone - y*y) * (x*x*(y*y)))%F = Fzero)
    by (transitivity ((Fone + y) * (Fone - y) * (x * y * (x * y)))%F; [ ring | exact Harg0 ]).
  assert (Ha : Curve25519.E.a = F.opp Fone)
    by (unfold Curve25519.E.a; apply ModularArithmeticTheorems.F.eq_to_Z_iff; vm_compute; reflexivity).
  apply Ristretto255_Sqrt.mul_zero_factor in Hfac. destruct Hfac as [Hy2 | Hxxyy].
  - assert (Hy2' : (y*y)%F = Fone) by (symmetry; apply Ristretto255_Sqrt.sub_eq_zero; exact Hy2).
    assert (Hadx : ((Curve25519.E.a - Curve25519.E.d) * (x * x))%F = Fzero).
    { rewrite Hy2' in Hc.
      assert (Hr2 : ((Curve25519.E.a - Curve25519.E.d) * (x * x))%F
                  = ((Curve25519.E.a * (x*x) + Fone) - (Fone + Curve25519.E.d * (x*x) * Fone))%F) by field.
      rewrite Hr2, <- Hc. field. }
    assert (Had : (Curve25519.E.a - Curve25519.E.d)%F <> Fzero)
      by (unfold Curve25519.E.a, Curve25519.E.d; Decidable.vm_decide).
    apply Ristretto255_Sqrt.mul_zero_factor in Hadx.
    destruct Hadx as [Hbad | Hxx]; [ exfalso; apply Had; exact Hbad | ].
    apply Ristretto255_Sqrt.mul_zero_factor in Hxx.
    assert (Hx0 : x = Fzero) by (destruct Hxx; assumption).
    assert (Hyfac : ((y - Fone) * (y + Fone))%F = Fzero)
      by (transitivity (y*y - Fone)%F; [ ring | rewrite Hy2'; field ]).
    apply Ristretto255_Sqrt.mul_zero_factor in Hyfac. unfold is_4torsion_affine.
    destruct Hyfac as [Hy1 | Hym1].
    + left. split; [exact Hx0 | apply Ristretto255_Sqrt.sub_eq_zero; exact Hy1].
    + right; left. split; [exact Hx0 | apply Ristretto255_Sqrt.add_eq_zero; exact Hym1].
  - apply Ristretto255_Sqrt.mul_zero_factor in Hxxyy. destruct Hxxyy as [Hxx | Hyy].
    + assert (Hx0 : x = Fzero)
        by (apply Ristretto255_Sqrt.mul_zero_factor in Hxx; destruct Hxx; assumption).
      rewrite Hx0 in Hc.
      assert (Hy2' : (y*y)%F = Fone)
        by (transitivity (Fone + Curve25519.E.d * (Fzero*Fzero)*(y*y))%F;
            [ rewrite <- Hc; rewrite Ha; field | field ]).
      assert (Hyfac : ((y - Fone) * (y + Fone))%F = Fzero)
        by (transitivity (y*y - Fone)%F; [ ring | rewrite Hy2'; field ]).
      apply Ristretto255_Sqrt.mul_zero_factor in Hyfac. unfold is_4torsion_affine.
      destruct Hyfac as [Hy1 | Hym1].
      * left. split; [exact Hx0 | apply Ristretto255_Sqrt.sub_eq_zero; exact Hy1].
      * right; left. split; [exact Hx0 | apply Ristretto255_Sqrt.add_eq_zero; exact Hym1].
    + assert (Hy0 : y = Fzero)
        by (apply Ristretto255_Sqrt.mul_zero_factor in Hyy; destruct Hyy; assumption).
      rewrite Hy0 in Hc.
      assert (Hx2 : (x*x)%F = F.opp Fone).
      { rewrite Ha in Hc.
        assert (Hr : (F.opp Fone * (x*x) + Fzero*Fzero)%F = F.opp (x*x)) by field.
        rewrite Hr in Hc.
        assert (Hc2 : F.opp (x*x) = Fone) by (rewrite Hc; field).
        assert (Hr2 : (x*x)%F = F.opp (F.opp (x*x))) by field.
        rewrite Hr2, Hc2. field. }
      assert (Hxfac : ((x - SQRT_M1) * (x + SQRT_M1))%F = Fzero)
        by (transitivity (x*x - SQRT_M1*SQRT_M1)%F;
            [ ring | rewrite Hx2, Ristretto255_CaseScratch.SQRT_M1_sq; field ]).
      apply Ristretto255_Sqrt.mul_zero_factor in Hxfac. unfold is_4torsion_affine.
      destruct Hxfac as [Hxs | Hxms].
      * right; right; left. split; [apply Ristretto255_Sqrt.sub_eq_zero; exact Hxs | exact Hy0].
      * right; right; right. split; [apply Ristretto255_Sqrt.add_eq_zero; exact Hxms | exact Hy0].
Qed.

(* [sub_affine (a,b) (0,1) = (a,b)] (unconditional; denominators collapse to 1). *)
Lemma sub_affine_id_01 : forall (a b : Fp), sub_affine (a, b) (Fzero, Fone) = (a, b).
Proof.
  intros a b. unfold sub_affine, opp_affine.
  f_equal; [ field; Decidable.vm_decide | unfold Curve25519.E.a; field; Decidable.vm_decide ].
Qed.

(* ===================== x-sign pinning helpers =====================
   [abs_pins_sign]: equal squares + nonneg target pin [a = +/- b] by sign of a.
   [oncurve_x2_eq]: on the curve, [x^2] is a function of [y^2] (off the
   [1-y^2=0] locus), so equal [y^2] forces equal [x^2]. *)

Lemma abs_pins_sign : forall (a b : Fp),
  (a * a)%F = (b * b)%F -> is_negative b = false ->
  (is_negative a = false -> a = b) /\ (is_negative a = true -> a = F.opp b).
Proof.
  intros a b Hsq Hbneg.
  assert (Habs : abs a = abs b) by (apply Ristretto255_CaseScratch.abs_eq_of_sq; exact Hsq).
  unfold abs in Habs. rewrite Hbneg in Habs.
  split.
  - intro Ha. rewrite Ha in Habs. exact Habs.
  - intro Ha. rewrite Ha in Habs.
    assert (Hr : a = F.opp (F.opp a)) by field. rewrite Hr, Habs. reflexivity.
Qed.

Lemma oncurve_x2_eq : forall (x y x'' y'' : Fp),
  (Curve25519.E.a * (x * x) + y * y = Fone + Curve25519.E.d * (x * x) * (y * y))%F ->
  (Curve25519.E.a * (x'' * x'') + y'' * y'' = Fone + Curve25519.E.d * (x'' * x'') * (y'' * y''))%F ->
  (y * y)%F = (y'' * y'')%F ->
  ((Fone + y) * (Fone - y))%F <> Fzero ->
  (x * x)%F = (x'' * x'')%F.
Proof.
  intros x y x'' y'' Hc Hc'' Hyy Hu1.
  assert (Ha : Curve25519.E.a = F.opp Fone)
    by (unfold Curve25519.E.a; apply ModularArithmeticTheorems.F.eq_to_Z_iff; vm_compute; reflexivity).
  set (D := (Curve25519.E.a - Curve25519.E.d * (y*y))%F).
  assert (Hx : (x * x * D = Fone - y*y)%F).
  { unfold D. rewrite Ha in Hc |- *.
    assert (Hr : (x * x * (F.opp Fone - Curve25519.E.d * (y*y)))%F
               = ((F.opp Fone * (x*x) + y*y) - (Fone + Curve25519.E.d * (x*x) * (y*y)) + Fone - y*y)%F) by field.
    rewrite Hr, Hc. field. }
  assert (Hx'' : (x'' * x'' * D = Fone - y*y)%F).
  { unfold D. rewrite Ha in Hc'' |- *. rewrite Hyy.
    assert (Hr : (x'' * x'' * (F.opp Fone - Curve25519.E.d * (y''*y'')))%F
               = ((F.opp Fone * (x''*x'') + y''*y'') - (Fone + Curve25519.E.d * (x''*x'') * (y''*y'')) + Fone - y''*y'')%F) by field.
    rewrite Hr, Hc''. field. }
  assert (HDnz : D <> Fzero).
  { intro HD. rewrite HD in Hx.
    assert (Hk : (Fone - y*y)%F = Fzero) by (rewrite <- Hx; field).
    apply Hu1. transitivity (Fone - y*y)%F; [ field | exact Hk ]. }
  apply (Ristretto255_Sqrt.mul_cancel_l D _ _ HDnz).
  transitivity (Fone - y*y)%F; [ transitivity (x*x*D)%F; [ field | exact Hx ]
                              | transitivity (x''*x''*D)%F; [ exact (eq_sym Hx'') | field ] ].
Qed.

(* 1 - d*x^2 <> 0 for x <> 0 (d is a non-square). *)
Lemma one_sub_dx2_nz : forall (x : Fp), x <> Fzero ->
  (Fone - Curve25519.E.d * (x * x))%F <> Fzero.
Proof.
  intros x Hx Hk.
  assert (Hxx : (x * x)%F <> Fzero)
    by (intro H; destruct (Ristretto255_Sqrt.mul_zero_factor x x H); apply Hx; assumption).
  assert (Hd1 : (Curve25519.E.d * (x * x))%F = Fone)
    by (transitivity (Fone - (Fone - Curve25519.E.d * (x * x)))%F; [ ring | rewrite Hk; ring ]).
  apply (Curve25519.E.nonsquare_d (F.inv x)).
  apply (Ristretto255_Sqrt.mul_cancel_l (x * x) _ _ Hxx).
  replace ((x * x) * Curve25519.E.d)%F with (Fone:Fp) by (rewrite <- Hd1; ring).
  field. exact Hx.
Qed.

(* Rotated on-curve relation: y'^2 = -x^2 forces x'^2 = -y^2 (mirrors
   oncurve_x2_eq via the 1-d*x^2 factor instead of 1-y^2). *)
Lemma oncurve_rot_x2 : forall (x y x' y' : Fp),
  (Curve25519.E.a * (x * x) + y * y = Fone + Curve25519.E.d * (x * x) * (y * y))%F ->
  (Curve25519.E.a * (x' * x') + y' * y' = Fone + Curve25519.E.d * (x' * x') * (y' * y'))%F ->
  (y' * y' = F.opp (x * x))%F ->
  x <> Fzero ->
  (x' * x' = F.opp (y * y))%F.
Proof.
  intros x y x' y' Hc Hc' Hy' Hx.
  pose proof (one_sub_dx2_nz x Hx) as Hdx2.
  rewrite HaQ in Hc, Hc'. rewrite Hy' in Hc'.
  set (D := (Fone - Curve25519.E.d * (x * x))%F) in *.
  assert (Hyx : (y * y * D = Fone + x * x)%F).
  { unfold D.
    assert (Hr : (y * y * (Fone - Curve25519.E.d * (x * x)))%F
               = ((F.opp Fone * (x*x) + y*y) - (Fone + Curve25519.E.d * (x*x) * (y*y)) + Fone + x*x)%F) by field.
    rewrite Hr, Hc. field. }
  assert (Hx'x : (x' * x' * D = F.opp (Fone + x * x))%F).
  { unfold D.
    assert (Hr : (x' * x' * (Fone - Curve25519.E.d * (x * x)))%F
               = ((Fone + Curve25519.E.d * (x'*x') * F.opp (x*x)) - (F.opp Fone * (x'*x') + F.opp (x*x)) + F.opp (Fone + x*x))%F) by field.
    rewrite Hr, Hc'. field. }
  apply (Ristretto255_Sqrt.mul_cancel_l D _ _ Hdx2).
  transitivity (F.opp (Fone + x*x))%F.
  - transitivity (x' * x' * D)%F; [ ring | exact Hx'x ].
  - transitivity (F.opp (y * y * D))%F; [ rewrite Hyx; ring | ring ].
Qed.

(* ============================================================================
   STATUS (ristretto255 injectivity residual / Decaf cofactor theorem).

   DONE (Qed, 0 axioms):
     * [step1_reduction] — the full STEP-1 reduction: any of the four
       polynomial systems (with the two sub_affine denominators nonzero)
       implies [is_4torsion_affine (sub_affine (x,y) (x',y'))].  Pure field
       algebra; covers all four torsion points (0,1),(0,-1),(SQRT_M1,0),
       (-SQRT_M1,0).  REUSABLE.
     * [div_eq], [HaQ] — supporting field/curve facts.
     * [yeq_noflip] — STEP-2 principal-branch y-determination (sign-free):
       the encoder's non-rotate/non-flip/was_square branch pins y = y'.
     * [denomx_nz], [denomy_nz] — the two [sub_affine] denominators
       [1 +/- d*x*x2*y*y2] are nonzero for any two on-curve points (Edwards
       completeness, [d] a non-square).  These discharge the side conditions
       [step1_reduction] requires.  Wrap [Crypto.Curves.Edwards.Pre
       .denominator_nonzero_{x,y}].  REUSABLE.
     * [enc_arg0_s0], [deg_oncurve_torsion], [sub_affine_id_01] — the
       DEGENERATE (sqrt-argument = 0) case, FULLY closed: [s = 0] forces the
       decoder to [(x',y')=(0,1)], [sub_affine (x,y) (0,1) = (x,y)], and on
       the curve the vanishing argument forces [(x,y)] itself into E[4].
     * [abs_pins_sign] — equal squares + nonneg target pin [a = +/- b] by the
       sign bit of [a] (the x-sign-pinning lemma).  REUSABLE.
     * [oncurve_x2_eq] — on the curve [x^2] is a function of [y^2] (off the
       [1-y^2=0] locus): equal [y^2] forces equal [x^2].  REUSABLE.
     * [main_inversion] VERIFIED CORE (machine-checked, 0 axioms): the unified
       encoder inversion [Hstar : s^2*(1+Yf) = z_inv*(1-Yf)], the
       branch-independent magnitude [Hmag : den_inv^2*(1-Yf^2) = z_inv] (curve
       identity + [K2]), the z_inv collapse [z_inv in {1, SQRT_M1}], and the
       cancellation [z_inv = 1 -> Yf = y'].  The top-level
       [encode_decode_equiv'] is fully assembled (Qed) on top of
       [main_inversion]; only [main_inversion]'s final 8-leaf branch dispatch
       (M x rot x flip) remains [Admitted] — see the in-body STATUS there for
       the exact remaining goal and the per-leaf recipe.

   VERIFIED STRUCTURAL RECIPE (machine-checked interactively; the key the
   earlier passes lacked, to be transcribed into the proof body).  After the
   setup below, set [u1e := (1+y)(1-y)], [u2e := x*y], [arg := u1e*u2e^2],
   destruct [sqrt_ratio_m1 1 arg] as [ws inv], and set [zinv := inv*inv*arg].

     (Z) z_inv COLLAPSE.  In the encoder, [z_inv = den1*den2*T
         = inv^2 * u1e * u2e * u2e = inv^2 * arg].  By [sqrt_ratio_m1_correct]
         applied to (1, arg) [needs arg<>0 — see degenerate cases], the value
         [arg*inv*inv] is EXACTLY [1] (ws=true) or [SQRT_M1] (ws=false).  Hence
            Hzinv_val : zinv = Fone \/ zinv = SQRT_M1.
         This pins [rotate = is_negative(u2e*zinv)] and the inner flip
         [is_negative(Xenc*zinv)] with [Xenc = if rotate then y*SQRT_M1 else x].

     (D2) DEN-MAGNITUDE.  With [den_inv = if rotate then inv*u1e*INVSQRT_A_MINUS_D
         else inv*u2e]:
            no-rotate : (inv*u2e)^2                       = zinv * /u1e
            rotate    : (inv*u1e*INVSQRT_A_MINUS_D)^2      = zinv * /(1+x^2)
         The rotate case uses the curve identity (a = -1)
            Hcurve_id : (1+x^2)(1-y^2) = (x*y)^2 (a-d)
         and the constant fact [K2 : INVSQRT_A_MINUS_D^2 (a-d) = 1].

     (STAR) UNIFIED ENCODER INVERSION.  Writing
            Yenc := if rotate then x*SQRT_M1 else y,
            Yf   := if flip   then F.opp Yenc else Yenc,
         one has [s = abs(den_inv*(1 - Yf))], so [s^2 = den_inv^2*(1-Yf)^2],
         and [Yf^2 = Yenc^2].  Combining (D2) with the curve identity gives the
         BRANCH-INDEPENDENT magnitude [den_inv^2*(1-Yf^2) = zinv], hence
            Hstar : s*s*(1 + Yf) = zinv*(1 - Yf).
         (Rotate uses [Yenc^2 = (x*SQRT_M1)^2 = -x^2], so [1-Yf^2 = 1+x^2];
          no-rotate uses [Yenc^2 = y^2], so [1-Yf^2 = 1-y^2 = u1e].)

   The decoder profile gives the dual [Hyvu2 : y'*(1+s^2) = 1-s^2], i.e.
   [Hs2y' : s*s*(1+y') = 1-y'].  For [zinv = Fone], (STAR) and [Hs2y'] subtract
   to [(Yf - y')(1 + s^2) = 0]; since [1 + s^2 <> 0] (= [Hu2nz]) this forces
   [Yf = y'].  For [zinv = SQRT_M1] the analogous step pins the order-4 coset.

   The verified proof skeleton for [encode_decode_equiv'] (all steps below
   were machine-checked interactively and re-establish on each session) is:

       intros x y x' y' Hoc Hdec.
       pose proof (encode_decode_same_s (x, y) (x', y') Hdec) as Hsame.
       set (s := ristretto_encode (to_extended (x, y))) in *.
       unfold ristretto_encode_bytes, ristretto_encode_bytes_of_F in Hdec.
       fold s in Hdec.
       pose proof (decoded_self_characterization s x' y' Hdec) as Hchar.
       cbv zeta in Hchar.
       destruct Hchar as (Hnegs & Hynz & Hu2nz & Hvnz & Hyvu2 & Hxv2v & Hxneg & Hoc_Q).
       (* decoder profile in hand: y'*(1+s^2)=1-s^2, x'^2*v=4s^2, both on curve,
          is_negative s=false, is_negative x'=false, y'<>0 *)
       assert (Hs2y' : s*s*(1+y') = 1-y') ... (* Qed, derived from Hyvu2 *)
       assert (Hsdef : s = ristretto_encode_aux x y 1 (x*y)) by reflexivity.
       unfold ristretto_encode_aux in Hsdef.
       set (Aenc := (1+y)*(1-y)*(x*y*(x*y))) in *.
       destruct (sqrt_ratio_m1 1 Aenc) as [wsenc invsqrtE] eqn:Hsrenc.
       set (zarg := x*y*(invsqrtE*((1+y)*(1-y))*(invsqrtE*(x*y))*(x*y))) in *.
       destruct (is_negative zarg) eqn:Hrot.   (* rotate vs not *)
       (* each rotate branch further splits on the inner flip [is_negative(X'*zarg)]
          and on wsenc via sqrt_ratio_m1_correct *)

   REMAINING GAP (the genuine Decaf cofactor content, ~250-400 LoC):
   From the encoder case-split above, produce one of [step1_reduction]'s four
   polynomial systems.  Per branch:
     - non-rotate, non-flip, was_square : y = y' (have [yeq_noflip]); then
       sign-pinning [is_negative x'=false] + the encoder flip-condition forces
       x = x' (NOT -x'), giving system (i) [identity, (0,1)].
     - non-rotate, flip               : y = -y'  -> system (ii) [(0,-1)].
     - rotate (both flips)            : (x,y) is the order-4 translate
       (SQRT_M1*y', SQRT_M1*x') resp. its negation, using
       INVSQRT_A_MINUS_D^2*(a-d)=1 -> systems (iii)/(iv).
   The Decaf key is that exactly ONE of [Aenc] / [rotated arg] is a square
   (SQRT_M1 is a quadratic non-residue: see local_SQRT_M1_nonsquare in
   Ristretto255_RoundTrip), which is what makes [rotate] well-defined and pins
   the active branch; the [s=0] degenerate case (-> identity coset) and the
   x-sign pinning are the most delicate sub-steps.  Also requires the two
   sub_affine denominators (Edwards completeness, d a non-square) nonzero to
   feed [step1_reduction].
   ============================================================================ *)

(* ===================== MAIN ENCODER INVERSION (arg <> 0) =====================
   The genuine Decaf cofactor content.  From [s = encode_aux x y 1 (x*y)]
   (with the sqrt argument nonzero), the decoder relation [s^2(1+y')=1-y'],
   and the sign/on-curve profile of [(x',y')], invert the encoder to one of
   [step1_reduction]'s four polynomial systems, hence E[4]. *)
(* ===================== M=Fone branch leaves (RC-15 factoring) =====================
   The four M=Fone leaves of [main_inversion], extracted as standalone Qed lemmas.
   Each is LET-FREE (no [set]-bound M/rot/Yf/den_inv/s in scope), so the kernel
   re-checks each in a tiny context.  [main_inversion] keeps only the cheap
   let-handling (deriving [HY'] from HMcancel and the sign from [Hflip]) and
   [apply]s the matching leaf.  This replaces the previous monolithic ~46-min Qed.

   Leaf hypotheses (per branch): both points on curve, [is_negative x'=false],
   the two [sub_affine] denominators nonzero (= step1_reduction's), plus the
   already-resolved [y'] value and the sign condition that [main_inversion]
   computes from the let-context before the [apply]. *)

(* rot=true, flip=true : y' = -(x*SQRT_M1), x' = -(SQRT_M1*y) ; system (iii). *)
Lemma leaf_inv_tt : forall (x y x' y' : Fp),
  (Curve25519.E.a * (x * x) + y * y = Fone + Curve25519.E.d * (x * x) * (y * y))%F ->
  (Curve25519.E.a * (x' * x') + y' * y' = Fone + Curve25519.E.d * (x' * x') * (y' * y'))%F ->
  is_negative x' = false ->
  x <> Fzero -> y <> Fzero -> SQRT_M1 <> Fzero ->
  (Fone + Curve25519.E.d * x * F.opp x' * y * y') <> Fzero ->
  (Fone - Curve25519.E.d * x * F.opp x' * y * y') <> Fzero ->
  y' = F.opp (x * SQRT_M1)%F ->
  is_negative (SQRT_M1 * y) = true ->
  is_4torsion_affine (sub_affine (x, y) (x', y')).
Proof.
  intros x y x' y' Hoc Hoc_Q Hxneg Hxnz Hynz0 HSnz Hdx Hdy HY' Hsneg.
  assert (Hy'2 : (y' * y' = F.opp (x * x))%F)
    by (rewrite HY'; transitivity ((x*x)*(SQRT_M1*SQRT_M1))%F;
        [ ring | rewrite Ristretto255_CaseScratch.SQRT_M1_sq; ring ]).
  pose proof (oncurve_rot_x2 x y x' y' Hoc Hoc_Q Hy'2 Hxnz) as Hx'2.
  assert (Hsymnz : (SQRT_M1 * y)%F <> Fzero)
    by (intro Hk; destruct (Ristretto255_Sqrt.mul_zero_factor _ _ Hk); [ apply HSnz | apply Hynz0 ]; assumption).
  assert (Hbneg : is_negative (F.opp (SQRT_M1 * y)) = false)
    by (rewrite (Ristretto255_Sqrt.is_negative_opp_nonzero _ Hsymnz), Hsneg; reflexivity).
  assert (Hx'eq : x' = F.opp (SQRT_M1 * y)).
  { destruct (abs_pins_sign x' (F.opp (SQRT_M1 * y))) as [Hp _].
    - rewrite Hx'2. transitivity ((SQRT_M1*SQRT_M1)*(y*y))%F;
      [ rewrite Ristretto255_CaseScratch.SQRT_M1_sq; ring | ring ].
    - exact Hbneg.
    - exact (Hp Hxneg). }
  apply step1_reduction; [ exact Hdx | exact Hdy | ].
  assert (Hxxyy : (Curve25519.E.d * x * x' * y * y' = F.opp (Curve25519.E.d*(x*x)*(y*y)))%F).
  { rewrite HY', Hx'eq. transitivity (Curve25519.E.d*(x*x)*(y*y)*(SQRT_M1*SQRT_M1))%F;
    [ ring | rewrite Ristretto255_CaseScratch.SQRT_M1_sq; ring ]. }
  right; right; left. split.
  * rewrite HY', Hx'eq. ring.
  * rewrite Hxxyy, HY', Hx'eq. rewrite HaQ in Hoc.
    transitivity (SQRT_M1 * (F.opp Fone*(x*x) + y*y))%F; [ ring | rewrite Hoc; ring ].
Qed.

(* rot=true, flip=false : y' = x*SQRT_M1, x' = SQRT_M1*y ; system (iv). *)
Lemma leaf_inv_tf : forall (x y x' y' : Fp),
  (Curve25519.E.a * (x * x) + y * y = Fone + Curve25519.E.d * (x * x) * (y * y))%F ->
  (Curve25519.E.a * (x' * x') + y' * y' = Fone + Curve25519.E.d * (x' * x') * (y' * y'))%F ->
  is_negative x' = false ->
  x <> Fzero ->
  (Fone + Curve25519.E.d * x * F.opp x' * y * y') <> Fzero ->
  (Fone - Curve25519.E.d * x * F.opp x' * y * y') <> Fzero ->
  y' = (x * SQRT_M1)%F ->
  is_negative (SQRT_M1 * y) = false ->
  is_4torsion_affine (sub_affine (x, y) (x', y')).
Proof.
  intros x y x' y' Hoc Hoc_Q Hxneg Hxnz Hdx Hdy HY' Hsneg.
  assert (Hy'2 : (y' * y' = F.opp (x * x))%F)
    by (rewrite HY'; transitivity ((x*x)*(SQRT_M1*SQRT_M1))%F;
        [ ring | rewrite Ristretto255_CaseScratch.SQRT_M1_sq; ring ]).
  pose proof (oncurve_rot_x2 x y x' y' Hoc Hoc_Q Hy'2 Hxnz) as Hx'2.
  assert (Hx'eq : x' = (SQRT_M1 * y)%F).
  { destruct (abs_pins_sign x' (SQRT_M1 * y)) as [Hp _].
    - rewrite Hx'2. transitivity ((SQRT_M1*SQRT_M1)*(y*y))%F;
      [ rewrite Ristretto255_CaseScratch.SQRT_M1_sq; ring | ring ].
    - exact Hsneg.
    - exact (Hp Hxneg). }
  apply step1_reduction; [ exact Hdx | exact Hdy | ].
  assert (Hxxyy : (Curve25519.E.d * x * x' * y * y' = F.opp (Curve25519.E.d*(x*x)*(y*y)))%F).
  { rewrite HY', Hx'eq. transitivity (Curve25519.E.d*(x*x)*(y*y)*(SQRT_M1*SQRT_M1))%F;
    [ ring | rewrite Ristretto255_CaseScratch.SQRT_M1_sq; ring ]. }
  right; right; right. split.
  * rewrite HY', Hx'eq. ring.
  * rewrite Hxxyy, HY', Hx'eq. rewrite HaQ in Hoc.
    transitivity (F.opp SQRT_M1 * (F.opp Fone*(x*x) + y*y))%F; [ ring | rewrite Hoc; ring ].
Qed.

(* rot=false, flip=true : y' = -y, x = -x' ; system (ii). *)
Lemma leaf_inv_ft : forall (x y x' y' : Fp),
  (Curve25519.E.a * (x * x) + y * y = Fone + Curve25519.E.d * (x * x) * (y * y))%F ->
  (Curve25519.E.a * (x' * x') + y' * y' = Fone + Curve25519.E.d * (x' * x') * (y' * y'))%F ->
  is_negative x' = false ->
  ((Fone + y) * (Fone - y))%F <> Fzero ->
  (Fone + Curve25519.E.d * x * F.opp x' * y * y') <> Fzero ->
  (Fone - Curve25519.E.d * x * F.opp x' * y * y') <> Fzero ->
  y' = F.opp y ->
  is_negative x = true ->
  is_4torsion_affine (sub_affine (x, y) (x', y')).
Proof.
  intros x y x' y' Hoc Hoc_Q Hxneg Hu1 Hdx Hdy HY' Hxn.
  assert (Hyy2 : (y * y = y' * y')%F) by (rewrite HY'; ring).
  pose proof (oncurve_x2_eq x y x' y' Hoc Hoc_Q Hyy2 Hu1) as Hx2.
  assert (Hxeq : x = F.opp x').
  { destruct (abs_pins_sign x x' Hx2 Hxneg) as [_ Hp]. exact (Hp Hxn). }
  apply step1_reduction; [ exact Hdx | exact Hdy | ].
  right; left. rewrite HY', Hxeq. split.
  * ring.
  * rewrite HaQ in Hoc_Q.
    transitivity (F.opp (F.opp Fone*(x'*x') + (F.opp y)*(F.opp y)))%F; [ ring | ].
    rewrite HY' in Hoc_Q. rewrite Hoc_Q. ring.
Qed.

(* rot=false, flip=false : y' = y, x = x' ; system (i). *)
Lemma leaf_inv_ff : forall (x y x' y' : Fp),
  (Curve25519.E.a * (x * x) + y * y = Fone + Curve25519.E.d * (x * x) * (y * y))%F ->
  (Curve25519.E.a * (x' * x') + y' * y' = Fone + Curve25519.E.d * (x' * x') * (y' * y'))%F ->
  is_negative x' = false ->
  ((Fone + y) * (Fone - y))%F <> Fzero ->
  (Fone + Curve25519.E.d * x * F.opp x' * y * y') <> Fzero ->
  (Fone - Curve25519.E.d * x * F.opp x' * y * y') <> Fzero ->
  y' = y ->
  is_negative x = false ->
  is_4torsion_affine (sub_affine (x, y) (x', y')).
Proof.
  intros x y x' y' Hoc Hoc_Q Hxneg Hu1 Hdx Hdy HY' Hxn.
  assert (Hyy2 : (y * y = y' * y')%F) by (rewrite HY'; ring).
  pose proof (oncurve_x2_eq x y x' y' Hoc Hoc_Q Hyy2 Hu1) as Hx2.
  assert (Hxeq : x = x').
  { destruct (abs_pins_sign x x' Hx2 Hxneg) as [Hp _]. exact (Hp Hxn). }
  apply step1_reduction; [ exact Hdx | exact Hdy | ].
  left. rewrite HY', <- Hxeq. split.
  * ring.
  * rewrite HaQ in Hoc.
    transitivity (F.opp Fone*(x*x) + y*y)%F; [ ring | ].
    rewrite Hoc. ring.
Qed.

(* ===================== Setup field/ring identities (RC-15 factoring) =====================
   The pre-dispatch [main_inversion] setup proofs, extracted as standalone Qed lemmas so the
   monolithic Qed no longer re-checks their (let-coupled) field terms.  Each is invoked from
   [main_inversion] with [eq_refl] for the [set]-let definitions (convertible by construction). *)

(* The on-curve magnitude identity (was [Hcurve_id], 5 field calls). Ground in (x,y). *)
Lemma curve_id_lemma : forall (x y : Fp),
  (Curve25519.E.a * (x * x) + y * y = Fone + Curve25519.E.d * (x * x) * (y * y))%F ->
  ((Fone + x*x) * ((Fone + y) * (Fone - y)) = ((x*y) * (x*y)) * (Curve25519.E.a - Curve25519.E.d))%F.
Proof.
  intros x y Hoc. rewrite HaQ in Hoc |- *.
  assert (Hd : (Curve25519.E.d*(x*x)*(y*y))%F = (y*y - x*x - Fone)%F).
  { assert (Hr : (Curve25519.E.d*(x*x)*(y*y))%F
               = ((Fone + Curve25519.E.d*(x*x)*(y*y)) - Fone)%F) by field.
    rewrite Hr.
    assert (HQc : (y*y - x*x)%F = (Fone + Curve25519.E.d*(x*x)*(y*y))%F).
    { assert (Hr2 : (y*y - x*x)%F = (F.opp Fone*(x*x) + y*y)%F) by field.
      rewrite Hr2. exact Hoc. }
    rewrite <- HQc. field. }
  assert (Hr : ((Fone + x*x) * ((Fone + y)*(Fone - y)))%F = (Fone + x*x - y*y - x*x*(y*y))%F) by field.
  rewrite Hr.
  assert (Hr3 : (x*y*(x*y)*(F.opp Fone - Curve25519.E.d))%F
              = (F.opp (x*x*(y*y)) - Curve25519.E.d*(x*x)*(y*y))%F) by field.
  rewrite Hr3, Hd. field.
Qed.

(* The constant K2 (was a vm_compute assert inside main_inversion). *)
Lemma k2_fact :
  (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D * (Curve25519.E.a - Curve25519.E.d))%F = Fone.
Proof.
  unfold INVSQRT_A_MINUS_D, Curve25519.E.a, Curve25519.E.d;
  apply ModularArithmeticTheorems.F.eq_to_Z_iff; vm_compute; reflexivity.
Qed.

(* Branch-independent magnitude (was [Hmag]): den_inv^2 (1 - Yf^2) = M. *)
Lemma mag_lemma : forall (x y inv u1 u2 den_inv Yf Y0 M : Fp) (rot : bool),
  u1 = ((Fone + y) * (Fone - y))%F ->
  u2 = (x * y)%F ->
  M = (inv * u1 * (inv * u2) * u2)%F ->
  Y0 = (if rot then x * SQRT_M1 else y)%F ->
  den_inv = (if rot then inv * u1 * INVSQRT_A_MINUS_D else inv * u2)%F ->
  (Yf * Yf = Y0 * Y0)%F ->
  ((Fone + x*x) * u1 = (u2 * u2) * (Curve25519.E.a - Curve25519.E.d))%F ->
  (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D * (Curve25519.E.a - Curve25519.E.d))%F = Fone ->
  u1 <> Fzero ->
  (den_inv * den_inv * (Fone - Yf * Yf) = M)%F.
Proof.
  intros x y inv u1 u2 den_inv Yf Y0 M rot Hu1 Hu2 HM HY0 Hden HYf2 Hcid K2 Hu1nz0.
  rewrite HYf2, Hden, HY0.
  destruct rot.
  - assert (HY0s : ((x * SQRT_M1) * (x * SQRT_M1))%F = F.opp (x*x))
      by (assert (Hr : ((x * SQRT_M1) * (x * SQRT_M1))%F = ((SQRT_M1*SQRT_M1)*(x*x))%F) by field;
          rewrite Hr, Ristretto255_CaseScratch.SQRT_M1_sq; field).
    rewrite HY0s.
    apply (Ristretto255_Sqrt.mul_cancel_l u1 _ _ Hu1nz0).
    transitivity ((inv*u1*INVSQRT_A_MINUS_D)*(inv*u1*INVSQRT_A_MINUS_D) * ((Fone + x*x)*u1))%F;
      [ field | ].
    rewrite Hcid.
    transitivity ((inv*u1*(inv*u1)*(u2*u2)) * (INVSQRT_A_MINUS_D*INVSQRT_A_MINUS_D*(Curve25519.E.a-Curve25519.E.d)))%F;
      [ field | rewrite K2, HM; field ].
  - assert (HY0s : (y * y)%F = (Fone - u1)%F) by (rewrite Hu1; field).
    rewrite HY0s.
    assert (Hr : (Fone - (Fone - u1))%F = u1) by field. rewrite Hr.
    rewrite HM; field.
Qed.

(* Unified encoder inversion (was [Hstar]): s^2 (1+Yf) = M (1-Yf). *)
Lemma star_lemma : forall (s den_inv Yf M : Fp),
  (s * s = den_inv * (Fone - Yf) * (den_inv * (Fone - Yf)))%F ->
  (den_inv * den_inv * (Fone - Yf * Yf) = M)%F ->
  (s * s * (Fone + Yf) = M * (Fone - Yf))%F.
Proof.
  intros s den_inv Yf M Hs2 Hmag.
  rewrite Hs2.
  transitivity ((den_inv * den_inv * (Fone - Yf * Yf)) * (Fone - Yf))%F; [ field | ].
  rewrite Hmag. ring.
Qed.

(* Cancellation vs decoder relation (was [HMcancel]): M=1 -> Yf=y'. *)
Lemma mcancel_lemma : forall (s Yf y' M : Fp),
  (s * s * (Fone + Yf) = M * (Fone - Yf))%F ->
  (s * s * (Fone + y') = Fone - y')%F ->
  (Fone + s * s <> Fzero)%F ->
  M = Fone ->
  Yf = y'.
Proof.
  intros s Yf y' M Hstar Hs2y' Hu2nz HM1.
  rewrite HM1 in Hstar.
  apply (Ristretto255_Sqrt.mul_cancel_l (Fone + s*s) _ _ Hu2nz).
  transitivity (Fone - s*s)%F.
  - replace ((Fone + s*s)*Yf)%F with (Yf + (s*s*(Fone + Yf)) - s*s)%F by ring.
    rewrite Hstar. ring.
  - replace ((Fone + s*s)*y')%F with (y' + (s*s*(Fone + y')) - s*s)%F by ring.
    rewrite Hs2y'. ring.
Qed.

(* ===================== M=Fone dispatch (RC-15 structural factoring) =====================
   The four-way (rot x flip) dispatch of [main_inversion]'s M=Fone branch, extracted with the
   encoder lets [M Xsel Y0 Yf rot flip] as EXPLICIT PARAMETERS (+ their defining equations as
   hyps).  In [main_inversion] those are [set (… ) in *] lets, so [destruct rot/flip] there
   generalized the whole let-dependency-closure into the match motive -> the kernel-Qed blew up
   (~46 min / OOM).  Here rot/flip are bare booleans: [destruct] only case-splits the (let-free)
   goal, so the motive is trivial and BOTH this Qed and main_inversion's are fast.  Each branch
   reduces the [if] equations ([cbv iota]), recovers [HY']/sign, and applies the matching leaf. *)
Lemma dispatch_Mfone : forall (x y x' y' M Xsel Y0 Yf : Fp) (rot flip : bool),
  M = Fone ->
  Xsel = (if rot then y * SQRT_M1 else x)%F ->
  Y0 = (if rot then x * SQRT_M1 else y)%F ->
  flip = is_negative (Xsel * M) ->
  Yf = (if flip then F.opp Y0 else Y0)%F ->
  Yf = y' ->
  (Curve25519.E.a * (x * x) + y * y = Fone + Curve25519.E.d * (x * x) * (y * y))%F ->
  (Curve25519.E.a * (x' * x') + y' * y' = Fone + Curve25519.E.d * (x' * x') * (y' * y'))%F ->
  is_negative x' = false ->
  x <> Fzero -> y <> Fzero -> SQRT_M1 <> Fzero ->
  ((Fone + y) * (Fone - y))%F <> Fzero ->
  (Fone + Curve25519.E.d * x * F.opp x' * y * y') <> Fzero ->
  (Fone - Curve25519.E.d * x * F.opp x' * y * y') <> Fzero ->
  is_4torsion_affine (sub_affine (x, y) (x', y')).
Proof.
  intros x y x' y' M Xsel Y0 Yf rot flip HM1 HXsel HY0 Hflip HYf HYfy'
         Hoc Hoc_Q Hxneg Hxnz Hynz0 HSnz Hu1 Hdx Hdy.
  destruct rot; destruct flip; cbv iota in HXsel, HY0, HYf.
  - (* rot=true, flip=true : y' = -(x*SQRT_M1) ; system (iii) *)
    assert (HY' : y' = F.opp (x * SQRT_M1)%F) by (rewrite <- HYfy', HYf, HY0; reflexivity).
    assert (Hsneg : is_negative (SQRT_M1 * y) = true).
    { rewrite HXsel, HM1 in Hflip.
      replace (y * SQRT_M1 * Fone)%F with (SQRT_M1 * y)%F in Hflip by ring.
      symmetry; exact Hflip. }
    exact (leaf_inv_tt x y x' y' Hoc Hoc_Q Hxneg Hxnz Hynz0 HSnz Hdx Hdy HY' Hsneg).
  - (* rot=true, flip=false : y' = x*SQRT_M1 ; system (iv) *)
    assert (HY' : y' = (x * SQRT_M1)%F) by (rewrite <- HYfy', HYf, HY0; reflexivity).
    assert (Hsneg : is_negative (SQRT_M1 * y) = false).
    { rewrite HXsel, HM1 in Hflip.
      replace (y * SQRT_M1 * Fone)%F with (SQRT_M1 * y)%F in Hflip by ring.
      symmetry; exact Hflip. }
    exact (leaf_inv_tf x y x' y' Hoc Hoc_Q Hxneg Hxnz Hdx Hdy HY' Hsneg).
  - (* rot=false, flip=true : y' = -y ; system (ii) *)
    assert (HY' : y' = F.opp y) by (rewrite <- HYfy', HYf, HY0; reflexivity).
    assert (Hxn : is_negative x = true).
    { rewrite HXsel, HM1 in Hflip.
      replace (x * Fone)%F with x in Hflip by ring. symmetry; exact Hflip. }
    exact (leaf_inv_ft x y x' y' Hoc Hoc_Q Hxneg Hu1 Hdx Hdy HY' Hxn).
  - (* rot=false, flip=false : y' = y ; system (i) *)
    assert (HY' : y' = y) by (rewrite <- HYfy', HYf, HY0; reflexivity).
    assert (Hxn : is_negative x = false).
    { rewrite HXsel, HM1 in Hflip.
      replace (x * Fone)%F with x in Hflip by ring. symmetry; exact Hflip. }
    exact (leaf_inv_ff x y x' y' Hoc Hoc_Q Hxneg Hu1 Hdx Hdy HY' Hxn).
Qed.

Lemma main_inversion : forall (x y x' y' : Fp),
  (Curve25519.E.a * (x * x) + y * y = Fone + Curve25519.E.d * (x * x) * (y * y))%F ->
  (Curve25519.E.a * (x' * x') + y' * y' = Fone + Curve25519.E.d * (x' * x') * (y' * y'))%F ->
  ((Fone + y) * (Fone - y) * (x * y * (x * y)))%F <> Fzero ->
  (ristretto_encode_aux x y Fone (x*y) * ristretto_encode_aux x y Fone (x*y) * (Fone + y')
     = Fone - y')%F ->
  (Fone + ristretto_encode_aux x y Fone (x*y) * ristretto_encode_aux x y Fone (x*y) <> Fzero)%F ->
  is_negative x' = false ->
  is_negative (ristretto_encode_aux x y Fone (x*y)) = false ->
  y' <> Fzero ->
  fst (sqrt_ratio_m1 Fone ((Fone + y) * (Fone - y) * (x * y * (x * y)))) = true ->
  is_4torsion_affine (sub_affine (x, y) (x', y')).
Proof.
  intros x y x' y' Hoc Hoc_Q Hargnz Hs2y' Hu2nz Hxneg Hnegs Hynz Hvalid.
  set (u1 := ((Fone + y) * (Fone - y))%F) in *.
  set (u2 := (x * y)%F) in *.
  assert (Hu2nz0 : u2 <> Fzero) by (intro Hk; apply Hargnz; unfold u1, u2 in *; rewrite Hk; field).
  assert (Hu1nz0 : u1 <> Fzero) by (intro Hk; apply Hargnz; unfold u1, u2 in *; rewrite Hk; field).
  revert Hs2y' Hu2nz Hnegs.
  unfold ristretto_encode_aux. fold u1 u2.
  pose proof (Ristretto255_Sqrt.sqrt_ratio_m1_correct Fone _ Hargnz) as Hsr.
  fold u1 u2 in Hsr.
  destruct (sqrt_ratio_m1 Fone (u1 * (u2 * u2))) as [ws inv] eqn:Esr.
  destruct Hsr as [Hsrcase Hinvneg].
  intros Hs2y' Hu2nz Hnegs.
  simpl in Hvalid.
  set (M := (inv * u1 * (inv * u2) * u2)%F) in *.
  (* Validity (ws=true) forces M=Fone directly: the M=SQRT_M1 (ws=false) disjunct of the
     sqrt invariant is excluded by Hvalid.  This removes the [destruct HMval] + vacuity from
     the tail, leaving a single [exact (dispatch_Mfone …)] -> main_inversion's Qed is fast. *)
  assert (HMfone : M = Fone).
  { destruct Hsrcase as [[_ Hsq] | [Hwsf _]].
    - transitivity (u1 * (u2 * u2) * inv * inv)%F; [ unfold M; field | exact Hsq ].
    - rewrite Hvalid in Hwsf; discriminate. }
  set (rot := is_negative (u2 * M)) in *.
  set (Xsel := (if rot then y * SQRT_M1 else x)%F) in *.
  set (Y0 := (if rot then x * SQRT_M1 else y)%F) in *.
  set (den_inv := (if rot then inv * u1 * INVSQRT_A_MINUS_D else inv * u2)%F) in *.
  set (flip := is_negative (Xsel * M)) in *.
  set (Yf := (if flip then F.opp Y0 else Y0)%F) in *.
  set (s := abs (den_inv * (Fone - Yf))) in *.
  assert (Hs2 : (s * s = den_inv * (Fone - Yf) * (den_inv * (Fone - Yf)))%F)
    by (unfold s; apply Ristretto255_Sqrt.abs_sq).
  assert (HYf2 : (Yf * Yf = Y0 * Y0)%F) by (unfold Yf; destruct flip; [ field | reflexivity ]).
  pose proof k2_fact as K2.
  assert (Hcurve_id : ((Fone + x*x) * u1 = (u2 * u2) * (Curve25519.E.a - Curve25519.E.d))%F)
    by exact (curve_id_lemma x y Hoc).
  assert (Hmag : (den_inv * den_inv * (Fone - Yf * Yf) = M)%F)
    by exact (mag_lemma x y inv u1 u2 den_inv Yf Y0 M rot
                eq_refl eq_refl eq_refl eq_refl eq_refl HYf2 Hcurve_id K2 Hu1nz0).
  assert (Hstar : (s * s * (Fone + Yf) = M * (Fone - Yf))%F)
    by exact (star_lemma s den_inv Yf M Hs2 Hmag).
  assert (HMcancel : (M = Fone -> Yf = y')%F)
    by (intro HM1; exact (mcancel_lemma s Yf y' M Hstar Hs2y' Hu2nz HM1)).
  (* VERIFIED CORE (all the above machine-checked, 0 axioms):
       [Hstar] s^2*(1+Yf)=M*(1-Yf) (encoder inversion); [Hmag] den_inv^2*(1-Yf^2)=M
       (magnitude, from [Hcurve_id]+[K2]); [HMfone] M=Fone (validity forces it);
       [HMcancel] M=Fone -> Yf=y'.  All eight M x rot x flip leaves are discharged by the
       four standalone [leaf_inv_*] lemmas via [dispatch_Mfone]; the ws=false / M=SQRT_M1
       case is excluded by [Hvalid] (round-trip is genuinely false there — see
       writeup/RISTRETTO_ROUNDTRIP_FIX_PLAN.md).  The dispatch is factored out (lets as
       explicit params) so [destruct rot/flip] stays cheap — see reference_slow_proofs_fiat
       RC-19 (main_inversion Qed 46 min -> 5s). *)
  assert (Hxnz : x <> Fzero) by (intro Hk; apply Hu2nz0; unfold u2; rewrite Hk; ring).
  assert (Hynz0 : y <> Fzero) by (intro Hk; apply Hu2nz0; unfold u2; rewrite Hk; ring).
  assert (HoQ' : (Curve25519.E.a * (F.opp x' * F.opp x') + y' * y'
                  = Fone + Curve25519.E.d * (F.opp x' * F.opp x') * (y' * y'))%F)
    by (replace (F.opp x' * F.opp x')%F with (x' * x')%F by ring; exact Hoc_Q).
  pose proof (denomx_nz x y (F.opp x') y' Hoc HoQ') as Hdx.
  pose proof (denomy_nz x y (F.opp x') y' Hoc HoQ') as Hdy.
  assert (HSnz : SQRT_M1 <> Fzero) by (apply Ristretto255_Sqrt.SQRT_M1_nz).
  (* M = Fone (HMfone, from validity) -> delegate to dispatch_Mfone, whose lets-as-params
     keep destruct rot/flip cheap.  No [destruct HMval]/vacuity: the ws=false (M=SQRT_M1)
     case is already excluded by Hvalid (the round-trip is genuinely FALSE for ws=false
     on-curve points — Coq-verified counterexample y=10; see RISTRETTO_ROUNDTRIP_FIX_PLAN.md). *)
  exact (dispatch_Mfone x y x' y' M Xsel Y0 Yf rot flip HMfone
           eq_refl eq_refl eq_refl eq_refl (HMcancel HMfone)
           Hoc Hoc_Q Hxneg Hxnz Hynz0 HSnz Hu1nz0 Hdx Hdy).
Qed.

Lemma encode_decode_equiv' : forall (x y x' y' : Fp),
  (Curve25519.E.a * (x * x) + y * y = Fone + Curve25519.E.d * (x * x) * (y * y))%F ->
  ristretto_decode_coords (ristretto_encode_bytes (to_extended (x, y))) = Some (x', y') ->
  fst (sqrt_ratio_m1 Fone ((Fone + y) * (Fone - y) * (x * y * (x * y)))) = true ->
  is_4torsion_affine (sub_affine (x, y) (x', y')).
Proof.
  intros x y x' y' Hoc Hdec Hvalid.
  pose proof (encode_decode_same_s (x, y) (x', y') Hdec) as Hsame.
  set (s := ristretto_encode (to_extended (x, y))) in *.
  unfold ristretto_encode_bytes, ristretto_encode_bytes_of_F in Hdec.
  fold s in Hdec.
  pose proof (decoded_self_characterization s x' y' Hdec) as Hchar.
  cbv zeta in Hchar.
  destruct Hchar as (Hnegs & Hynz & Hu2nz & Hvnz & Hyvu2 & Hxv2v & Hxneg & Hoc_Q).
  assert (Hs2y' : (s * s * (Fone + y') = Fone - y')%F).
  { assert (Hexp : (s*s*y' = Fone - s*s - y')%F).
    { assert (Hr : (y' * (Fone + s*s))%F = (y' + s*s*y')%F) by ring.
      rewrite Hr in Hyvu2.
      apply Ristretto255_Sqrt.sub_eq_zero. rewrite <- Hyvu2 at 1. ring. }
    transitivity (s*s + (s*s*y'))%F; [ ring | rewrite Hexp; ring ]. }
  assert (Hsval : s = ristretto_encode_aux x y Fone (x*y)) by reflexivity.
  destruct (F.eq_dec ((Fone + y) * (Fone - y) * (x * y * (x * y))) Fzero) as [Harg0 | Hargnz].
  - (* DEGENERATE: s = 0, decoder pins (x',y')=(0,1), sub_affine = (x,y) in E[4]. *)
    assert (Hs0 : s = Fzero) by (rewrite Hsval; apply enc_arg0_s0; exact Harg0).
    assert (Hy'1 : y' = Fone).
    { apply (Ristretto255_Sqrt.mul_cancel_l (Fone + s*s) _ _ Hu2nz).
      transitivity (Fone - s*s)%F; [ | rewrite Hs0; field ]. rewrite <- Hyvu2. ring. }
    assert (Hx'0 : x' = Fzero).
    { assert (Hxx0 : (x' * x')%F = Fzero).
      { apply (Ristretto255_Sqrt.mul_cancel_l
          (F.opp (E.d * ((Fone - s * s) * (Fone - s * s))) - (Fone + s * s) * (Fone + s * s)) _ _ Hvnz).
        transitivity (F.of_Z p 4 * (s * s))%F.
        - transitivity (x' * x' * (F.opp (E.d * ((Fone - s * s) * (Fone - s * s))) -
            (Fone + s * s) * (Fone + s * s)))%F; [ ring | exact Hxv2v ].
        - rewrite Hs0. field. }
      apply Ristretto255_Sqrt.mul_zero_factor in Hxx0; destruct Hxx0; assumption. }
    subst x' y'. rewrite sub_affine_id_01. apply (deg_oncurve_torsion x y Hoc Harg0).
  - (* MAIN: sqrt argument nonzero. *)
    rewrite Hsval in Hs2y', Hu2nz, Hnegs.
    apply (main_inversion x y x' y' Hoc Hoc_Q Hargnz Hs2y' Hu2nz Hxneg Hnegs Hynz Hvalid).
Qed.

(** Theorem 1 (encode->decode round-trip), conditional form, PROVED here (0 axioms) via
    [encode_decode_equiv'].  Same statement as
    [Ristretto255_RoundTrip.ristretto_encode_decode_roundtrip] (corrected with the validity
    hypothesis), discharged at this level where [main_inversion] is available — RoundTrip
    keeps it [Admitted] only because it cannot import this file (circular). *)
Theorem ristretto_encode_decode_roundtrip_valid :
  forall (oc : OnCurveObligation) (P Q : Curve25519.E.point),
    ristretto_decode_bytes oc
      (ristretto_encode_bytes (to_extended (point_coords P))) = Some Q ->
    (let '(x, y) := point_coords P in
       fst (sqrt_ratio_m1 Fone ((Fone + y) * (Fone - y) * (x * y * (x * y)))) = true) ->
    ristretto_equiv P Q.
Proof.
  intros oc P Q Hdec Hvalid.
  pose proof (decode_bytes_coords oc _ Q Hdec) as HQc.
  unfold ristretto_equiv.
  destruct P as [[x y] HocP].
  destruct Q as [[x' y'] HocQ].
  cbn [point_coords proj1_sig] in HQc, Hvalid |- *.
  cbv iota in Hvalid.
  exact (encode_decode_equiv' x y x' y' HocP HQc Hvalid).
Qed.

(** ===================== Existential round-trip (Phases 0/A/B/C, 2026-05-25) =====================
    [valid_ristretto_input P] = the encoder's sqrt branch succeeds — the TRUE domain of the
    round-trip (the y=10 counterexample shows on-curve alone is insufficient). *)
Definition valid_ristretto_input (P : Curve25519.E.point) : Prop :=
  let '(x, y) := point_coords P in
    fst (sqrt_ratio_m1 Fone ((Fone + y) * (Fone - y) * (x * y * (x * y)))) = true.

(** (B) DECODE-SUCCESS — a valid input's encoding decodes successfully.  TRUE (the encoder
    produces a decodable [s] for valid points), but the proof is the CONVERSE of
    [Ristretto255_JacobiQuartic.decoder_on_jq] (the decoder's [was_square] guard, Decode.v:147,
    passes) plus the [is_negative t = false] / [y <> 0] sign conditions — no existing helper.

    B-α (degenerate case, Qed): if [arg = 0] then [s = 0] and the decoder pins
    [(0,1)] via [decoder_zero_returns_identity].

    B-β (non-degenerate case, named axiom residual): for [arg ≠ 0] the encoder
    [s_leaf] is one of 4 closed forms (per [encoder_on_jq_core_{nonrot, nonrot_flip,
    rot, rot_flip}]) and the encoder's rotate/flip selection (per [encoder_z_inv_eq_one]
    giving [z_inv = 1]) guarantees [is_negative (x_dec · y_dec) = false] and [y_dec ≠ 0]
    at the decoder.  Mechanical per-leaf sign analysis; deferred. *)

(** B-α: degenerate case fully closed (Qed, 0 axioms). *)
Lemma decode_encode_success_degenerate :
  forall (oc : OnCurveObligation) (x y : Fp),
    ((Fone + y) * (Fone - y) * (x * y * (x * y)))%F = Fzero ->
    exists Q, ristretto_decode_bytes oc
                (ristretto_encode_bytes (to_extended (x, y))) = Some Q.
Proof.
  intros oc x y Harg0.
  unfold ristretto_encode_bytes, ristretto_encode_bytes_of_F,
         ristretto_encode, to_extended.
  assert (Hs0 : ristretto_encode_aux x y Fone (x * y) = Fzero)
    by (apply enc_arg0_s0; exact Harg0).
  rewrite Hs0.
  replace (F.to_Z (Fzero : Fp)) with 0%Z by reflexivity.
  apply (decode_bytes_some_of_coords oc _ Fzero Fone).
  exact Ristretto255_JacobiQuartic.decoder_zero_returns_identity.
Qed.

(** B-β: non-degenerate case.  Per the plan, this is the 4-leaf sign analysis.
    We discharge the [decode_encode_success_nondegenerate] cluster axiom into:

    (i)   structural reduction (Qed): [decode_coords_succeeds_from_inv]
          — given [is_negative s = false], the [was_square = true] branch of
          [sqrt_ratio_m1] at [jq_v(s)·(1+s²)²], plus [is_negative(t)=false]
          and [y_dec≠0], the decoder returns [Some (x_dec, y_dec)].
    (ii)  [is_negative s = false] for encoder output (Qed via [encoder_is_negative_false]).
    (iii) [was_square = true] for the decoder's [den] (Qed via JQ.encoder_decoder_was_square,
          modulo [den ≠ 0]).
    (iv)  [den ≠ 0], [is_negative t = false], [y_dec ≠ 0] — the three residual sign
          obligations.  Each requires its own per-leaf algebraic argument; they are
          isolated as smaller, named axioms below so downstream consumers can see
          precisely which leaf-level facts are missing.

    The single big [decode_encode_success_nondegenerate] axiom is then proved as
    a [Lemma] (Qed) by composing (i)–(iv).  Net effect: the gap is now three named
    sub-axioms, each strictly smaller than the original. *)

(** Encoder output is non-negative (drops out of the [abs] at the end). *)
Lemma encoder_is_negative_false : forall (x y : Fp),
  is_negative (ristretto_encode_aux x y Fone (x * y)) = false.
Proof.
  intros x y. unfold ristretto_encode_aux.
  destruct (sqrt_ratio_m1 Fone _) as [ws invsqrt] eqn:Esr.
  destruct (is_negative (_ * _)); destruct (is_negative (_ * _));
    apply Ristretto255_Sqrt.is_negative_abs.
Qed.

(** Bridge: the decoder's literal [sqrt_ratio_m1] argument equals [jq_v(s)·(1+s²)²]. *)
Lemma decoder_sr_eq : forall s,
  ((F.opp (Curve25519.E.d * ((Fone - s * s) * (Fone - s * s))) -
    (Fone + s * s) * (Fone + s * s)) *
   ((Fone + s * s) * (Fone + s * s)))%F =
  (Ristretto255_JacobiQuartic.jq_v s * ((Fone + s*s) * (Fone + s*s)))%F.
Proof. intros. unfold Ristretto255_JacobiQuartic.jq_v. reflexivity. Qed.

(** B-β structural reduction (Qed, 0 axioms): given [is_negative s = false],
    a [was_square=true] inverse-square-root, and the two sign predicates, the
    decoder succeeds with coords [(x_dec, y_dec)].  This factors B-β into the
    three per-leaf sign obligations below. *)
Lemma decode_coords_succeeds_from_inv : forall (s : Fp),
  is_negative s = false ->
  forall (iv : Fp),
    sqrt_ratio_m1 Fone
      (Ristretto255_JacobiQuartic.jq_v s * ((Fone + s*s) * (Fone + s*s)))
      = (true, iv) ->
    let x_dec := abs (F.of_Z _ 2 * s * (iv * (Fone + s*s))) in
    let y_dec := ((Fone - s*s) *
                  (iv * (iv * (Fone + s*s)) *
                   Ristretto255_JacobiQuartic.jq_v s))%F in
    is_negative (x_dec * y_dec) = false ->
    y_dec <> Fzero ->
    ristretto_decode_coords (le_split 32 (F.to_Z s)) = Some (x_dec, y_dec).
Proof.
  intros s Hneg_s iv Hsr. cbv zeta.
  unfold ristretto_decode_coords.
  rewrite Ristretto255_RoundTrip.le_split_F_round_trip.
  rewrite Hneg_s.
  intros Hnegt Hynz.
  rewrite decoder_sr_eq.
  rewrite Hsr.
  cbn [negb].
  rewrite orb_false_l.
  unfold Ristretto255_JacobiQuartic.jq_v in Hnegt.
  rewrite Hnegt.
  rewrite orb_false_l.
  destruct (F.to_Z _ =? 0)%Z eqn:Hyz.
  - exfalso. apply Hynz.
    apply ModularArithmeticTheorems.F.eq_to_Z_iff.
    unfold Ristretto255_JacobiQuartic.jq_v.
    apply Z.eqb_eq in Hyz. rewrite Hyz. reflexivity.
  - reflexivity.
Qed.

(** ===== Three residual per-leaf sign facts =====

    Two of three are now closed as Qed lemmas (was: Axiom each).  The remaining
    one ([encoder_decoder_neg_t], the deepest sign predicate) is kept as an
    Axiom pending a per-leaf [is_negative] analysis.

    Reduction strategy (used for both closed ones):
    - [encoder_on_jq] (existing, Qed in JQ.v) gives [on_jq s X] for the
      encoder output [s] and [X ∈ {x, y·SQRT_M1}].
    - [on_jq s X] = [X² · jq_v(s) = 4·s²].  Specialising at [s² = 1] gives
      [X² = -1]; at [s = 0] gives [X = 0]; at [(1+s²) = 0] gives [d · X² = 1].
    - The two on-curve hypotheses + [arg ≠ 0] each refute the conclusion at
      both [X = x] and [X = y·SQRT_M1].  Uniform, no per-leaf casework. *)

(** Algebraic kernel: [on_jq s X] forces [X² = -1] when [s² = 1]. *)
Lemma s_sq_one_X_sq_m1 : forall (s X : Fp),
  Ristretto255_JacobiQuartic.on_jq s X ->
  (s * s)%F = Fone ->
  (X * X)%F = F.opp Fone.
Proof.
  intros s X Honj Hs2.
  unfold Ristretto255_JacobiQuartic.on_jq, Ristretto255_JacobiQuartic.jq_v in Honj.
  rewrite Hs2 in Honj.
  assert (H4nz : (F.of_Z (2^255-19) 4 : Fp) <> Fzero) by apply Ristretto255_JacobiQuartic.four_nz.
  apply (Ristretto255_Sqrt.mul_cancel_l (F.of_Z (2^255-19) 4) _ _ H4nz).
  transitivity (F.opp (X * X * (F.opp (Curve25519.E.d * ((Fone - Fone) * (Fone - Fone))) - (Fone + Fone) * (Fone + Fone))))%F.
  - ring.
  - rewrite Honj. ring.
Qed.

(** Refute [x² = -1] under on-curve + y ≠ 0. *)
Lemma x_sq_not_m1 : forall (x y : Fp),
  (Curve25519.E.a * (x * x) + y * y =
     Fone + Curve25519.E.d * (x * x) * (y * y))%F ->
  y <> Fzero ->
  (x * x)%F <> F.opp Fone.
Proof.
  intros x y Hoc Hynz Hx2.
  rewrite HaQ in Hoc. rewrite Hx2 in Hoc.
  assert (Hy2_dp1 : (y * y * (Curve25519.E.d + Fone))%F = Fzero).
  { assert (Hsub : (F.opp Fone * F.opp Fone + y * y - (Fone + Curve25519.E.d * F.opp Fone * (y * y)) = Fzero)%F).
    { rewrite Hoc. ring. }
    transitivity (F.opp Fone * F.opp Fone + y * y - (Fone + Curve25519.E.d * F.opp Fone * (y * y)))%F.
    - ring.
    - exact Hsub. }
  apply Ristretto255_Sqrt.mul_zero_factor in Hy2_dp1.
  destruct Hy2_dp1 as [Hy2 | Hdp1].
  - apply Ristretto255_Sqrt.mul_zero_factor in Hy2.
    destruct Hy2 as [Hy | Hy]; apply Hynz; exact Hy.
  - exact (Ristretto255_JacobiQuartic.dp1_nz Hdp1).
Qed.

(** Refute [(y·SQRT_M1)² = -1] under arg ≠ 0. *)
Lemma ySQ_sq_not_m1 : forall (x y : Fp),
  ((Fone + y) * (Fone - y) * (x * y * (x * y)))%F <> Fzero ->
  (y * SQRT_M1 * (y * SQRT_M1))%F <> F.opp Fone.
Proof.
  intros x y Harg Hsq.
  assert (HSqi : (SQRT_M1 * SQRT_M1)%F = F.opp Fone) by exact Ristretto255_CaseScratch.SQRT_M1_sq.
  assert (Hy2_eq_one : (y * y)%F = Fone).
  { transitivity (F.opp (y * SQRT_M1 * (y * SQRT_M1)))%F.
    - transitivity (F.opp (y * y * (SQRT_M1 * SQRT_M1)))%F.
      + rewrite HSqi. ring.
      + f_equal. ring.
    - rewrite Hsq. ring. }
  apply Harg.
  assert (H1my2 : ((Fone + y) * (Fone - y))%F = Fzero).
  { transitivity (Fone - y * y)%F.
    - ring.
    - rewrite Hy2_eq_one. ring. }
  transitivity (Fzero * (x * y * (x * y)))%F.
  - rewrite <- H1my2. ring.
  - ring.
Qed.

(** Encoder output [s] satisfies [s² ≠ 1]. *)
Lemma encoder_s_sq_ne_one : forall (x y : Fp),
  (Curve25519.E.a * (x * x) + y * y =
     Fone + Curve25519.E.d * (x * x) * (y * y))%F ->
  ((Fone + y) * (Fone - y) * (x * y * (x * y)))%F <> Fzero ->
  fst (sqrt_ratio_m1 Fone ((Fone + y) * (Fone - y) * (x * y * (x * y)))) = true ->
  let s := ristretto_encode_aux x y Fone (x * y) in
  (s * s)%F <> Fone.
Proof.
  intros x y Hoc Harg Hws s Hs2.
  assert (Hy : y <> Fzero) by (intro H; apply Harg; rewrite H; ring).
  destruct (Ristretto255_JacobiQuartic.encoder_on_jq x y Hoc Harg Hws) as [Honj|Honj];
    fold s in Honj.
  - pose proof (s_sq_one_X_sq_m1 _ _ Honj Hs2) as Hx2.
    exact (x_sq_not_m1 _ _ Hoc Hy Hx2).
  - pose proof (s_sq_one_X_sq_m1 _ _ Honj Hs2) as Hysq.
    exact (ySQ_sq_not_m1 _ _ Harg Hysq).
Qed.

(** [sqrt_ratio_m1 Fone Fzero = (false, _)]: enables a clean inversion-extraction. *)
Lemma sqrt_ratio_m1_zero_false :
  fst (sqrt_ratio_m1 Fone Fzero) = false.
Proof. vm_compute. reflexivity. Qed.

(** From [sqrt_ratio_m1 Fone v = (true, iv)], extract the invariant [v · iv² = 1]. *)
Lemma sqrt_ratio_m1_true_inv : forall (v iv : Fp),
  sqrt_ratio_m1 Fone v = (true, iv) ->
  (v * iv * iv = Fone)%F /\ v <> Fzero.
Proof.
  intros v iv Hsr.
  destruct (F.eq_dec v Fzero) as [Hz|Hnz].
  - exfalso. subst v. pose proof sqrt_ratio_m1_zero_false as Hf.
    rewrite Hsr in Hf. simpl in Hf. discriminate.
  - split; [|exact Hnz].
    pose proof (sqrt_ratio_m1_correct Fone v Hnz) as Hc.
    rewrite Hsr in Hc.
    destruct Hc as [Hdisj _].
    destruct Hdisj as [[_ Heq]|[Hf _]].
    + exact Heq.
    + discriminate.
Qed.

(** From [on_jq s X] + [s = 0], derive [X = 0] (since [jq_v(0) = -(d+1) ≠ 0]). *)
Lemma s_zero_X_zero : forall (s X : Fp),
  Ristretto255_JacobiQuartic.on_jq s X ->
  s = Fzero ->
  X = Fzero.
Proof.
  intros s X Honj Hs. subst s.
  unfold Ristretto255_JacobiQuartic.on_jq, Ristretto255_JacobiQuartic.jq_v in Honj.
  assert (Hp_simp : (F.opp (Curve25519.E.d * ((Fone - Fzero * Fzero) * (Fone - Fzero * Fzero))) - (Fone + Fzero * Fzero) * (Fone + Fzero * Fzero) = F.opp (Curve25519.E.d + Fone))%F) by ring.
  rewrite Hp_simp in Honj.
  assert (Hrhs : (F.of_Z (2^255-19) 4 * (Fzero * Fzero))%F = Fzero) by ring.
  rewrite Hrhs in Honj.
  apply Ristretto255_Sqrt.mul_zero_factor in Honj.
  destruct Honj as [HX2 | Hdp1].
  - apply Ristretto255_Sqrt.mul_zero_factor in HX2.
    destruct HX2; assumption.
  - exfalso. apply (Ristretto255_JacobiQuartic.dp1_nz).
    transitivity (F.opp (F.opp (Curve25519.E.d + Fone)))%F.
    + ring.
    + rewrite Hdp1. ring.
Qed.

(** Encoder output [s] is nonzero. *)
Lemma encoder_s_ne_zero : forall (x y : Fp),
  (Curve25519.E.a * (x * x) + y * y =
     Fone + Curve25519.E.d * (x * x) * (y * y))%F ->
  ((Fone + y) * (Fone - y) * (x * y * (x * y)))%F <> Fzero ->
  fst (sqrt_ratio_m1 Fone ((Fone + y) * (Fone - y) * (x * y * (x * y)))) = true ->
  let s := ristretto_encode_aux x y Fone (x * y) in
  s <> Fzero.
Proof.
  intros x y Hoc Harg Hws s Hs.
  assert (Hx : x <> Fzero) by (intro H; apply Harg; rewrite H; ring).
  assert (Hy : y <> Fzero) by (intro H; apply Harg; rewrite H; ring).
  destruct (Ristretto255_JacobiQuartic.encoder_on_jq x y Hoc Harg Hws) as [Honj|Honj];
    fold s in Honj.
  - pose proof (s_zero_X_zero _ _ Honj Hs) as Hxz.
    exact (Hx Hxz).
  - pose proof (s_zero_X_zero _ _ Honj Hs) as Hyz.
    apply Ristretto255_Sqrt.mul_zero_factor in Hyz.
    destruct Hyz as [Hy0 | HS0].
    + exact (Hy Hy0).
    + exact (Ristretto255_Sqrt.SQRT_M1_nz HS0).
Qed.

(** From [on_jq s X] + [(1+s²) = 0], derive [d · X² = 1]. *)
Lemma one_plus_s_sq_zero_d_X_sq_one : forall (s X : Fp),
  Ristretto255_JacobiQuartic.on_jq s X ->
  (Fone + s * s)%F = Fzero ->
  (Curve25519.E.d * (X * X))%F = Fone.
Proof.
  intros s X Honj H1ps.
  unfold Ristretto255_JacobiQuartic.on_jq, Ristretto255_JacobiQuartic.jq_v in Honj.
  assert (Hs2 : (s * s)%F = F.opp Fone).
  { transitivity (Fone + s * s - Fone)%F.
    - ring.
    - rewrite H1ps. ring. }
  rewrite Hs2 in Honj.
  assert (H4nz : (F.of_Z (2^255-19) 4 : Fp) <> Fzero) by apply Ristretto255_JacobiQuartic.four_nz.
  apply (Ristretto255_Sqrt.mul_cancel_l (F.of_Z (2^255-19) 4) _ _ H4nz).
  transitivity (F.opp (X * X * (F.opp (Curve25519.E.d * ((Fone - F.opp Fone) * (Fone - F.opp Fone))) - (Fone + F.opp Fone) * (Fone + F.opp Fone))))%F.
  - ring.
  - rewrite Honj. ring.
Qed.

(** Refute [d·x² = 1] under on-curve (forces [d = -1], contradicting [d+1 ≠ 0]). *)
Lemma d_x_sq_one_contra : forall (x y : Fp),
  (Curve25519.E.a * (x * x) + y * y =
     Fone + Curve25519.E.d * (x * x) * (y * y))%F ->
  (Curve25519.E.d * (x * x))%F <> Fone.
Proof.
  intros x y Hoc Hdxsq.
  rewrite HaQ in Hoc.
  apply Ristretto255_JacobiQuartic.dp1_nz.
  assert (Heq : (F.opp Fone - Curve25519.E.d = Fzero)%F).
  { transitivity (Curve25519.E.d * (F.opp Fone * (x * x) + y * y) - Curve25519.E.d * (Fone + Curve25519.E.d * (x * x) * (y * y)))%F.
    - replace (Curve25519.E.d * (F.opp Fone * (x * x) + y * y))%F with
              (F.opp (Curve25519.E.d * (x * x)) + Curve25519.E.d * (y * y))%F by ring.
      replace (Curve25519.E.d * (Fone + Curve25519.E.d * (x * x) * (y * y)))%F with
              (Curve25519.E.d + Curve25519.E.d * (Curve25519.E.d * (x * x)) * (y * y))%F by ring.
      rewrite Hdxsq. ring.
    - rewrite Hoc. ring. }
  transitivity (F.opp (F.opp Fone - Curve25519.E.d))%F.
  - ring.
  - rewrite Heq. ring.
Qed.

(** Refute [d·(y·SQRT_M1)² = 1] under on-curve + arg ≠ 0 (forces [y² = 1]). *)
Lemma d_ySQ_sq_one_contra : forall (x y : Fp),
  (Curve25519.E.a * (x * x) + y * y =
     Fone + Curve25519.E.d * (x * x) * (y * y))%F ->
  ((Fone + y) * (Fone - y) * (x * y * (x * y)))%F <> Fzero ->
  (Curve25519.E.d * (y * SQRT_M1 * (y * SQRT_M1)))%F <> Fone.
Proof.
  intros x y Hoc Harg Hdysq.
  assert (HSqi : (SQRT_M1 * SQRT_M1)%F = F.opp Fone) by exact Ristretto255_CaseScratch.SQRT_M1_sq.
  assert (Hdysq2 : (Curve25519.E.d * (y * y))%F = F.opp Fone).
  { transitivity (F.opp (Curve25519.E.d * (y * SQRT_M1 * (y * SQRT_M1))))%F.
    - transitivity (F.opp (Curve25519.E.d * (y * y) * (SQRT_M1 * SQRT_M1)))%F.
      + rewrite HSqi. ring.
      + f_equal. ring.
    - rewrite Hdysq. ring. }
  rewrite HaQ in Hoc.
  assert (Hy2_one : (y * y)%F = Fone).
  { transitivity (F.opp Fone * (x * x) + y * y + x * x)%F.
    - ring.
    - rewrite Hoc.
      transitivity (Fone + (Curve25519.E.d * (y * y)) * (x * x) + (x * x))%F.
      + ring.
      + rewrite Hdysq2. ring. }
  apply Harg.
  assert (H1my2 : ((Fone + y) * (Fone - y))%F = Fzero).
  { transitivity (Fone - y * y)%F.
    - ring.
    - rewrite Hy2_one. ring. }
  transitivity (Fzero * (x * y * (x * y)))%F.
  - rewrite <- H1my2. ring.
  - ring.
Qed.

(** Encoder output [s] satisfies [(1+s²) ≠ 0]. *)
Lemma encoder_one_plus_s_sq_ne_zero : forall (x y : Fp),
  (Curve25519.E.a * (x * x) + y * y =
     Fone + Curve25519.E.d * (x * x) * (y * y))%F ->
  ((Fone + y) * (Fone - y) * (x * y * (x * y)))%F <> Fzero ->
  fst (sqrt_ratio_m1 Fone ((Fone + y) * (Fone - y) * (x * y * (x * y)))) = true ->
  let s := ristretto_encode_aux x y Fone (x * y) in
  (Fone + s * s)%F <> Fzero.
Proof.
  intros x y Hoc Harg Hws s H1ps.
  destruct (Ristretto255_JacobiQuartic.encoder_on_jq x y Hoc Harg Hws) as [Honj|Honj];
    fold s in Honj.
  - pose proof (one_plus_s_sq_zero_d_X_sq_one _ _ Honj H1ps) as Hdxsq.
    exact (d_x_sq_one_contra _ _ Hoc Hdxsq).
  - pose proof (one_plus_s_sq_zero_d_X_sq_one _ _ Honj H1ps) as Hdysq.
    exact (d_ySQ_sq_one_contra _ _ Hoc Harg Hdysq).
Qed.

(** From [on_jq s X] + [s ≠ 0], [jq_v(s) ≠ 0]. *)
Lemma jq_v_ne_zero_from_on_jq : forall (s X : Fp),
  Ristretto255_JacobiQuartic.on_jq s X ->
  s <> Fzero ->
  Ristretto255_JacobiQuartic.jq_v s <> Fzero.
Proof.
  intros s X Honj Hsnz Hjqv.
  unfold Ristretto255_JacobiQuartic.on_jq in Honj.
  rewrite Hjqv in Honj.
  assert (Hs2 : (s * s)%F = Fzero).
  { assert (H4nz : (F.of_Z (2^255-19) 4 : Fp) <> Fzero) by apply Ristretto255_JacobiQuartic.four_nz.
    apply (Ristretto255_Sqrt.mul_cancel_l (F.of_Z (2^255-19) 4) _ _ H4nz).
    rewrite <- Honj. ring. }
  apply Ristretto255_Sqrt.mul_zero_factor in Hs2.
  destruct Hs2 as [H|H]; exact (Hsnz H).
Qed.

(** Encoder output: [jq_v(s) ≠ 0]. *)
Lemma encoder_jq_v_ne_zero : forall (x y : Fp),
  (Curve25519.E.a * (x * x) + y * y =
     Fone + Curve25519.E.d * (x * x) * (y * y))%F ->
  ((Fone + y) * (Fone - y) * (x * y * (x * y)))%F <> Fzero ->
  fst (sqrt_ratio_m1 Fone ((Fone + y) * (Fone - y) * (x * y * (x * y)))) = true ->
  let s := ristretto_encode_aux x y Fone (x * y) in
  Ristretto255_JacobiQuartic.jq_v s <> Fzero.
Proof.
  intros x y Hoc Harg Hws s.
  pose proof (encoder_s_ne_zero x y Hoc Harg Hws) as Hsnz. fold s in Hsnz.
  destruct (Ristretto255_JacobiQuartic.encoder_on_jq x y Hoc Harg Hws) as [Honj|Honj];
    fold s in Honj.
  - exact (jq_v_ne_zero_from_on_jq _ _ Honj Hsnz).
  - exact (jq_v_ne_zero_from_on_jq _ _ Honj Hsnz).
Qed.

(** (B-β.1) The decoder's denominator [jq_v(s) * (1+s²)²] is nonzero whenever
    the encoder ran on a valid (non-degenerate) input.  CLOSED (Qed) — combines
    [encoder_jq_v_ne_zero] + [encoder_one_plus_s_sq_ne_zero]. *)
Lemma encoder_decoder_den_nz : forall (x y : Fp),
  (Curve25519.E.a * (x * x) + y * y =
     Fone + Curve25519.E.d * (x * x) * (y * y))%F ->
  ((Fone + y) * (Fone - y) * (x * y * (x * y)))%F <> Fzero ->
  fst (sqrt_ratio_m1 Fone ((Fone + y) * (Fone - y) * (x * y * (x * y)))) = true ->
  let s := ristretto_encode_aux x y Fone (x * y) in
  (Ristretto255_JacobiQuartic.jq_v s * ((Fone + s*s) * (Fone + s*s)))%F <> Fzero.
Proof.
  intros x y Hoc Harg Hws s.
  pose proof (encoder_jq_v_ne_zero x y Hoc Harg Hws) as Hjqv_nz. fold s in Hjqv_nz.
  pose proof (encoder_one_plus_s_sq_ne_zero x y Hoc Harg Hws) as H1ps_nz. fold s in H1ps_nz.
  intro Hk.
  apply Ristretto255_Sqrt.mul_zero_factor in Hk.
  destruct Hk as [Hjqv | H1ps2].
  - exact (Hjqv_nz Hjqv).
  - apply Ristretto255_Sqrt.mul_zero_factor in H1ps2.
    destruct H1ps2; exact (H1ps_nz H).
Qed.

(** (B-β.2) Decoded [t = x_dec · y_dec] is non-negative.  REDUCED 2026-05-26 to
    the sharper sub-axiom [encoder_decoder_neg_t_residual] below: the entire
    [abs]/[*]/[1−s²] structure of the outer [is_negative] reduces (Qed-verified)
    to a single sign-bit equality between [2s(1−s²)iv] and [2s·iv·(1+s²)] — the
    encoder's per-leaf sign guarantee (8-leaf [ristretto_encode_aux] rotate/flip
    analysis bridging [encinv] ↔ [iv]).  Net effect: the original opaque axiom is
    now a [Lemma] (Qed) over a strictly-narrower residual axiom. *)
Axiom encoder_decoder_neg_t_residual : forall (x y : Fp),
  (Curve25519.E.a * (x * x) + y * y =
     Fone + Curve25519.E.d * (x * x) * (y * y))%F ->
  ((Fone + y) * (Fone - y) * (x * y * (x * y)))%F <> Fzero ->
  fst (sqrt_ratio_m1 Fone ((Fone + y) * (Fone - y) * (x * y * (x * y)))) = true ->
  let s := ristretto_encode_aux x y Fone (x * y) in
  forall iv : Fp,
    sqrt_ratio_m1 Fone
      (Ristretto255_JacobiQuartic.jq_v s * ((Fone + s*s) * (Fone + s*s)))
      = (true, iv) ->
    is_negative (F.of_Z _ 2 * s * (Fone - s*s) * iv)
    = is_negative (F.of_Z _ 2 * s * (iv * (Fone + s*s))).

Lemma encoder_decoder_neg_t : forall (x y : Fp),
  (Curve25519.E.a * (x * x) + y * y =
     Fone + Curve25519.E.d * (x * x) * (y * y))%F ->
  ((Fone + y) * (Fone - y) * (x * y * (x * y)))%F <> Fzero ->
  fst (sqrt_ratio_m1 Fone ((Fone + y) * (Fone - y) * (x * y * (x * y)))) = true ->
  let s := ristretto_encode_aux x y Fone (x * y) in
  forall iv : Fp,
    sqrt_ratio_m1 Fone
      (Ristretto255_JacobiQuartic.jq_v s * ((Fone + s*s) * (Fone + s*s)))
      = (true, iv) ->
    is_negative
      (abs (F.of_Z _ 2 * s * (iv * (Fone + s*s)))
       * ((Fone - s*s) *
          (iv * (iv * (Fone + s*s)) * Ristretto255_JacobiQuartic.jq_v s)))
    = false.
Proof.
  intros x y Hoc Harg Hws s iv Hsr.
  assert (Hzf : fst (sqrt_ratio_m1 Fone Fzero) = false) by (vm_compute; reflexivity).
  assert (Hden_nz : (Ristretto255_JacobiQuartic.jq_v s * ((Fone + s*s) * (Fone + s*s)))%F <> Fzero).
  { intro Hzero. rewrite Hzero in Hsr. rewrite Hsr in Hzf. simpl in Hzf. discriminate Hzf. }
  pose proof (Ristretto255_Sqrt.sqrt_ratio_m1_correct Fone _ Hden_nz) as Hc.
  rewrite Hsr in Hc.
  destruct Hc as [Hcdisj Hivneg].
  assert (Hinv : (Ristretto255_JacobiQuartic.jq_v s * ((Fone + s*s) * (Fone + s*s)) * (iv * iv) = Fone)%F).
  { destruct Hcdisj as [[_ Heq] | [Hf _]]; [ | discriminate Hf ].
    transitivity (Ristretto255_JacobiQuartic.jq_v s * ((Fone + s*s) * (Fone + s*s)) * iv * iv)%F; [ring | exact Heq]. }
  clear Hcdisj Hzf.
  set (xd := abs (F.of_Z p 2 * s * (iv * (Fone + s*s)))) in *.
  set (yd := ((Fone - s*s) * (iv * (iv * (Fone + s*s)) * Ristretto255_JacobiQuartic.jq_v s))%F) in *.
  assert (Hyd : (yd * (Fone + s*s))%F = (Fone - s*s)%F).
  { unfold yd.
    transitivity ((Fone - s*s) * (Ristretto255_JacobiQuartic.jq_v s * ((Fone + s*s) * (Fone + s*s)) * (iv * iv)))%F.
    - ring.
    - rewrite Hinv. ring. }
  set (xraw := (F.of_Z p 2 * s * (iv * (Fone + s*s)))%F) in *.
  assert (Hxrawyd : (xraw * yd)%F = (F.of_Z p 2 * s * (Fone - s*s) * iv)%F).
  { unfold xraw.
    transitivity (F.of_Z p 2 * s * iv * (yd * (Fone + s*s)))%F.
    - ring.
    - rewrite Hyd. ring. }
  pose proof (encoder_decoder_neg_t_residual x y Hoc Harg Hws iv Hsr) as Hres.
  fold s in Hres. fold xraw in Hres.
  unfold xd, abs.
  destruct (is_negative xraw) eqn:Hxr.
  - replace (F.opp xraw * yd)%F with (F.opp (xraw * yd))%F by ring.
    rewrite Hxrawyd.
    destruct (F.eq_dec (F.of_Z p 2 * s * (Fone - s*s) * iv) Fzero) as [Hz | Hnz].
    + rewrite Hz. unfold is_negative. rewrite F.to_Z_opp.
      replace (F.to_Z (Fzero:Fp)) with 0%Z by (rewrite ModularArithmeticTheorems.F.to_Z_of_Z; reflexivity).
      reflexivity.
    + rewrite (Ristretto255_Sqrt.is_negative_opp_nonzero _ Hnz).
      rewrite Hres. reflexivity.
  - rewrite Hxrawyd. rewrite Hres. reflexivity.
Qed.

(** (B-β.3) Decoded [y_dec ≠ 0].  CLOSED (Qed) — via
    [decoder_y_zero_to_s_sq] + [encoder_s_sq_ne_one]. *)
Lemma encoder_decoder_y_nz : forall (x y : Fp),
  (Curve25519.E.a * (x * x) + y * y =
     Fone + Curve25519.E.d * (x * x) * (y * y))%F ->
  ((Fone + y) * (Fone - y) * (x * y * (x * y)))%F <> Fzero ->
  fst (sqrt_ratio_m1 Fone ((Fone + y) * (Fone - y) * (x * y * (x * y)))) = true ->
  let s := ristretto_encode_aux x y Fone (x * y) in
  forall iv : Fp,
    sqrt_ratio_m1 Fone
      (Ristretto255_JacobiQuartic.jq_v s * ((Fone + s*s) * (Fone + s*s)))
      = (true, iv) ->
    ((Fone - s*s) *
     (iv * (iv * (Fone + s*s)) * Ristretto255_JacobiQuartic.jq_v s))%F <> Fzero.
Proof.
  intros x y Hoc Harg Hws s iv Hsr Hy0.
  pose proof (sqrt_ratio_m1_true_inv _ _ Hsr) as [Hinv _].
  exfalso.
  assert (Hinv' : (Ristretto255_JacobiQuartic.jq_v s * ((Fone + s * s) * (Fone + s * s)) * (iv * iv) = Fone)%F).
  { transitivity (Ristretto255_JacobiQuartic.jq_v s * ((Fone + s * s) * (Fone + s * s)) * iv * iv)%F.
    - ring.
    - exact Hinv. }
  pose proof (Ristretto255_JacobiQuartic.decoder_y_zero_to_s_sq s iv Hinv' Hy0) as Hss1.
  exact (encoder_s_sq_ne_one x y Hoc Harg Hws Hss1).
Qed.

(** B-β: full assembly (Qed) via the three residual axioms above + the structural
    reduction lemma + JQ.encoder_decoder_was_square. *)
Lemma decode_encode_success_nondegenerate :
  forall (oc : OnCurveObligation) (x y : Fp),
    (Curve25519.E.a * (x * x) + y * y =
       Fone + Curve25519.E.d * (x * x) * (y * y))%F ->
    ((Fone + y) * (Fone - y) * (x * y * (x * y)))%F <> Fzero ->
    fst (sqrt_ratio_m1 Fone ((Fone + y) * (Fone - y) * (x * y * (x * y)))) = true ->
    exists Q, ristretto_decode_bytes oc
                (ristretto_encode_bytes (to_extended (x, y))) = Some Q.
Proof.
  intros oc x y Hoc Harg Hws.
  unfold ristretto_encode_bytes, ristretto_encode_bytes_of_F,
         ristretto_encode, to_extended.
  set (s := ristretto_encode_aux x y Fone (x * y)).
  (* den ≠ 0 (axiom B-β.1) *)
  pose proof (encoder_decoder_den_nz x y Hoc Harg Hws) as Hden.
  cbv zeta in Hden. fold s in Hden.
  (* ws = true at den (via JQ.encoder_decoder_was_square) *)
  pose proof (Ristretto255_JacobiQuartic.encoder_decoder_was_square
                x y Hoc Harg Hws) as Hws_den.
  cbv zeta in Hws_den. fold s in Hws_den. specialize (Hws_den Hden).
  (* Destruct sqrt_ratio_m1 at den, fix ws = true. *)
  destruct (sqrt_ratio_m1 Fone
              (Ristretto255_JacobiQuartic.jq_v s * ((Fone + s*s) * (Fone + s*s))))
    as [ws_den iv] eqn:Hsr.
  cbn [fst] in Hws_den. subst ws_den.
  (* The two remaining sign obligations from the named axioms. *)
  pose proof (encoder_decoder_neg_t x y Hoc Harg Hws iv) as Hnegt.
  cbv zeta in Hnegt. fold s in Hnegt. specialize (Hnegt Hsr).
  pose proof (encoder_decoder_y_nz x y Hoc Harg Hws iv) as Hynz.
  cbv zeta in Hynz. fold s in Hynz. specialize (Hynz Hsr).
  (* is_negative s = false. *)
  assert (Hneg_s : is_negative s = false) by (unfold s; apply encoder_is_negative_false).
  (* Apply the reduction lemma. *)
  apply (decode_bytes_some_of_coords oc _
          (abs (F.of_Z _ 2 * s * (iv * (Fone + s*s))))
          ((Fone - s*s) *
           (iv * (iv * (Fone + s*s)) *
            Ristretto255_JacobiQuartic.jq_v s))).
  exact (decode_coords_succeeds_from_inv s Hneg_s iv Hsr Hnegt Hynz).
Qed.

Lemma decode_encode_success :
  forall (oc : OnCurveObligation) (P : Curve25519.E.point),
    valid_ristretto_input P ->
    exists Q, ristretto_decode_bytes oc
                (ristretto_encode_bytes (to_extended (point_coords P))) = Some Q.
Proof.
  intros oc P Hv.
  destruct P as [[x y] HocP].
  cbn [point_coords proj1_sig] in *.
  unfold valid_ristretto_input in Hv.
  cbn [point_coords proj1_sig] in Hv.
  destruct (F.eq_dec
    ((Fone + y) * (Fone - y) * (x * y * (x * y)))%F Fzero)
    as [Harg0 | Harg_nz].
  - (* B-α: degenerate case (Qed via [decode_encode_success_degenerate]). *)
    exact (decode_encode_success_degenerate oc x y Harg0).
  - (* B-β: non-degenerate; per-leaf sign analysis, axiomatised. *)
    exact (decode_encode_success_nondegenerate oc x y HocP Harg_nz Hv).
Qed.

(** (C) EXISTENTIAL Theorem 1 over the validity domain — PROVED (0 axioms modulo (B)), via
    [decode_encode_success] + [ristretto_encode_decode_roundtrip_valid]. *)
Theorem ristretto_encode_decode_roundtrip_exists :
  forall (oc : OnCurveObligation) (P : Curve25519.E.point),
    valid_ristretto_input P ->
    exists Q, ristretto_decode_bytes oc
                (ristretto_encode_bytes (to_extended (point_coords P))) = Some Q
              /\ ristretto_equiv P Q.
Proof.
  intros oc P Hv.
  destruct (decode_encode_success oc P Hv) as [Q HdecQ].
  exists Q. split; [ exact HdecQ | ].
  exact (ristretto_encode_decode_roundtrip_valid oc P Q HdecQ Hv).
Qed.

(** (A) DECAF SQUARENESS — membership ⇒ validity: a prime-order point's encoder sqrt succeeds.
    The genuine deep theorem (Hamburg Decaf §5 / Jacobi-quartic isogeny; ws=true ⟺ (1-y²) is a
    square on the main subgroup).

    STRENGTHENED to a disjunction with the identity coords [(0,1)]: the original statement
    [on_main_subgroup P -> valid_ristretto_input P] is FALSE at [P = E.zero] (verified by
    [vm_compute]: [sqrt_ratio_m1 Fone Fzero = (false, _)] — the [arg = 0] degenerate input
    gives [was_square = false], not [true]).  All consumers that branch through the round-trip
    handle the identity disjunct separately via [decoder_zero_returns_identity]. *)

(** ===== Doubling-surjection axiom (A.2.1 + group structure of ⟨B⟩) =====

    Every prime-order ⟨B⟩ point is either the identity (coords (0,1)) or is the double of
    another on-curve point [Q] whose doubling-formula's denominator [(1 - d·xQ²·yQ²)] is
    nonzero (free Edwards completeness lemma [denomy_nz] applied to [Q,Q]) AND whose image
    avoids the encoder's [arg = 0] degeneracy [(1+yP)(1-yP)(xP·yP)² ≠ 0] (the latter holds
    because ⟨B⟩ has odd prime order [l ≈ 2^252] and contains no order-2/order-4 points,
    excluding the locus [x=0 ∨ y=±1] which is exactly E[4]).

    This axiom encapsulates A.2.1 ([l·B = E.zero], RFC 8032 §5.1) PLUS the torsion-exclusion
    on ⟨B⟩ PLUS the 2-surjectivity ((ℓ+1)/2 is the inverse of 2 mod ℓ).  All three are
    well-known group-theoretic facts; the codebase currently lacks a verified Edwards
    scalarmult to derive them mechanically (see [src/Bedrock/End2End/Ed25519/Scalarmult.v]'s
    deferred-with-comment placeholder).  Per plan §A.2.1 fallback (a).

    PARTIAL DISCHARGE (2026-05-26): The [n = 0] (identity) case is now PROVED as a
    [Lemma] via [nB_zero_coords] below: [Nat.iter 0 _ Curve25519.E.zero = Curve25519.E.zero],
    whose coords are [(F.zero, F.one)] by [vm_compute].  The residual axiom
    [main_subgroup_doubling_nontrivial] is restricted to the [n <> 0] case — exactly the
    non-identity prime-order points, where the [2]-surjectivity of [⟨B⟩] (and the
    torsion-exclusion arg ≠ 0) is the genuine open content.  No new axiomatic content;
    the [n = 0] sub-case is no longer assumed. *)

(** [nB 0 = E.zero] by [Nat.iter] computation; coords reduce to [(0, 1)] by [vm_compute]
    on [F (2^255-19)] zero/one canonical reps.  Closes the identity case of
    [main_subgroup_doubling_or_identity] mechanically. *)
Lemma nB_zero_coords : point_coords (nB 0) = (Fzero, Fone).
Proof.
  cbv [nB Nat.iter].
  cbv [point_coords Curve25519.E.zero E.zero proj1_sig].
  apply pair_equal_spec.
  split; apply ModularArithmeticTheorems.F.eq_to_Z_iff; reflexivity.
Qed.

(** Residual content of the original axiom, now restricted to the [n <> 0] case.
    For [n = 0], [nB_zero_coords] suffices (identity disjunct) — see [main_subgroup_doubling_or_identity]
    below, which is now a proved [Lemma].

    The [n <> 0] case requires [⟨B⟩] = prime-order subgroup structure: [2]-surjectivity
    (every nonzero element of an odd-prime-order group is a doubled element) AND
    torsion-exclusion (no [n <> 0 mod l] hits the locus [x = 0 ∨ y = ±1] = E[4]).
    Both follow from [l · B = E.zero], which in turn requires a verified bedrock2
    Edwards scalarmult (see [src/Bedrock/End2End/Ed25519/Scalarmult.v] — parameters
    declared, body deferred). *)
(** WIRED 2026-05-26: this is now [Ristretto255_MainSubgroup.main_subgroup_doubling_nontrivial]
    (a proper [Lemma] / [Qed] assembly), discharged from the bridge's [E_mul_l_B_zero] via
    [scalarmult_mod_order]-based 2-surjectivity and [double_x0_zero]-based torsion-exclusion.
    The cluster's residual axioms now live in [Ristretto255_MainSubgroup]: 5 documented
    deferred axioms ([surjectivity_witness], [arg_zero_kills], [S_torsion_kill],
    [double_x0_zero], and the bridge's [E_mul_l_B_zero]), each with the full proof
    preserved in a [(* PRESERVED PROOF *)] comment — same kernel-perf-wall class as
    [E_mul_l_B_zero], identifiable for re-attack as Rocq Qed perf improves. *)
(* main_subgroup_doubling_nontrivial: imported from Ristretto255_MainSubgroup. *)

(** Discharged from [nB_zero_coords] (n=0) + [main_subgroup_doubling_nontrivial] (n<>0).
    Signature unchanged; downstream consumer [main_subgroup_valid] needs no edit. *)
Lemma main_subgroup_doubling_or_identity :
  forall (P : Curve25519.E.point), on_main_subgroup P ->
    point_coords P = (Fzero, Fone) \/
    exists (xQ yQ : Fp),
      (Curve25519.E.a * (xQ * xQ) + yQ * yQ
       = Fone + Curve25519.E.d * (xQ * xQ) * (yQ * yQ))%F /\
      snd (point_coords P)
        = ((yQ * yQ + xQ * xQ)
           / (Fone - Curve25519.E.d * (xQ * xQ) * (yQ * yQ)))%F /\
      ((Fone + snd (point_coords P)) * (Fone - snd (point_coords P)) *
        (fst (point_coords P) * snd (point_coords P) *
         (fst (point_coords P) * snd (point_coords P))))%F <> Fzero.
Proof.
  intros P [n Hn].
  destruct n as [|n'].
  - left. rewrite Hn. apply nB_zero_coords.
  - destruct (main_subgroup_doubling_nontrivial (S n') ltac:(discriminate)) as [Hid|Hex].
    + left. rewrite Hn. exact Hid.
    + right. rewrite Hn. exact Hex.
Qed.

Lemma main_subgroup_valid :
  forall P : Curve25519.E.point, on_main_subgroup P ->
    point_coords P = (Fzero, Fone) \/ valid_ristretto_input P.
Proof.
  intros P Hm.
  destruct (main_subgroup_doubling_or_identity P Hm) as [Hid | (xQ & yQ & HoQ & HyP_eq & Harg)].
  - left. exact Hid.
  - right. unfold valid_ristretto_input.
    destruct (point_coords P) as [xP yP] eqn:HPc.
    cbn [snd] in HyP_eq. cbn [fst snd] in Harg.
    apply (Ristretto255_JacobiQuartic.chi_doubling_main_subgroup xP yP).
    + (* on-curve at P *)
      destruct P as [[x y] HocP]. cbn [point_coords proj1_sig] in HPc. inversion HPc; subst.
      exact HocP.
    + (* doubling witness *)
      exists xQ, yQ. split; [ exact HoQ | ]. split.
      * pose proof (denomy_nz xQ yQ xQ yQ HoQ HoQ) as HDny.
        intro Hk. apply HDny.
        transitivity (Fone - Curve25519.E.d * (xQ * xQ) * (yQ * yQ))%F; [ ring | exact Hk ].
      * exact HyP_eq.
    + exact Harg.
Qed.

(** Helper: at the all-zero byte string, [ristretto_decode_bytes oc] returns a typed
    point whose coords are [(0, 1)] (the affine identity).  Composes
    [decoder_zero_returns_identity] (from [Ristretto255_JacobiQuartic]) with the
    convoy match of [ristretto_decode_bytes]. *)
Lemma decode_bytes_zero :
  forall (oc : OnCurveObligation),
  exists Q : edwards25519_point,
    ristretto_decode_bytes oc (le_split 32 0%Z) = Some Q /\
    point_coords Q = (Fzero, Fone).
Proof.
  intros oc.
  pose proof Ristretto255_JacobiQuartic.decoder_zero_returns_identity as Hdec0.
  pose proof (decode_bytes_some_of_coords oc _ _ _ Hdec0) as [Q HQ].
  exists Q. split; [ exact HQ | ].
  (* Use [decode_bytes_coords] as the left-inverse: [bytes-decode = Some Q ⟹
     coords-decode = Some (point_coords Q)].  Then equate with [Hdec0] and
     inject.  Avoids the slow inline [destruct (ristretto_decode_coords ...)]
     against the unfolded convoy (the >6 min Qed pitfall). *)
  pose proof (decode_bytes_coords oc _ _ HQ) as Hcoords.
  rewrite Hdec0 in Hcoords.
  injection Hcoords. intros Heq. symmetry. exact Heq.
Qed.

(** (C') EXISTENTIAL Theorem 1 over the main subgroup — the form [Ristretto255_Canonicality.v]
    consumes — PROVED (0 axioms modulo (A)+(B) +
    [main_subgroup_doubling_or_identity]). *)
Theorem ristretto_encode_decode_roundtrip_subgroup :
  forall (oc : OnCurveObligation) (P : Curve25519.E.point),
    on_main_subgroup P ->
    exists Q, ristretto_decode_bytes oc
                (ristretto_encode_bytes (to_extended (point_coords P))) = Some Q
              /\ ristretto_equiv P Q.
Proof.
  intros oc P Hm.
  destruct (main_subgroup_valid P Hm) as [Hid | Hv].
  - (* Identity case: encode P = 0 bytes, decode 0 bytes = identity (0,1).
       The bytes-equation closes by [f_equal] (F.to_Z Fzero reduces to 0). *)
    assert (Hbytes : ristretto_encode_bytes (to_extended (point_coords P))
                    = le_split 32 0%Z).
    { rewrite Hid. unfold ristretto_encode_bytes, ristretto_encode_bytes_of_F,
        to_extended, ristretto_encode.
      assert (Hs0 : ristretto_encode_aux Fzero Fone Fone (Fzero * Fone) = Fzero)
        by (apply enc_arg0_s0; ring).
      rewrite Hs0. f_equal. }
    rewrite Hbytes.
    destruct (decode_bytes_zero oc) as [Q [HdecQ HQc]].
    exists Q. split; [ exact HdecQ | ].
    unfold ristretto_equiv. rewrite Hid, HQc, sub_affine_id_01.
    unfold is_4torsion_affine. left. split; reflexivity.
  - exact (ristretto_encode_decode_roundtrip_exists oc P Hv).
Qed.
