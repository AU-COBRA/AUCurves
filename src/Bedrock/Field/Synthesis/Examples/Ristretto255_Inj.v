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
Local Lemma HaQ : Curve25519.E.a = F.opp Fone.
Proof. unfold Curve25519.E.a. apply ModularArithmeticTheorems.F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

(* a/b = c whenever a = c*b and b<>0. *)
Local Lemma div_eq : forall (a b c : Fp), b <> Fzero -> a = (c * b)%F -> (a / b)%F = c.
Proof. intros a b c Hb Ha. rewrite Ha. field. exact Hb. Qed.

(* ===================== Edwards-completeness denominators =====================
   For any two on-curve affine points, the two [sub_affine] denominators are
   nonzero.  These are exactly the side conditions [step1_reduction] requires.
   Both follow from Edwards-curve completeness ([d] a non-square): see
   [Crypto.Curves.Edwards.Pre.denominator_nonzero_{x,y}].  Pure, reusable. *)
Local Lemma denomx_nz : forall (x1 y1 x2 y2 : Fp),
  (Curve25519.E.a * (x1 * x1) + y1 * y1 = Fone + Curve25519.E.d * (x1 * x1) * (y1 * y1))%F ->
  (Curve25519.E.a * (x2 * x2) + y2 * y2 = Fone + Curve25519.E.d * (x2 * x2) * (y2 * y2))%F ->
  (Fone + Curve25519.E.d * x1 * x2 * y1 * y2)%F <> Fzero.
Proof.
  intros x1 y1 x2 y2 H1 H2.
  exact (Crypto.Curves.Edwards.Pre.denominator_nonzero_x _ Curve25519.E.nonzero_a
           Curve25519.E.square_a _ Curve25519.E.nonsquare_d _ _ H1 _ _ H2).
Qed.

Local Lemma denomy_nz : forall (x1 y1 x2 y2 : Fp),
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
Local Lemma step1_reduction : forall (x y x' y' : Fp),
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
Local Lemma yeq_noflip : forall (s x y y' invsqrtE : Fp),
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
Local Lemma enc_arg0_s0 : forall (x y : Fp),
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
Local Lemma deg_oncurve_torsion : forall (x y : Fp),
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
Local Lemma sub_affine_id_01 : forall (a b : Fp), sub_affine (a, b) (Fzero, Fone) = (a, b).
Proof.
  intros a b. unfold sub_affine, opp_affine.
  f_equal; [ field; Decidable.vm_decide | unfold Curve25519.E.a; field; Decidable.vm_decide ].
Qed.

(* ===================== x-sign pinning helpers =====================
   [abs_pins_sign]: equal squares + nonneg target pin [a = +/- b] by sign of a.
   [oncurve_x2_eq]: on the curve, [x^2] is a function of [y^2] (off the
   [1-y^2=0] locus), so equal [y^2] forces equal [x^2]. *)

Local Lemma abs_pins_sign : forall (a b : Fp),
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

Local Lemma oncurve_x2_eq : forall (x y x'' y'' : Fp),
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
Local Lemma main_inversion : forall (x y x' y' : Fp),
  (Curve25519.E.a * (x * x) + y * y = Fone + Curve25519.E.d * (x * x) * (y * y))%F ->
  (Curve25519.E.a * (x' * x') + y' * y' = Fone + Curve25519.E.d * (x' * x') * (y' * y'))%F ->
  ((Fone + y) * (Fone - y) * (x * y * (x * y)))%F <> Fzero ->
  (ristretto_encode_aux x y Fone (x*y) * ristretto_encode_aux x y Fone (x*y) * (Fone + y')
     = Fone - y')%F ->
  (Fone + ristretto_encode_aux x y Fone (x*y) * ristretto_encode_aux x y Fone (x*y) <> Fzero)%F ->
  is_negative x' = false ->
  is_negative (ristretto_encode_aux x y Fone (x*y)) = false ->
  y' <> Fzero ->
  is_4torsion_affine (sub_affine (x, y) (x', y')).
Proof.
  intros x y x' y' Hoc Hoc_Q Hargnz Hs2y' Hu2nz Hxneg Hnegs Hynz.
  assert (Ha : Curve25519.E.a = F.opp Fone)
    by (unfold Curve25519.E.a; apply ModularArithmeticTheorems.F.eq_to_Z_iff; vm_compute; reflexivity).
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
  set (M := (inv * u1 * (inv * u2) * u2)%F) in *.
  assert (HMval : M = Fone \/ M = SQRT_M1).
  { destruct Hsrcase as [[_ Hsq] | [_ Hsq]].
    - left. transitivity (u1 * (u2 * u2) * inv * inv)%F; [ unfold M; field | exact Hsq ].
    - right. transitivity (u1 * (u2 * u2) * inv * inv)%F; [ unfold M; field | rewrite Hsq; field ]. }
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
  assert (K2 : (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D * (Curve25519.E.a - Curve25519.E.d))%F = Fone)
    by (unfold INVSQRT_A_MINUS_D, Curve25519.E.a, Curve25519.E.d;
        apply ModularArithmeticTheorems.F.eq_to_Z_iff; vm_compute; reflexivity).
  assert (Hcurve_id : ((Fone + x*x) * u1 = (u2 * u2) * (Curve25519.E.a - Curve25519.E.d))%F).
  { unfold u1, u2. rewrite Ha in Hoc |- *.
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
    rewrite Hr3, Hd. field. }
  assert (Hmag : (den_inv * den_inv * (Fone - Yf * Yf) = M)%F).
  { rewrite HYf2. unfold den_inv, Y0.
    destruct rot;
    [ assert (HY0s : ((x * SQRT_M1) * (x * SQRT_M1))%F = F.opp (x*x))
        by (assert (Hr : ((x * SQRT_M1) * (x * SQRT_M1))%F = ((SQRT_M1*SQRT_M1)*(x*x))%F) by field;
            rewrite Hr, Ristretto255_CaseScratch.SQRT_M1_sq; field);
      rewrite HY0s;
      apply (Ristretto255_Sqrt.mul_cancel_l u1 _ _ Hu1nz0);
      (transitivity ((inv*u1*INVSQRT_A_MINUS_D)*(inv*u1*INVSQRT_A_MINUS_D) * ((Fone + x*x)*u1))%F;
        [ field | ]);
      rewrite Hcurve_id;
      (transitivity ((inv*u1*(inv*u1)*(u2*u2)) * (INVSQRT_A_MINUS_D*INVSQRT_A_MINUS_D*(Curve25519.E.a-Curve25519.E.d)))%F;
        [ field | rewrite K2; unfold M; field ])
    | assert (HY0s : (y * y)%F = (Fone - u1)%F) by (unfold u1; field);
      rewrite HY0s;
      (assert (Hr : (Fone - (Fone - u1))%F = u1) by field); rewrite Hr;
      unfold M; field ]. }
  assert (Hstar : (s * s * (Fone + Yf) = M * (Fone - Yf))%F).
  { rewrite Hs2.
    transitivity ((den_inv * den_inv * (Fone - Yf * Yf)) * (Fone - Yf))%F; [ field | ].
    rewrite Hmag. ring. }
  assert (HMcancel : (M = Fone -> Yf = y')%F).
  { intro HM1. rewrite HM1 in Hstar.
    apply (Ristretto255_Sqrt.mul_cancel_l (Fone + s*s) _ _ Hu2nz).
    transitivity (Fone - s*s)%F.
    - replace ((Fone + s*s)*Yf)%F with (Yf + (s*s*(Fone + Yf)) - s*s)%F by ring.
      rewrite Hstar. ring.
    - replace ((Fone + s*s)*y')%F with (y' + (s*s*(Fone + y')) - s*s)%F by ring.
      rewrite Hs2y'. ring. }
  (* ----------------------------------------------------------------------
     VERIFIED CORE (all the above is machine-checked, 0 axioms):
       * [Hstar]   : s^2*(1+Yf) = M*(1-Yf)        -- unified encoder inversion
       * [Hmag]    : den_inv^2*(1-Yf^2) = M       -- branch-independent magnitude
                     (curve identity [Hcurve_id] + constant [K2])
       * [HMval]   : M = 1 \/ M = SQRT_M1         -- z_inv collapse
       * [HMcancel]: M = 1 -> Yf = y'             -- cancellation vs decoder rel.
     Reusable supporting lemmas (all Qed): [abs_pins_sign] (sign pinning from
     equal squares + nonneg target) and [oncurve_x2_eq] (x^2 is a function of
     y^2 on the curve).

     REMAINING GOAL (the 8-leaf branch dispatch, [M] x [rot] x [flip]):
        |- is_4torsion_affine (sub_affine (x, y) (x', y'))
     with [Hstar], [HMcancel], [HMval] in scope plus [Hxneg : is_negative x' =
     false], [Hynz : y' <> Fzero], both points on curve, [Hu1nz0 : u1 <> 0].

     Per-leaf recipe (worked out, feeds [step1_reduction]; each leaf pins
     (x,y) to one explicit E[4]-translate of (x',y') then [apply
     step1_reduction] with [denomx_nz]/[denomy_nz]):
       M=1, rot=false : flip = is_negative x; Yf = y' gives y' = +/- y, then
         [oncurve_x2_eq] => x^2=x'^2 and [abs_pins_sign x x'] pins the sign via
         flip:  flip=false => x=x' (system (i), (0,1));
                flip=true  => x=-x',y'=-y (system (ii), (0,-1)).
       M=1, rot=true  : Yf = +/- x*SQRT_M1 = y' (order-4); [oncurve_x2_eq] on
         y'^2 = -x^2 and [abs_pins_sign] pin to (SQRT_M1*y, SQRT_M1*x)-translate
         (systems (iii)/(iv)).
       M=SQRT_M1 (rot=false/true) : the dual pairing; cancel [Hstar] vs
         [Hs2y'] (eliminate s^2) to relate Yf and y' through SQRT_M1, then the
         same [oncurve_x2_eq]+[abs_pins_sign] sign-pinning yields the
         complementary two systems.
     ---------------------------------------------------------------------- *)
Admitted.

Lemma encode_decode_equiv' : forall (x y x' y' : Fp),
  (Curve25519.E.a * (x * x) + y * y = Fone + Curve25519.E.d * (x * x) * (y * y))%F ->
  ristretto_decode_coords (ristretto_encode_bytes (to_extended (x, y))) = Some (x', y') ->
  is_4torsion_affine (sub_affine (x, y) (x', y')).
Proof.
  intros x y x' y' Hoc Hdec.
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
    apply (main_inversion x y x' y' Hoc Hoc_Q Hargnz Hs2y' Hu2nz Hxneg Hnegs Hynz).
Qed.
