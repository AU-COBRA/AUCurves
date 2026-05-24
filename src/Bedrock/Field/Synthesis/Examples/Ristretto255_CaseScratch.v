(** * Ristretto255_CaseScratch — LIGHT scratch file to develop the four
      4-torsion canonical-rep case lemmas (encoder-invariance halves)
      that are Admitted in Ristretto255_RoundTrip.v.

    Loadable via MCP fast (mirrors Ristretto255_Sqrt.v header).
    DO NOT DELETE — proofs are recoverable from here. *)

From Stdlib Require Import ZArith NArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia Bool.Bool.
Require Import Crypto.Spec.ModularArithmetic Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.PrimeFieldTheorems Crypto.Algebra.Hierarchy Crypto.Algebra.Field.
Require Import Crypto.Algebra.Group.
Require Import Crypto.Spec.Curve25519.
Require Import Crypto.Spec.CompleteEdwardsCurve.
Require Import Crypto.Curves.Edwards.AffineProofs.
Require Import Bedrock.Field.Synthesis.Examples.Ristretto255_Encode.
Require Import Bedrock.Field.Synthesis.Examples.Ristretto255_Sqrt.
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

(* === replicated from Ristretto255_RoundTrip.v / TorsionCases.v === *)

Definition to_extended (xy : Fp * Fp) : Fp * Fp * Fp * Fp :=
  let '(x, y) := xy in (x, y, Fone, (x * y)%F).

Definition opp_affine (xy : Fp * Fp) : Fp * Fp :=
  let '(x, y) := xy in (F.opp x, y).

Definition sub_affine_x (P Q : Fp * Fp) : Fp :=
  let '(x1, y1) := P in
  let '(x2, y2) := opp_affine Q in
  ((x1 * y2 + y1 * x2) / (Fone + Curve25519.E.d * x1 * x2 * y1 * y2))%F.

Definition sub_affine_y (P Q : Fp * Fp) : Fp :=
  let '(x1, y1) := P in
  let '(x2, y2) := opp_affine Q in
  ((y1 * y2 - Curve25519.E.a * x1 * x2) / (Fone - Curve25519.E.d * x1 * x2 * y1 * y2))%F.

(* === helper lemmas (from Sqrt.v / TorsionCases.v) === *)

Lemma is_negative_opp_nonzero : forall (s : Fp),
  s <> Fzero -> is_negative (F.opp s) = negb (is_negative s).
Proof.
  intros s Hnz.
  unfold is_negative.
  rewrite F.to_Z_opp.
  assert (Hp : (0 < 2^255-19)%Z) by (vm_compute; reflexivity).
  assert (Hrng : (0 <= F.to_Z s < 2^255-19)%Z) by (apply F.to_Z_range; lia).
  assert (Hsnz : F.to_Z s <> 0%Z).
  { intro Hz. apply Hnz. apply ModularArithmeticTheorems.F.eq_to_Z_iff.
    rewrite Hz. rewrite F.to_Z_of_Z. reflexivity. }
  rewrite Z.mod_opp_l_nz; [|lia|rewrite Z.mod_small; lia].
  rewrite Z.mod_small by lia.
  change (Z.pos (2^255-19)%positive) with (2^255 - 19)%Z.
  rewrite !Z.bit0_odd.
  rewrite Z.odd_sub.
  replace (Z.odd (2^255 - 19)) with true by reflexivity.
  destruct (Z.odd (F.to_Z s)); reflexivity.
Qed.

Lemma is_negative_zero : is_negative Fzero = false.
Proof. unfold is_negative. rewrite F.to_Z_of_Z. reflexivity. Qed.

Lemma SQRT_M1_sq : (SQRT_M1 * SQRT_M1)%F = F.opp Fone.
Proof. unfold SQRT_M1. apply ModularArithmeticTheorems.F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

(* abs of opp equals abs *)
Lemma abs_opp : forall (s : Fp), abs (F.opp s) = abs s.
Proof.
  intros s. destruct (F.eq_dec s Fzero) as [Hz | Hnz].
  - subst s. unfold abs. Decidable.vm_decide.
  - unfold abs. rewrite (is_negative_opp_nonzero s Hnz).
    destruct (is_negative s); simpl.
    + reflexivity.
    + field.
Qed.

(* === scratch development below === *)

(* mul of two opps *)
Lemma opp_mul_opp : forall (x y : Fp), (F.opp x * F.opp y)%F = (x * y)%F.
Proof. intros. field. Qed.

Lemma mul_zero_factor : forall (a b : Fp), (a * b)%F = Fzero -> a = Fzero \/ b = Fzero.
Proof. intros a b H. apply Hierarchy.zero_product_zero_factor in H. exact H. Qed.

Lemma sub_eq_zero : forall (a b : Fp), (a - b)%F = Fzero -> a = b.
Proof. intros a b H. assert (Hr : a = ((a - b) + b)%F) by field. rewrite Hr, H. field. Qed.

(* On the curve, (1+y)(1-y) = 0 forces x = 0.  (a-d) <> 0 makes
   (a-d)*x^2 = 0 collapse to x = 0.) *)
Lemma oncurve_u1c : forall (x y : Fp),
  (Curve25519.E.a * (x * x) + y * y = Fone + Curve25519.E.d * (x * x) * (y * y))%F ->
  x = Fzero \/ ((Fone + y) * (Fone - y))%F <> Fzero.
Proof.
  intros x y Hc.
  destruct (F.eq_dec ((Fone + y) * (Fone - y)) Fzero) as [Hu | Hu];
    [ left | right; exact Hu ].
  (* (1+y)(1-y) = 0 means y*y = 1; substitute into curve eqn. *)
  assert (Hy2 : (y * y)%F = Fone)
    by (assert (Hr : (y*y)%F = (Fone - (Fone+y)*(Fone-y))%F) by field;
        rewrite Hr, Hu; field).
  (* Hadx := (a - d) * (x*x) = 0 *)
  assert (Hadx : ((Curve25519.E.a - Curve25519.E.d) * (x * x))%F = Fzero).
  { rewrite Hy2 in Hc.
    assert (Hr2 : ((Curve25519.E.a - Curve25519.E.d) * (x * x))%F
                = ((Curve25519.E.a * (x*x) + Fone)
                   - (Fone + Curve25519.E.d * (x*x) * Fone))%F) by field.
    rewrite Hr2, <- Hc. field. }
  assert (Had : (Curve25519.E.a - Curve25519.E.d)%F <> Fzero)
    by (unfold Curve25519.E.a, Curve25519.E.d; Decidable.vm_decide).
  apply mul_zero_factor in Hadx.
  destruct Hadx as [H | Hxx];
    [ exact (False_ind _ (Had H))
    | apply mul_zero_factor in Hxx; destruct Hxx; assumption ].
Qed.

(* In char <> 2: a*(b - F.opp b) = a*2*b; if a*b = 0 then a*b = a*(F.opp b). *)
Lemma sub_opp_eq_of_mul_zero : forall (a b : Fp),
  (a * b)%F = Fzero -> (a * (Fone - F.opp b))%F = (a * (Fone - b))%F.
Proof.
  intros a b H.
  assert (Hr : (a * (Fone - F.opp b) - a * (Fone - b))%F = (a * b + a * b)%F) by field.
  apply sub_eq_zero. rewrite Hr, H. field.
Qed.

(** Encoder-invariance under (x,y) -> (-x,-y), keeping Z=1, T=x*y.
    This is the order-2 symmetry.  Needs (x,y) on the curve to rule out
    the [u1c = 0] corner in the [X'*z_inv = 0] case. *)
Lemma encode_aux_negate : forall (x y : Fp),
  (Curve25519.E.a * (x * x) + y * y = Fone + Curve25519.E.d * (x * x) * (y * y))%F ->
  ristretto_encode_aux (F.opp x) (F.opp y) Fone (x * y)
  = ristretto_encode_aux x y Fone (x * y).
Proof.
  intros x y Hc.
  unfold ristretto_encode_aux.
  assert (Hu1 : (Fone + F.opp y) * (Fone - F.opp y) = (Fone + y) * (Fone - y)) by field.
  assert (Hu2 : (F.opp x * F.opp y) = (x * y)) by field.
  rewrite !Hu1, !Hu2.
  destruct (sqrt_ratio_m1 Fone ((Fone + y) * (Fone - y) * (x * y * (x * y)))) as [ws inv].
  set (u1c := (Fone + y) * (Fone - y)) in *.
  set (zinv := (x * y * (inv * u1c * (inv * (x * y)) * (x * y)))) in *.
  set (rot := is_negative zinv) in *.
  set (M := (inv * u1c * (inv * (x * y)) * (x * y))%F) in *.
  set (di := (if rot then inv * u1c * INVSQRT_A_MINUS_D else inv * (x * y))%F) in *.
  set (X'R := (if rot then y * SQRT_M1 else x)%F) in *.
  set (Y0R := (if rot then x * SQRT_M1 else y)%F) in *.
  assert (HX'L : (if rot then F.opp y * SQRT_M1 else F.opp x) = F.opp X'R)
    by (unfold X'R; destruct rot; field).
  assert (HY0L : (if rot then F.opp x * SQRT_M1 else F.opp y) = F.opp Y0R)
    by (unfold Y0R; destruct rot; field).
  rewrite HX'L, HY0L.
  assert (Hopp_mul : (F.opp X'R * M) = F.opp (X'R * M)) by field.
  rewrite Hopp_mul.
  (* Key: when X'*z_inv = 0, then di * Y0R = 0 (forces both outputs equal). *)
  assert (HdiY0 : (X'R * M)%F = Fzero -> (di * Y0R)%F = Fzero).
  { intro Hz.
    destruct (oncurve_u1c x y Hc) as [Hx0 | Hu1c].
    - unfold di, Y0R, X'R, M, u1c in *; subst x; destruct rot; field.
    - unfold X'R, M in Hz.
      assert (Hrot_nz : rot = true -> zinv <> Fzero)
        by (unfold rot; intros Hr Hc0; rewrite Hc0, is_negative_zero in Hr; discriminate).
      destruct rot eqn:Erot.
      + (* rot = true forces zinv <> 0, hence y <> 0; X'*M=0 is a contradiction. *)
        exfalso.
        assert (Hzinv : zinv <> Fzero) by (apply Hrot_nz; reflexivity).
        apply Hzinv.
        assert (HSnz : SQRT_M1 <> Fzero)
          by (unfold SQRT_M1; intro Hs; apply F.eq_to_Z_iff in Hs; vm_compute in Hs; discriminate).
        assert (Hrw : zinv = ((x / SQRT_M1)
                       * (y * SQRT_M1 * (inv * u1c * (inv * (x * y)) * (x * y))))%F)
          by (unfold zinv, M; field; exact HSnz).
        rewrite Hrw, Hz. field. exact HSnz.
      + (* rot = false: di = inv*(x*y), Y0R = y; factor out u1c (<> 0). *)
        unfold di, Y0R.
        assert (Hz2 : (u1c * (inv * (inv * (x * x * x * (y * y)))))%F = Fzero)
          by (rewrite <- Hz; field).
        apply mul_zero_factor in Hz2. destruct Hz2 as [Hbad | Hz3];
          [ exfalso; apply Hu1c; unfold u1c in Hbad; exact Hbad | ].
        apply mul_zero_factor in Hz3. destruct Hz3 as [Hi | Hz4].
        * rewrite Hi. field.
        * apply mul_zero_factor in Hz4. destruct Hz4 as [Hi2 | Hz5].
          -- rewrite Hi2. field.
          -- apply mul_zero_factor in Hz5. destruct Hz5 as [Hx3 | Hy2z].
             ++ apply mul_zero_factor in Hx3. destruct Hx3 as [Hxx | Hx0];
                  [ apply mul_zero_factor in Hxx; destruct Hxx as [Hx0|Hx0]; rewrite Hx0; field
                  | rewrite Hx0; field ].
             ++ apply mul_zero_factor in Hy2z. destruct Hy2z as [Hy0|Hy0]; rewrite Hy0; field. }
  destruct (F.eq_dec (X'R * M) Fzero) as [Hz | Hnz].
  - assert (Hz0 : F.opp (X'R * M) = Fzero) by (rewrite Hz; field).
    rewrite Hz0, Hz. rewrite is_negative_zero. cbn match.
    rewrite (sub_opp_eq_of_mul_zero di Y0R (HdiY0 Hz)). reflexivity.
  - rewrite (is_negative_opp_nonzero (X'R * M) Hnz).
    destruct (is_negative (X'R * M)); simpl.
    + reflexivity.
    + f_equal; f_equal; f_equal; field.
Qed.

Lemma canonical_rep_case_order2 :
  forall (Px Py Qx Qy : Fp),
    (Curve25519.E.a * (Px * Px) + Py * Py =
     Fone + Curve25519.E.d * (Px * Px) * (Py * Py))%F ->
    (Curve25519.E.a * (Qx * Qx) + Qy * Qy =
     Fone + Curve25519.E.d * (Qx * Qx) * (Qy * Qy))%F ->
    sub_affine_x (Px, Py) (Qx, Qy) = Fzero ->
    sub_affine_y (Px, Py) (Qx, Qy) = F.opp Fone ->
    ristretto_encode_bytes (to_extended (Px, Py))
    = ristretto_encode_bytes (to_extended (Qx, Qy)).
Proof.
  intros Px Py Qx Qy HP HQ Hx Hy.
  pose (Pt := exist (fun xy => let '(x, y) := xy in
    (Curve25519.E.a*(x*x) + y*y = Fone + Curve25519.E.d*(x*x)*(y*y))%F)
    (Px, Py) HP : Curve25519.E.point).
  pose (Qt := exist (fun xy => let '(x, y) := xy in
    (Curve25519.E.a*(x*x) + y*y = Fone + Curve25519.E.d*(x*x)*(y*y))%F)
    (Qx, Qy) HQ : Curve25519.E.point).
  pose (Qopp := @AffineProofs.E.opp _ _ _ _ F.opp F.add F.sub F.mul _ _
    Curve25519.field _ Curve25519.E.a Curve25519.E.d
    Curve25519.E.nonzero_a Qt).
  pose (D := Curve25519.E.add Pt Qopp).
  assert (Hcoord_D : E.coordinates D
                     = (sub_affine_x (Px, Py) (Qx, Qy),
                        sub_affine_y (Px, Py) (Qx, Qy)))
    by reflexivity.
  rewrite Hx, Hy in Hcoord_D.
  assert (HT2 : (Curve25519.E.a * (Fzero * Fzero) + F.opp Fone * F.opp Fone
                 = Fone + Curve25519.E.d * (Fzero * Fzero)
                          * (F.opp Fone * F.opp Fone))%F)
    by (unfold Curve25519.E.a, Curve25519.E.d; Decidable.vm_decide).
  pose (T2 := exist (fun xy => let '(x, y) := xy in
    (Curve25519.E.a*(x*x) + y*y = Fone + Curve25519.E.d*(x*x)*(y*y))%F)
    (Fzero, F.opp Fone) HT2 : Curve25519.E.point).
  assert (HD_T2 : E.eq D T2).
  1:unfold E.eq, T2; rewrite Hcoord_D; simpl; split; reflexivity.
  pose proof (@AffineProofs.E.edwards_curve_commutative_group _ _ _ _
                F.opp F.add F.sub F.mul _ _
                Curve25519.field Curve25519.char_ge_3 _
                Curve25519.E.a Curve25519.E.d
                Curve25519.E.nonzero_a
                Curve25519.E.square_a
                Curve25519.E.nonsquare_d) as Hgrp.
  assert (HPt_eq : E.eq Pt (Curve25519.E.add T2 Qt)).
  1:rewrite <- HD_T2; unfold D, Qopp;
    rewrite <- (associative Pt (E.opp Qt) Qt);
    rewrite (left_inverse Qt); rewrite (right_identity Pt); reflexivity.
  assert (HT2Qt_coord : E.coordinates (Curve25519.E.add T2 Qt)
                       = (F.opp Qx, F.opp Qy)).
  1:unfold Curve25519.E.add, E.add, T2, Qt, E.coordinates;
    cbv [fst snd]; f_equal;
    [field; Decidable.vm_decide | field; Decidable.vm_decide].
  assert (HPxy : (Px, Py) = (F.opp Qx, F.opp Qy)).
  1:rewrite <- HT2Qt_coord;
    destruct HPt_eq as [Hx' Hy'];
    unfold Pt, E.coordinates in Hx', Hy';
    destruct (E.coordinates (Curve25519.E.add T2 Qt)) as [x2 y2] eqn:E;
    injection (eq_sym (E : E.coordinates _ = _)) as Hcx Hcy;
    subst x2 y2; cbn in Hx', Hy'; subst; reflexivity.
  inversion HPxy as [[HPx HPy]]. subst Px Py.
  (* Encoder-invariance half. *)
  unfold ristretto_encode_bytes, ristretto_encode, to_extended.
  f_equal.
  rewrite (opp_mul_opp Qx Qy).
  apply (encode_aux_negate Qx Qy HQ).
Qed.

(** ** Identity case — ported verbatim from Ristretto255_TorsionCases.v
       (fully Qed there).  sub_affine = (0,1) ⇒ P = Q. *)
Lemma canonical_rep_case_identity :
  forall (Px Py Qx Qy : Fp),
    (Curve25519.E.a * (Px * Px) + Py * Py =
     Fone + Curve25519.E.d * (Px * Px) * (Py * Py))%F ->
    (Curve25519.E.a * (Qx * Qx) + Qy * Qy =
     Fone + Curve25519.E.d * (Qx * Qx) * (Qy * Qy))%F ->
    sub_affine_x (Px, Py) (Qx, Qy) = Fzero ->
    sub_affine_y (Px, Py) (Qx, Qy) = Fone ->
    ristretto_encode_bytes (to_extended (Px, Py))
    = ristretto_encode_bytes (to_extended (Qx, Qy)).
Proof.
  intros Px Py Qx Qy HP HQ Hx Hy.
  pose (Pt := exist (fun xy => let '(x, y) := xy in
    (Curve25519.E.a*(x*x) + y*y = Fone + Curve25519.E.d*(x*x)*(y*y))%F)
    (Px, Py) HP : Curve25519.E.point).
  pose (Qt := exist (fun xy => let '(x, y) := xy in
    (Curve25519.E.a*(x*x) + y*y = Fone + Curve25519.E.d*(x*x)*(y*y))%F)
    (Qx, Qy) HQ : Curve25519.E.point).
  pose (Qopp := @AffineProofs.E.opp _ _ _ _ F.opp F.add F.sub F.mul _ _
    Curve25519.field _ Curve25519.E.a Curve25519.E.d
    Curve25519.E.nonzero_a Qt).
  pose (D := Curve25519.E.add Pt Qopp).
  assert (Hcoord_D : E.coordinates D
                     = (sub_affine_x (Px, Py) (Qx, Qy),
                        sub_affine_y (Px, Py) (Qx, Qy)))
    by reflexivity.
  rewrite Hx, Hy in Hcoord_D.
  assert (HD_zero : E.eq D Curve25519.E.zero)
    by (unfold E.eq, Curve25519.E.zero, E.zero;
        rewrite Hcoord_D; simpl; split; reflexivity).
  pose proof (@AffineProofs.E.edwards_curve_commutative_group _ _ _ _
                F.opp F.add F.sub F.mul _ _
                Curve25519.field Curve25519.char_ge_3 _
                Curve25519.E.a Curve25519.E.d
                Curve25519.E.nonzero_a
                Curve25519.E.square_a
                Curve25519.E.nonsquare_d) as Hgrp.
  destruct Hgrp as [Hgrp_group _].
  pose proof (@inv_unique _ _ _ _ _ Hgrp_group Qopp Pt HD_zero) as Hinv1.
  pose proof (@Group.inv_inv _ _ _ _ _ Hgrp_group Qt) as Hinvinv.
  assert (HPt_Qt : E.eq Pt Qt)
    by (etransitivity; [exact Hinv1 | exact Hinvinv]).
  assert (Hcoords : E.coordinates Pt = E.coordinates Qt)
    by (unfold Pt, Qt, E.coordinates;
        destruct HPt_Qt as [Hx' Hy']; simpl in *; congruence).
  unfold Pt, Qt, E.coordinates in Hcoords.
  inversion Hcoords; subst.
  reflexivity.
Qed.

(* === order-4 encoder-invariance scaffolding === *)

(* abs collapses sign: equal squares -> equal abs. *)
Lemma abs_eq_of_sq : forall (a b : Fp), (a * a)%F = (b * b)%F -> abs a = abs b.
Proof.
  intros a b H.
  assert (Hfac : ((a - b) * (a + b))%F = Fzero)
    by (assert (Hr : ((a - b) * (a + b))%F = (a*a - b*b)%F) by field;
        rewrite Hr, H; field).
  apply mul_zero_factor in Hfac. destruct Hfac as [Hd | Hd].
  - assert (a = b) by (apply sub_eq_zero; exact Hd). subst. reflexivity.
  - assert (a = F.opp b) by (apply add_eq_zero; exact Hd). subst. apply abs_opp.
Qed.

(** ** The "Hamburg flip" rotation invariance, parameterised by a square
    root of [-1] (so it covers BOTH order-4 cosets via [c = SQRT_M1] and
    [c = -SQRT_M1]).  For [(x,y)] on the curve, the rotated representative
    [(c*y, c*x)] (with [c^2 = -1]) encodes to the same field element [s].

    KEY STRUCTURE (documented for the reader):
      LHS sqrt_ratio argument  uL := (1 + c*x)(1 - c*x) * (c*y*(c*x))^2
                                   = (1 + x^2) * (x*y)^2     [since c^2=-1]
      RHS sqrt_ratio argument  uR := (1 + y)(1 - y) * (x*y)^2
                                   = (1 - y^2) * (x*y)^2
    These differ by the factor (1+x^2)/(1-y^2); on the curve (a=-1)
      1+x^2 = y^2(1 - d x^2),  1-y^2 = -x^2(1 + d y^2).
    The two [invsqrt] values are genuinely different, but the encoder's
    [rotate] branch + the [INVSQRT_A_MINUS_D] constant select the same [s].
    We close it by reducing [s] to [abs] of a value whose SQUARE matches on
    both sides (via [abs_eq_of_sq]) after resolving the rotate/sign branches
    with [sqrt_ratio_m1_correct]. *)

Lemma mul_cancel_l : forall (a x y : Fp), a <> Fzero -> (a * x)%F = (a * y)%F -> x = y.
Proof.
  intros a x y Ha H.
  assert (Hd : (a * (x - y))%F = Fzero)
    by (replace (a * (x - y))%F with ((a * x) - (a * y))%F by field; rewrite H; field).
  apply mul_zero_factor in Hd. destruct Hd as [Hd | Hd].
  - exfalso. apply Ha. exact Hd.
  - apply sub_eq_zero. exact Hd.
Qed.

(* On the curve, 1 + Qx^2 = Qy^2 (1 - d Qx^2) is nonzero: if it were 0 then
   d would be a square (= 1/Qx^2), contradicting nonsquare_d. *)
Lemma PL_nonzero : forall (Qx Qy : Fp),
  (Curve25519.E.a * (Qx * Qx) + Qy * Qy =
   Fone + Curve25519.E.d * (Qx * Qx) * (Qy * Qy))%F ->
  Qx <> Fzero -> Qy <> Fzero ->
  (Fone + Qx * Qx)%F <> Fzero.
Proof.
  intros Qx Qy HQ HQxnz HQynz.
  Opaque Curve25519.E.d.
  assert (Ha : (Curve25519.E.a : Fp) = F.opp Fone)
    by (unfold Curve25519.E.a; apply ModularArithmeticTheorems.F.eq_to_Z_iff;
        vm_compute; reflexivity).
  assert (Hd : (Curve25519.E.d*(Qx*Qx)*(Qy*Qy))%F = (Qy*Qy - Qx*Qx - Fone)%F)
    by (assert (Hr : (Curve25519.E.d*(Qx*Qx)*(Qy*Qy))%F
               = ((Fone + Curve25519.E.d*(Qx*Qx)*(Qy*Qy)) - Fone)%F) by field;
        rewrite Hr; rewrite Ha in HQ;
        assert (HQc : (Qy*Qy - Qx*Qx)%F = (Fone + Curve25519.E.d*(Qx*Qx)*(Qy*Qy))%F)
          by (assert (Hr2 : (Qy*Qy - Qx*Qx)%F = (F.opp Fone*(Qx*Qx) + Qy*Qy)%F) by field;
              rewrite Hr2; exact HQ);
        rewrite <- HQc; field).
  assert (HPLfac : (Fone + Qx*Qx)%F = (Qy*Qy*(Fone - Curve25519.E.d*(Qx*Qx)))%F)
    by (assert (Hr : (Qy*Qy*(Fone - Curve25519.E.d*(Qx*Qx)))%F
               = (Qy*Qy - Curve25519.E.d*(Qx*Qx)*(Qy*Qy))%F) by field;
        rewrite Hr, Hd; field).
  rewrite HPLfac. intro Hc. apply mul_zero_factor in Hc. destruct Hc as [Hc | Hc].
  - apply mul_zero_factor in Hc. destruct Hc; apply HQynz; assumption.
  - apply (Curve25519.E.nonsquare_d (F.inv Qx)).
    assert (Hdq : (Curve25519.E.d * (Qx*Qx))%F = Fone)
      by (symmetry; apply sub_eq_zero; exact Hc).
    apply (mul_cancel_l (Qx*Qx)%F);
      [ intro Hqq; apply mul_zero_factor in Hqq; destruct Hqq; apply HQxnz; assumption | ].
    transitivity (Fone:Fp); [ field; exact HQxnz | rewrite <- Hdq; field ].
Qed.

(* Symmetric: 1 - Qy^2 = -Qx^2 (1 + d Qy^2) is nonzero: if 0 then d = -1/Qy^2,
   so (i/Qy)^2 = d, contradicting nonsquare_d. *)
Lemma vR_nonzero : forall (Qx Qy : Fp),
  (Curve25519.E.a * (Qx * Qx) + Qy * Qy =
   Fone + Curve25519.E.d * (Qx * Qx) * (Qy * Qy))%F ->
  Qx <> Fzero -> Qy <> Fzero ->
  ((Fone + Qy) * (Fone - Qy))%F <> Fzero.
Proof.
  intros Qx Qy HQ HQxnz HQynz.
  Opaque Curve25519.E.d.
  assert (Ha : (Curve25519.E.a : Fp) = F.opp Fone)
    by (unfold Curve25519.E.a; apply ModularArithmeticTheorems.F.eq_to_Z_iff;
        vm_compute; reflexivity).
  assert (Hd : (Curve25519.E.d*(Qx*Qx)*(Qy*Qy))%F = (Qy*Qy - Qx*Qx - Fone)%F)
    by (assert (Hr : (Curve25519.E.d*(Qx*Qx)*(Qy*Qy))%F
               = ((Fone + Curve25519.E.d*(Qx*Qx)*(Qy*Qy)) - Fone)%F) by field;
        rewrite Hr; rewrite Ha in HQ;
        assert (HQc : (Qy*Qy - Qx*Qx)%F = (Fone + Curve25519.E.d*(Qx*Qx)*(Qy*Qy))%F)
          by (assert (Hr2 : (Qy*Qy - Qx*Qx)%F = (F.opp Fone*(Qx*Qx) + Qy*Qy)%F) by field;
              rewrite Hr2; exact HQ);
        rewrite <- HQc; field).
  assert (HvRfac : ((Fone + Qy) * (Fone - Qy))%F
                 = (F.opp (Qx*Qx) * (Fone + Curve25519.E.d*(Qy*Qy)))%F)
    by (assert (Hr : ((Fone + Qy) * (Fone - Qy))%F = (Fone - Qy*Qy)%F) by field;
        rewrite Hr;
        assert (Hr2 : (F.opp (Qx*Qx) * (Fone + Curve25519.E.d*(Qy*Qy)))%F
               = (F.opp (Qx*Qx) - Curve25519.E.d*(Qx*Qx)*(Qy*Qy))%F) by field;
        rewrite Hr2, Hd; field).
  rewrite HvRfac. intro Hc. apply mul_zero_factor in Hc. destruct Hc as [Hc | Hc].
  - assert (Hqq : (Qx*Qx)%F = Fzero)
      by (assert (Hr : (Qx*Qx)%F = F.opp (F.opp (Qx*Qx))) by field; rewrite Hr, Hc; field).
    apply mul_zero_factor in Hqq; destruct Hqq; apply HQxnz; assumption.
  - apply (Curve25519.E.nonsquare_d (F.inv Qy * SQRT_M1)).
    assert (Hdq : (Curve25519.E.d * (Qy*Qy))%F = F.opp Fone)
      by (transitivity ((Fone + Curve25519.E.d*(Qy*Qy)) - Fone)%F; [ field | rewrite Hc; field ]).
    apply (mul_cancel_l (Qy*Qy)%F);
      [ intro Hqq; apply mul_zero_factor in Hqq; destruct Hqq; apply HQynz; assumption | ].
    transitivity (F.opp Fone : Fp);
      [ transitivity (SQRT_M1 * SQRT_M1)%F; [ field; exact HQynz | exact SQRT_M1_sq ]
      | rewrite <- Hdq; field ].
Qed.

Transparent Curve25519.E.d.

Lemma negone_odd_pow : forall k:N, ((F.opp Fone : Fp) ^ (2*k+1))%F = F.opp Fone.
Proof.
  intro k. rewrite F.pow_add_r, F.pow_1_r, <- (F.pow_pow_l (F.opp Fone : Fp) 2 k).
  rewrite F.pow_2_r.
  assert (Hoo : (F.opp Fone * F.opp Fone)%F = (Fone:Fp))
    by (apply ModularArithmeticTheorems.F.eq_to_Z_iff; vm_compute; reflexivity).
  rewrite Hoo.
  assert (Hpk : (Fone:Fp) ^ k = Fone)
    by (etransitivity; [ apply F.pow_1_l | reflexivity ]).
  rewrite Hpk. apply Hierarchy.left_identity.
Qed.

(** [SQRT_M1] is a quadratic non-residue mod [p = 2^255-19].
    By Euler's criterion, if [SQRT_M1] were a square then
    [SQRT_M1 ^ ((p-1)/2) = 1]; but [(p-1)/2 = 2*(2^253-5)], so
    [SQRT_M1 ^ ((p-1)/2) = (SQRT_M1^2)^(2^253-5) = (-1)^(2^253-5) = -1]
    since [2^253-5] is odd, contradicting [1 <> -1]. *)
Lemma SQRT_M1_nonsquare : ~ (exists b:Fp, (b*b)%F = SQRT_M1).
Proof.
  intros [b Hb].
  pose proof (@F.euler_criterion (2^255-19)%positive prime_p ltac:(Decidable.vm_decide)
              SQRT_M1 SQRT_M1_nz) as Heuler.
  assert (Hsq : (SQRT_M1 ^ Z.to_N ((2^255-19) / 2))%F = Fone)
    by (apply Heuler; exists b; exact Hb).
  assert (Hexp : Z.to_N ((2^255-19) / 2) = (2 * (2^253 - 5))%N)
    by (vm_compute; reflexivity).
  rewrite Hexp in Hsq.
  rewrite <- (F.pow_pow_l SQRT_M1 2 (2^253-5)) in Hsq.
  rewrite F.pow_2_r, SQRT_M1_sq in Hsq.
  assert (Hodd : (2^253-5)%N = (2 * (2^252 - 3) + 1)%N) by (vm_compute; reflexivity).
  rewrite Hodd in Hsq. rewrite negone_odd_pow in Hsq.
  apply one_ne_opp_one. symmetry. exact Hsq.
Qed.

Lemma encode_aux_rotate : forall (c Qx Qy : Fp),
  (c * c)%F = F.opp Fone ->
  (E.a * (Qx * Qx) + Qy * Qy =
   Fone + E.d * (Qx * Qx) * (Qy * Qy))%F ->
  ristretto_encode_aux (c * Qy) (c * Qx) Fone (c * Qy * (c * Qx))
  = ristretto_encode_aux Qx Qy Fone (Qx * Qy).
Proof.
  intros c Qx Qy Hc HQ.
  unfold ristretto_encode_aux.
  destruct (F.eq_dec (Qx * Qy)%F Fzero) as [Hxy0 | Hxynz].
  - (* DEGENERATE: Qx*Qy = 0.  Both sqrt args are 0, so invsqrt = 0 on each
       side, hence den_inv = 0 and both encodings collapse to [abs Fzero]. *)
    assert (HargL : ((Fone + c * Qx) * (Fone - c * Qx) *
                     (c * Qy * (c * Qx) * (c * Qy * (c * Qx))))%F = Fzero).
    { assert (Hr : (c * Qy * (c * Qx))%F = Fzero).
      { assert (He : (c * Qy * (c * Qx))%F = (c*c*(Qx*Qy))%F) by field.
        rewrite He, Hxy0. field. }
      rewrite Hr. field. }
    assert (HargR : ((Fone + Qy) * (Fone - Qy) * (Qx * Qy * (Qx * Qy)))%F = Fzero).
    { rewrite Hxy0. field. }
    rewrite HargL, HargR.
    assert (Hsr0 : snd (sqrt_ratio_m1 Fone Fzero) = Fzero).
    { unfold sqrt_ratio_m1. cbv zeta. cbn [snd].
      set (r0 := (Fone * (Fzero * Fzero * Fzero) *
        (Fone * (Fzero * Fzero * Fzero * (Fzero * Fzero * Fzero) * Fzero))
        ^ Z.to_N ((2 ^ 255 - 19 - 5) / 8))%F).
      assert (Hr0 : r0 = Fzero) by (unfold r0; field). rewrite Hr0.
      destruct (F.to_Z (Fzero * Fzero * Fzero) =? F.to_Z Fone)%Z;
        [ unfold abs; rewrite is_negative_zero; reflexivity
        | destruct (F.to_Z (Fzero * Fzero * Fzero) =? F.to_Z (F.opp Fone))%Z;
          [ assert (Hz : (Fzero * SQRT_M1)%F = Fzero) by field; rewrite Hz;
            unfold abs; rewrite is_negative_zero; reflexivity
          | destruct (F.to_Z (Fzero * Fzero * Fzero)
                       =? F.to_Z (F.opp (SQRT_M1 * Fone)))%Z;
            [ assert (Hz : (Fzero * SQRT_M1)%F = Fzero) by field; rewrite Hz;
              unfold abs; rewrite is_negative_zero; reflexivity
            | unfold abs; rewrite is_negative_zero; reflexivity ] ] ]. }
    destruct (sqrt_ratio_m1 Fone Fzero) as [bb invsqrt] eqn:Esr.
    cbn [snd] in Hsr0. subst invsqrt.
    transitivity (abs Fzero);
      [ f_equal;
        destruct (is_negative (c * Qy * (c * Qx) *
          (Fzero * ((Fone + c * Qx) * (Fone - c * Qx)) *
           (Fzero * (c * Qy * (c * Qx))) * (c * Qy * (c * Qx))))); field
      | symmetry; f_equal;
        destruct (is_negative (Qx * Qy *
          (Fzero * ((Fone + Qy) * (Fone - Qy)) * (Fzero * (Qx * Qy)) *
           (Qx * Qy)))); field ].
  - (* MAIN: Qx*Qy <> 0. *)
    assert (HQxnz : Qx <> Fzero). { intro H. apply Hxynz. rewrite H. field. }
    assert (HQynz : Qy <> Fzero). { intro H. apply Hxynz. rewrite H. field. }
    assert (Hcnz : c <> Fzero).
    { intro H. assert (Hbad : (c*c)%F = Fzero) by (rewrite H; field).
      rewrite Hc in Hbad. apply one_ne_opp_one.
      assert (Hr : (Fone:Fp) = F.opp (F.opp Fone)) by field.
      rewrite Hr at 1. rewrite Hbad. field. }
    assert (Hxy2nz : (Qx * Qy * (Qx * Qy))%F <> Fzero).
    { intro H. apply mul_zero_factor in H. destruct H; apply Hxynz; assumption. }
    assert (Hu1L_eq : ((Fone + c * Qx) * (Fone - c * Qx))%F = (Fone + Qx * Qx)%F).
    { assert (Hr : ((Fone + c * Qx) * (Fone - c * Qx))%F = (Fone - (c*c)*(Qx*Qx))%F)
        by field. rewrite Hr, Hc. field. }
    assert (HargL : ((Fone + c * Qx) * (Fone - c * Qx) *
                     (c * Qy * (c * Qx) * (c * Qy * (c * Qx))))%F <> Fzero).
    { rewrite Hu1L_eq. intro H. apply mul_zero_factor in H. destruct H as [H | H].
      { apply (PL_nonzero Qx Qy HQ HQxnz HQynz); exact H. }
      { apply Hxy2nz.
        assert (He : (c * Qy * (c * Qx) * (c * Qy * (c * Qx)))%F
                   = ((c*c)*(c*c)*(Qx * Qy * (Qx * Qy)))%F) by field.
        rewrite He, Hc in H.
        assert (Hr : (Qx * Qy * (Qx * Qy))%F
                   = (F.opp Fone * F.opp Fone * (Qx * Qy * (Qx * Qy)))%F) by field.
        rewrite Hr; exact H. } }
    assert (HargR : ((Fone + Qy) * (Fone - Qy) * (Qx * Qy * (Qx * Qy)))%F <> Fzero).
    { intro H. apply mul_zero_factor in H. destruct H as [H | H].
      { apply (vR_nonzero Qx Qy HQ HQxnz HQynz); exact H. }
      { apply Hxy2nz; exact H. } }
    pose proof (sqrt_ratio_m1_correct Fone _ HargL) as HL.
    destruct (sqrt_ratio_m1 Fone
      ((Fone + c * Qx) * (Fone - c * Qx) * (c * Qy * (c * Qx) * (c * Qy * (c * Qx)))))
      as [wsL iL] eqn:EL.
    pose proof (sqrt_ratio_m1_correct Fone _ HargR) as HR.
    destruct (sqrt_ratio_m1 Fone ((Fone + Qy) * (Fone - Qy) * (Qx * Qy * (Qx * Qy))))
      as [wsR iR] eqn:ER.
    destruct HL as [HLcase HLneg]. destruct HR as [HRcase HRneg].
    apply abs_eq_of_sq.
    set (eL := (c * Qy * (c * Qx))%F) in *.
    set (aL := ((Fone + c * Qx) * (Fone - c * Qx))%F) in *.
    set (aR := ((Fone + Qy) * (Fone - Qy))%F) in *.
    set (P := (Qx * Qy)%F) in *.
    assert (HeL : eL = F.opp P).
    { unfold eL, P.
      assert (Hr : (c * Qy * (c * Qx))%F = ((c*c)*(Qx*Qy))%F) by field.
      rewrite Hr, Hc. field. }
    set (zL := (eL * (iL * aL * (iL * eL) * eL))%F) in *.
    set (zR := (P * (iR * aR * (iR * P) * P))%F) in *.
    assert (HeLsq : (eL * eL)%F = (P * P)%F) by (rewrite HeL; field).
    assert (HzL_val : zL = (F.opp (aL * (eL * eL) * iL * iL) * P)%F).
    { unfold zL. rewrite HeL. field. }
    assert (HzR_val : zR = (aR * (P * P) * iR * iR * P)%F) by (unfold zR; field).
    (* Case-independent facts. *)
    assert (Ha : (E.a : Fp) = F.opp Fone)
      by (unfold E.a; apply ModularArithmeticTheorems.F.eq_to_Z_iff; vm_compute; reflexivity).
    assert (K2 : (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D * (E.a - E.d))%F = Fone)
      by (unfold INVSQRT_A_MINUS_D, E.a, E.d;
          apply ModularArithmeticTheorems.F.eq_to_Z_iff; vm_compute; reflexivity).
    assert (HaRnz : aR <> Fzero) by (intro Hk; apply HargR; rewrite Hk; field).
    assert (HaLnz : aL <> Fzero) by (intro Hk; apply HargL; rewrite Hk; field).
    assert (HaLaR : (aL * aR)%F = (P * P * (E.a - E.d))%F).
    { unfold aR, P. rewrite Ha in HQ |- *.
      assert (Hd : (E.d*(Qx*Qx)*(Qy*Qy))%F = (Qy*Qy - Qx*Qx - Fone)%F).
      { assert (Hr : (E.d*(Qx*Qx)*(Qy*Qy))%F
                   = ((Fone + E.d*(Qx*Qx)*(Qy*Qy)) - Fone)%F) by field.
        rewrite Hr.
        assert (HQc : (Qy*Qy - Qx*Qx)%F = (Fone + E.d*(Qx*Qx)*(Qy*Qy))%F).
        { assert (Hr2 : (Qy*Qy - Qx*Qx)%F = (F.opp Fone*(Qx*Qx) + Qy*Qy)%F) by field.
          rewrite Hr2. exact HQ. }
        rewrite <- HQc. field. }
      assert (Hr : ((Fone + Qx * Qx) * ((Fone + Qy) * (Fone - Qy)))%F
                 = (Fone + Qx*Qx - Qy*Qy - Qx*Qx*(Qy*Qy))%F) by field.
      change ((Fone + c * Qx) * (Fone - c * Qx))%F with aL. rewrite Hu1L_eq, Hr.
      assert (Hr3 : (Qx * Qy * (Qx * Qy) * (F.opp Fone - E.d))%F
                  = (F.opp (Qx*Qx*(Qy*Qy)) - E.d*(Qx*Qx)*(Qy*Qy))%F) by field.
      rewrite Hr3, Hd. field. }
    assert (Hcval : c = SQRT_M1 \/ c = F.opp SQRT_M1).
    { assert (Hfac : ((c - SQRT_M1) * (c + SQRT_M1))%F = Fzero).
      { assert (Hr : ((c - SQRT_M1) * (c + SQRT_M1))%F = (c*c - SQRT_M1*SQRT_M1)%F) by field.
        rewrite Hr, Hc, SQRT_M1_sq. field. }
      apply mul_zero_factor in Hfac. destruct Hfac as [H | H].
      { left. apply sub_eq_zero in H. exact H. }
      { right. assert (Hr2 : c = ((c + SQRT_M1) - SQRT_M1)%F) by field.
        rewrite Hr2, H. field. } }
    (* SQRT_M1 is itself a nonzero square root of -1; needed for sign-flip lemmas. *)
    assert (HSQ : (SQRT_M1 * SQRT_M1)%F = F.opp Fone) by exact SQRT_M1_sq.
    destruct HLcase as [[HwsL HsqL] | [HwsL HsqL]];
      destruct HRcase as [[HwsR HsqR] | [HwsR HsqR]].
    + (* wsL = true, wsR = true: zL = -P, zR = P. *)
      rewrite HsqL in HzL_val. rewrite HsqR in HzR_val.
      assert (HnzR : zR <> Fzero) by (rewrite HzR_val; intro Hk; apply Hxynz;
        assert (Hr : P = (Fone * P)%F) by field; rewrite Hr; exact Hk).
      assert (HsignL : is_negative zL = negb (is_negative zR)).
      { rewrite HzL_val, HzR_val. assert (He : (F.opp Fone * P)%F = F.opp (Fone * P)%F) by field.
        rewrite He. apply is_negative_opp_nonzero. rewrite <- HzR_val. exact HnzR. }
      rewrite HsignL.
      assert (HML : (iL * aL * (iL * eL) * eL)%F = Fone) by (rewrite <- HsqL; field).
      assert (HMR : (iR * aR * (iR * P) * P)%F = Fone) by (rewrite <- HsqR; field).
      rewrite HML, HMR.
      assert (Hmag : (iL * aL * INVSQRT_A_MINUS_D * (iL * aL * INVSQRT_A_MINUS_D))%F
                   = (iR * P * (iR * P))%F).
      { apply (mul_cancel_l aR _ _ HaRnz).
        transitivity ((aL * (eL * eL) * iL * iL)
          * (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D * (E.a - E.d)))%F.
        { rewrite HeLsq.
          assert (Hexp : (aR * (iL * aL * INVSQRT_A_MINUS_D * (iL * aL * INVSQRT_A_MINUS_D)))%F
            = ((aL * aR) * (aL * iL * iL) * (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D))%F) by field.
          rewrite Hexp, HaLaR. field. }
        { rewrite HsqL, K2.
          assert (Hr : (aR * (iR * P * (iR * P)))%F = (aR * (P * P) * iR * iR)%F) by field.
          rewrite Hr, HsqR. field. } }
      assert (Hmag2 : (iL * eL * (iL * eL))%F
                    = (iR * aR * INVSQRT_A_MINUS_D * (iR * aR * INVSQRT_A_MINUS_D))%F).
      { apply (mul_cancel_l aL _ _ HaLnz).
        transitivity ((aR * (P * P) * iR * iR)
          * (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D * (E.a - E.d)))%F.
        { rewrite HsqR, K2.
          assert (Hr : (aL * (iL * eL * (iL * eL)))%F = (aL * (eL * eL) * iL * iL)%F) by field.
          rewrite Hr, HsqL. field. }
        { assert (Hr : (aL * (iR * aR * INVSQRT_A_MINUS_D * (iR * aR * INVSQRT_A_MINUS_D)))%F
            = ((aL * aR) * (aR * iR * iR) * (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D))%F) by field.
          rewrite Hr, HaLaR.
          assert (Ht : (P * P * (E.a - E.d) * (aR * iR * iR)
                        * (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D))%F
            = ((aR * (P * P) * iR * iR)
               * (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D * (E.a - E.d)))%F) by field.
          rewrite Ht, HsqR. field. } }
      destruct (is_negative zR) eqn:EzR; simpl negb; cbn match.
      * (* zR negative: LHS no-rotate (iL*eL), RHS rotate (iR*aR*INVSQRT). *)
        assert (HF1 : (c * Qy * Fone)%F = (c * Qy)%F) by field.
        assert (HF2 : (Qy * SQRT_M1 * Fone)%F = (Qy * SQRT_M1)%F) by field.
        rewrite HF1, HF2.
        destruct Hcval as [Hcv | Hcv].
        { assert (HE1 : (c * Qy)%F = (Qy * SQRT_M1)%F) by (rewrite Hcv; field).
          assert (HE2 : (c * Qx)%F = (Qx * SQRT_M1)%F) by (rewrite Hcv; field).
          rewrite HE1, HE2.
          destruct (is_negative (Qy * SQRT_M1)); cbn match;
            [ set (S := (Fone - F.opp (Qx * SQRT_M1))%F) in *
            | set (S := (Fone - Qx * SQRT_M1)%F) in * ];
            (transitivity ((iL * eL * (iL * eL)) * (S * S))%F;
              [ field | rewrite Hmag2; field ]). }
        { assert (HE1 : (c * Qy)%F = F.opp (Qy * SQRT_M1)%F) by (rewrite Hcv; field).
          assert (HE2 : (c * Qx)%F = F.opp (Qx * SQRT_M1)%F) by (rewrite Hcv; field).
          rewrite HE1, HE2.
          assert (HQySnz : (Qy * SQRT_M1)%F <> Fzero)
            by (intro Hk; apply mul_zero_factor in Hk; destruct Hk as [Hk|Hk];
                [apply HQynz; exact Hk | apply SQRT_M1_nz; exact Hk]).
          rewrite (is_negative_opp_nonzero _ HQySnz).
          destruct (is_negative (Qy * SQRT_M1)); simpl negb; cbn match.
          { set (S := (Fone - F.opp (Qx * SQRT_M1))%F) in *.
            transitivity ((iL * eL * (iL * eL)) * (S * S))%F; [ field | rewrite Hmag2; field ]. }
          { assert (Hyy : (F.opp (F.opp (Qx * SQRT_M1)))%F = (Qx * SQRT_M1)%F) by field.
            rewrite Hyy. set (S := (Fone - Qx * SQRT_M1)%F) in *.
            transitivity ((iL * eL * (iL * eL)) * (S * S))%F; [ field | rewrite Hmag2; field ]. } }
      * (* zR not negative: LHS rotate (iL*aL*INVSQRT), RHS no-rotate (iR*P). *)
        assert (HF1 : (c * Qx * SQRT_M1 * Fone)%F = (c * Qx * SQRT_M1)%F) by field.
        assert (HF2 : (Qx * Fone)%F = Qx) by field.
        rewrite HF1, HF2.
        destruct Hcval as [Hcv | Hcv].
        { assert (HE1 : (c * Qx * SQRT_M1)%F = F.opp Qx) by (rewrite Hcv;
            assert (Hr : (SQRT_M1 * Qx * SQRT_M1)%F = ((SQRT_M1 * SQRT_M1) * Qx)%F) by field;
            rewrite Hr, SQRT_M1_sq; field).
          assert (HE2 : (c * Qy * SQRT_M1)%F = F.opp Qy) by (rewrite Hcv;
            assert (Hr : (SQRT_M1 * Qy * SQRT_M1)%F = ((SQRT_M1 * SQRT_M1) * Qy)%F) by field;
            rewrite Hr, SQRT_M1_sq; field).
          rewrite HE1, HE2.
          rewrite (is_negative_opp_nonzero _ HQxnz).
          destruct (is_negative Qx); simpl negb; cbn match.
          { set (S := (Fone - F.opp Qy)%F) in *.
            transitivity ((iL * aL * INVSQRT_A_MINUS_D * (iL * aL * INVSQRT_A_MINUS_D))
              * (S * S))%F; [ field | rewrite Hmag; field ]. }
          { assert (Hyy : (F.opp (F.opp Qy))%F = Qy) by field. rewrite Hyy.
            set (S := (Fone - Qy)%F) in *.
            transitivity ((iL * aL * INVSQRT_A_MINUS_D * (iL * aL * INVSQRT_A_MINUS_D))
              * (S * S))%F; [ field | rewrite Hmag; field ]. } }
        { assert (HE1 : (c * Qx * SQRT_M1)%F = Qx) by (rewrite Hcv;
            assert (Hr : (F.opp SQRT_M1 * Qx * SQRT_M1)%F = (F.opp (SQRT_M1 * SQRT_M1) * Qx)%F) by field;
            rewrite Hr, SQRT_M1_sq; field).
          assert (HE2 : (c * Qy * SQRT_M1)%F = Qy) by (rewrite Hcv;
            assert (Hr : (F.opp SQRT_M1 * Qy * SQRT_M1)%F = (F.opp (SQRT_M1 * SQRT_M1) * Qy)%F) by field;
            rewrite Hr, SQRT_M1_sq; field).
          rewrite HE1, HE2.
          destruct (is_negative Qx); cbn match;
            [ set (S := (Fone - F.opp Qy)%F) in *
            | set (S := (Fone - Qy)%F) in * ];
            (transitivity ((iL * aL * INVSQRT_A_MINUS_D * (iL * aL * INVSQRT_A_MINUS_D))
              * (S * S))%F; [ field | rewrite Hmag; field ]). }
    + (* wsL = true, wsR = false: VACUOUS.  From HsqL [aL*P^2*iL^2 = 1] and
         HsqR [aR*P^2*iR^2 = SQRT_M1], multiplying and using
         HaLaR [aL*aR = P^2*(E.a-E.d)] and K2 [INVSQRT^2*(E.a-E.d) = 1] gives
         (P^3*iL*iR*F.inv INVSQRT_A_MINUS_D)^2 = SQRT_M1, i.e. SQRT_M1 is a
         square, contradicting [SQRT_M1_nonsquare]. *)
      exfalso.
      assert (HInz : INVSQRT_A_MINUS_D <> Fzero)
        by (unfold INVSQRT_A_MINUS_D; Decidable.vm_decide).
      apply SQRT_M1_nonsquare.
      exists (F.inv INVSQRT_A_MINUS_D * (P * P * P) * iL * iR)%F.
      set (X := ((P*P*P*iL*iR) * (P*P*P*iL*iR))%F).
      assert (HsqL' : (aL * (P * P) * iL * iL)%F = Fone)
        by (rewrite <- HeLsq; exact HsqL).
      assert (HsqR' : (aR * (P * P) * iR * iR)%F = SQRT_M1)
        by (rewrite HsqR; field).
      assert (Hpre : ((E.a - E.d) * X)%F = SQRT_M1).
      { transitivity ((aL * (P*P) * iL * iL) * (aR * (P*P) * iR * iR))%F.
        { assert (Hr : ((aL * (P*P) * iL * iL) * (aR * (P*P) * iR * iR))%F
                     = ((aL * aR) * ((P*P*iL*iR) * (P*P*iL*iR)))%F) by field.
          rewrite Hr, HaLaR. unfold X. field. }
        { rewrite HsqL', HsqR'. field. } }
      assert (HX : X = (SQRT_M1 * (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D))%F).
      { transitivity ((INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D * (E.a - E.d)) * X)%F.
        { rewrite K2. field. }
        { assert (Hr : (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D * (E.a - E.d) * X)%F
                     = (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D * ((E.a - E.d) * X))%F) by field.
          rewrite Hr, Hpre. field. } }
      transitivity (F.inv INVSQRT_A_MINUS_D * F.inv INVSQRT_A_MINUS_D * X)%F.
      * unfold X. field; exact HInz.
      * rewrite HX. field; exact HInz.
    + (* wsL = false, wsR = true: VACUOUS, symmetric to the previous
         (SQRT_M1 would be a square via P^3*iL*iR*F.inv INVSQRT_A_MINUS_D). *)
      exfalso.
      assert (HInz : INVSQRT_A_MINUS_D <> Fzero)
        by (unfold INVSQRT_A_MINUS_D; Decidable.vm_decide).
      apply SQRT_M1_nonsquare.
      exists (F.inv INVSQRT_A_MINUS_D * (P * P * P) * iL * iR)%F.
      set (X := ((P*P*P*iL*iR) * (P*P*P*iL*iR))%F).
      assert (HsqL' : (aL * (P * P) * iL * iL)%F = SQRT_M1)
        by (rewrite <- HeLsq, HsqL; field).
      assert (HsqR' : (aR * (P * P) * iR * iR)%F = Fone) by exact HsqR.
      assert (Hpre : ((E.a - E.d) * X)%F = SQRT_M1).
      { transitivity ((aL * (P*P) * iL * iL) * (aR * (P*P) * iR * iR))%F.
        { assert (Hr : ((aL * (P*P) * iL * iL) * (aR * (P*P) * iR * iR))%F
                     = ((aL * aR) * ((P*P*iL*iR) * (P*P*iL*iR)))%F) by field.
          rewrite Hr, HaLaR. unfold X. field. }
        { rewrite HsqL', HsqR'. field. } }
      assert (HX : X = (SQRT_M1 * (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D))%F).
      { transitivity ((INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D * (E.a - E.d)) * X)%F.
        { rewrite K2. field. }
        { assert (Hr : (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D * (E.a - E.d) * X)%F
                     = (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D * ((E.a - E.d) * X))%F) by field.
          rewrite Hr, Hpre. field. } }
      transitivity (F.inv INVSQRT_A_MINUS_D * F.inv INVSQRT_A_MINUS_D * X)%F.
      * unfold X. field; exact HInz.
      * rewrite HX. field; exact HInz.
    + (* wsL = false, wsR = false: zL = -SQRT_M1*P, zR = SQRT_M1*P. *)
      rewrite HsqL in HzL_val. rewrite HsqR in HzR_val.
      assert (HnzR : zR <> Fzero) by (rewrite HzR_val; intro Hk;
        apply mul_zero_factor in Hk; destruct Hk as [Hk|Hk];
        [ apply SQRT_M1_nz; assert (Hr : SQRT_M1 = (SQRT_M1*Fone)%F) by field;
          rewrite Hr; exact Hk | apply Hxynz; exact Hk ]).
      assert (HsignL : is_negative zL = negb (is_negative zR)).
      { rewrite HzL_val, HzR_val.
        assert (He : (F.opp (SQRT_M1 * Fone) * P)%F = F.opp (SQRT_M1 * Fone * P)%F) by field.
        rewrite He. apply is_negative_opp_nonzero. rewrite <- HzR_val. exact HnzR. }
      rewrite HsignL.
      assert (HML : (iL * aL * (iL * eL) * eL)%F = SQRT_M1)
        by (transitivity (SQRT_M1 * Fone)%F; [ rewrite <- HsqL; field | field ]).
      assert (HMR : (iR * aR * (iR * P) * P)%F = SQRT_M1)
        by (transitivity (SQRT_M1 * Fone)%F; [ rewrite <- HsqR; field | field ]).
      rewrite HML, HMR.
      assert (Hmag : (iL * aL * INVSQRT_A_MINUS_D * (iL * aL * INVSQRT_A_MINUS_D))%F
                   = (iR * P * (iR * P))%F).
      { apply (mul_cancel_l aR _ _ HaRnz).
        transitivity ((aL * (eL * eL) * iL * iL)
          * (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D * (E.a - E.d)))%F.
        { rewrite HeLsq.
          assert (Hexp : (aR * (iL * aL * INVSQRT_A_MINUS_D * (iL * aL * INVSQRT_A_MINUS_D)))%F
            = ((aL * aR) * (aL * iL * iL) * (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D))%F) by field.
          rewrite Hexp, HaLaR. field. }
        { rewrite HsqL, K2.
          assert (Hr : (aR * (iR * P * (iR * P)))%F = (aR * (P * P) * iR * iR)%F) by field.
          rewrite Hr, HsqR. field. } }
      assert (Hmag2 : (iL * eL * (iL * eL))%F
                    = (iR * aR * INVSQRT_A_MINUS_D * (iR * aR * INVSQRT_A_MINUS_D))%F).
      { apply (mul_cancel_l aL _ _ HaLnz).
        transitivity ((aR * (P * P) * iR * iR)
          * (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D * (E.a - E.d)))%F.
        { rewrite HsqR, K2.
          assert (Hr : (aL * (iL * eL * (iL * eL)))%F = (aL * (eL * eL) * iL * iL)%F) by field.
          rewrite Hr, HsqL. field. }
        { assert (Hr : (aL * (iR * aR * INVSQRT_A_MINUS_D * (iR * aR * INVSQRT_A_MINUS_D)))%F
            = ((aL * aR) * (aR * iR * iR) * (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D))%F) by field.
          rewrite Hr, HaLaR.
          assert (Ht : (P * P * (E.a - E.d) * (aR * iR * iR)
                        * (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D))%F
            = ((aR * (P * P) * iR * iR)
               * (INVSQRT_A_MINUS_D * INVSQRT_A_MINUS_D * (E.a - E.d)))%F) by field.
          rewrite Ht, HsqR. field. } }
      destruct (is_negative zR) eqn:EzR; simpl negb; cbn match.
      * (* zR negative: LHS no-rotate, RHS rotate; inner args carry an extra SQRT_M1. *)
        assert (HRA : (Qy * SQRT_M1 * SQRT_M1)%F = F.opp Qy)
          by (assert (Hr : (Qy * SQRT_M1 * SQRT_M1)%F = ((SQRT_M1 * SQRT_M1) * Qy)%F) by field;
              rewrite Hr, SQRT_M1_sq; field).
        rewrite HRA. rewrite (is_negative_opp_nonzero _ HQynz).
        destruct Hcval as [Hcv | Hcv].
        { assert (HLA : (c * Qy * SQRT_M1)%F = F.opp Qy) by (rewrite Hcv;
            assert (Hr : (SQRT_M1 * Qy * SQRT_M1)%F = ((SQRT_M1 * SQRT_M1) * Qy)%F) by field;
            rewrite Hr, SQRT_M1_sq; field).
          assert (HLB : (c * Qx)%F = (Qx * SQRT_M1)%F) by (rewrite Hcv; field).
          rewrite HLA, HLB. rewrite (is_negative_opp_nonzero _ HQynz).
          destruct (is_negative Qy); simpl negb; cbn match.
          { transitivity ((iL * eL * (iL * eL))
              * ((Fone - Qx * SQRT_M1) * (Fone - Qx * SQRT_M1)))%F;
              [ field | rewrite Hmag2; field ]. }
          { transitivity ((iL * eL * (iL * eL))
              * ((Fone - F.opp (Qx * SQRT_M1)) * (Fone - F.opp (Qx * SQRT_M1))))%F;
              [ field | rewrite Hmag2; field ]. } }
        { assert (HLA : (c * Qy * SQRT_M1)%F = Qy) by (rewrite Hcv;
            assert (Hr : (F.opp SQRT_M1 * Qy * SQRT_M1)%F = (F.opp (SQRT_M1 * SQRT_M1) * Qy)%F) by field;
            rewrite Hr, SQRT_M1_sq; field).
          assert (HLB : (c * Qx)%F = F.opp (Qx * SQRT_M1)%F) by (rewrite Hcv; field).
          rewrite HLA, HLB.
          destruct (is_negative Qy); simpl negb; cbn match.
          { assert (Hyy : (F.opp (F.opp (Qx * SQRT_M1)))%F = (Qx * SQRT_M1)%F) by field.
            rewrite Hyy.
            transitivity ((iL * eL * (iL * eL))
              * ((Fone - Qx * SQRT_M1) * (Fone - Qx * SQRT_M1)))%F;
              [ field | rewrite Hmag2; field ]. }
          { transitivity ((iL * eL * (iL * eL))
              * ((Fone - F.opp (Qx * SQRT_M1)) * (Fone - F.opp (Qx * SQRT_M1))))%F;
              [ field | rewrite Hmag2; field ]. } }
      * (* zR not negative: LHS rotate, RHS no-rotate. *)
        destruct Hcval as [Hcv | Hcv].
        { assert (HA : (c * Qx * SQRT_M1 * SQRT_M1)%F = F.opp (Qx * SQRT_M1)%F) by (rewrite Hcv;
            assert (Hr : (SQRT_M1 * Qx * SQRT_M1 * SQRT_M1)%F = (SQRT_M1 * (SQRT_M1 * SQRT_M1) * Qx)%F) by field;
            rewrite Hr, SQRT_M1_sq; field).
          assert (HB : (c * Qy * SQRT_M1)%F = F.opp Qy) by (rewrite Hcv;
            assert (Hr : (SQRT_M1 * Qy * SQRT_M1)%F = ((SQRT_M1 * SQRT_M1) * Qy)%F) by field;
            rewrite Hr, SQRT_M1_sq; field).
          rewrite HA, HB.
          assert (HQxSnz : (Qx * SQRT_M1)%F <> Fzero) by (intro Hk;
            apply mul_zero_factor in Hk; destruct Hk as [Hk|Hk];
            [apply HQxnz; exact Hk | apply SQRT_M1_nz; exact Hk]).
          rewrite (is_negative_opp_nonzero _ HQxSnz).
          destruct (is_negative (Qx * SQRT_M1)); simpl negb; cbn match.
          { transitivity ((iL * aL * INVSQRT_A_MINUS_D * (iL * aL * INVSQRT_A_MINUS_D))
              * ((Fone - F.opp Qy) * (Fone - F.opp Qy)))%F; [ field | rewrite Hmag; field ]. }
          { assert (Hyy : (F.opp (F.opp Qy))%F = Qy) by field. rewrite Hyy.
            transitivity ((iL * aL * INVSQRT_A_MINUS_D * (iL * aL * INVSQRT_A_MINUS_D))
              * ((Fone - Qy) * (Fone - Qy)))%F; [ field | rewrite Hmag; field ]. } }
        { assert (HA : (c * Qx * SQRT_M1 * SQRT_M1)%F = (Qx * SQRT_M1)%F) by (rewrite Hcv;
            assert (Hr : (F.opp SQRT_M1 * Qx * SQRT_M1 * SQRT_M1)%F = (F.opp (SQRT_M1 * (SQRT_M1 * SQRT_M1)) * Qx)%F) by field;
            rewrite Hr, SQRT_M1_sq; field).
          assert (HB : (c * Qy * SQRT_M1)%F = Qy) by (rewrite Hcv;
            assert (Hr : (F.opp SQRT_M1 * Qy * SQRT_M1)%F = (F.opp (SQRT_M1 * SQRT_M1) * Qy)%F) by field;
            rewrite Hr, SQRT_M1_sq; field).
          rewrite HA, HB.
          destruct (is_negative (Qx * SQRT_M1)); cbn match.
          { transitivity ((iL * aL * INVSQRT_A_MINUS_D * (iL * aL * INVSQRT_A_MINUS_D))
              * ((Fone - F.opp Qy) * (Fone - F.opp Qy)))%F; [ field | rewrite Hmag; field ]. }
          { transitivity ((iL * aL * INVSQRT_A_MINUS_D * (iL * aL * INVSQRT_A_MINUS_D))
              * ((Fone - Qy) * (Fone - Qy)))%F; [ field | rewrite Hmag; field ]. } }
Qed.

Opaque Curve25519.E.d.

Lemma canonical_rep_case_order4_pos :
  forall (Px Py Qx Qy : Fp),
    (Curve25519.E.a * (Px * Px) + Py * Py =
     Fone + Curve25519.E.d * (Px * Px) * (Py * Py))%F ->
    (Curve25519.E.a * (Qx * Qx) + Qy * Qy =
     Fone + Curve25519.E.d * (Qx * Qx) * (Qy * Qy))%F ->
    sub_affine_x (Px, Py) (Qx, Qy) = SQRT_M1 ->
    sub_affine_y (Px, Py) (Qx, Qy) = Fzero ->
    ristretto_encode_bytes (to_extended (Px, Py))
    = ristretto_encode_bytes (to_extended (Qx, Qy)).
Proof.
  Opaque SQRT_M1 Curve25519.E.d.
  intros Px Py Qx Qy HP HQ Hx Hy.
  pose (Pt := exist (fun xy => let '(x, y) := xy in
    (Curve25519.E.a*(x*x) + y*y = Fone + Curve25519.E.d*(x*x)*(y*y))%F)
    (Px, Py) HP : Curve25519.E.point).
  pose (Qt := exist (fun xy => let '(x, y) := xy in
    (Curve25519.E.a*(x*x) + y*y = Fone + Curve25519.E.d*(x*x)*(y*y))%F)
    (Qx, Qy) HQ : Curve25519.E.point).
  pose (Qopp := @AffineProofs.E.opp _ _ _ _ F.opp F.add F.sub F.mul _ _
    Curve25519.field _ Curve25519.E.a Curve25519.E.d
    Curve25519.E.nonzero_a Qt).
  pose (D := Curve25519.E.add Pt Qopp).
  assert (Hcoord_D : E.coordinates D
                     = (sub_affine_x (Px, Py) (Qx, Qy),
                        sub_affine_y (Px, Py) (Qx, Qy)))
    by reflexivity.
  rewrite Hx, Hy in Hcoord_D.
  assert (HT4 : (Curve25519.E.a * (SQRT_M1 * SQRT_M1) + Fzero * Fzero
                 = Fone + Curve25519.E.d * (SQRT_M1 * SQRT_M1)
                          * (Fzero * Fzero))%F).
  { Transparent SQRT_M1 Curve25519.E.d.
    unfold Curve25519.E.a, Curve25519.E.d, SQRT_M1; Decidable.vm_decide. }
  Opaque SQRT_M1 Curve25519.E.d.
  pose (T4 := exist (fun xy => let '(x, y) := xy in
    (Curve25519.E.a*(x*x) + y*y = Fone + Curve25519.E.d*(x*x)*(y*y))%F)
    (SQRT_M1, Fzero) HT4 : Curve25519.E.point).
  assert (HD_T4 : E.eq D T4).
  1:unfold E.eq, T4; rewrite Hcoord_D; simpl; split; reflexivity.
  pose proof (@AffineProofs.E.edwards_curve_commutative_group _ _ _ _
                F.opp F.add F.sub F.mul _ _
                Curve25519.field Curve25519.char_ge_3 _
                Curve25519.E.a Curve25519.E.d
                Curve25519.E.nonzero_a
                Curve25519.E.square_a
                Curve25519.E.nonsquare_d) as Hgrp.
  assert (HPt_eq : E.eq Pt (Curve25519.E.add T4 Qt)).
  1:rewrite <- HD_T4; unfold D, Qopp;
    rewrite <- (associative Pt (E.opp Qt) Qt);
    rewrite (left_inverse Qt); rewrite (right_identity Pt); reflexivity.
  assert (HT4Qt_coord : E.coordinates (Curve25519.E.add T4 Qt)
                       = (SQRT_M1 * Qy, SQRT_M1 * Qx)%F).
  { unfold Curve25519.E.add, E.add, T4, Qt, E.coordinates; cbv [fst snd].
    apply pair_equal_spec. split.
    - field. Decidable.vm_decide.
    - unfold Curve25519.E.a. field. Decidable.vm_decide. }
  assert (HPxy : (Px, Py) = (SQRT_M1 * Qy, SQRT_M1 * Qx)%F).
  1:rewrite <- HT4Qt_coord;
    destruct HPt_eq as [Hx' Hy'];
    unfold Pt, E.coordinates in Hx', Hy';
    destruct (E.coordinates (Curve25519.E.add T4 Qt)) as [x2 y2] eqn:E;
    injection (eq_sym (E : E.coordinates _ = _)) as Hcx Hcy;
    subst x2 y2; cbn in Hx', Hy'; subst; reflexivity.
  inversion HPxy as [[HPx HPy]]. subst Px Py.
  Transparent SQRT_M1 Curve25519.E.d.
  unfold ristretto_encode_bytes, ristretto_encode, to_extended.
  f_equal.
  (* The remaining encoder-invariance goal is exactly the "Hamburg flip"
     [encode_aux_rotate] with [c := SQRT_M1] (so [c^2 = -1] is [SQRT_M1_sq]). *)
  apply (encode_aux_rotate SQRT_M1 Qx Qy SQRT_M1_sq HQ).
Qed.

Lemma canonical_rep_case_order4_neg :
  forall (Px Py Qx Qy : Fp),
    (Curve25519.E.a * (Px * Px) + Py * Py =
     Fone + Curve25519.E.d * (Px * Px) * (Py * Py))%F ->
    (Curve25519.E.a * (Qx * Qx) + Qy * Qy =
     Fone + Curve25519.E.d * (Qx * Qx) * (Qy * Qy))%F ->
    sub_affine_x (Px, Py) (Qx, Qy) = F.opp SQRT_M1 ->
    sub_affine_y (Px, Py) (Qx, Qy) = Fzero ->
    ristretto_encode_bytes (to_extended (Px, Py))
    = ristretto_encode_bytes (to_extended (Qx, Qy)).
Proof.
  Opaque SQRT_M1 Curve25519.E.d.
  intros Px Py Qx Qy HP HQ Hx Hy.
  pose (Pt := exist (fun xy => let '(x, y) := xy in
    (Curve25519.E.a*(x*x) + y*y = Fone + Curve25519.E.d*(x*x)*(y*y))%F)
    (Px, Py) HP : Curve25519.E.point).
  pose (Qt := exist (fun xy => let '(x, y) := xy in
    (Curve25519.E.a*(x*x) + y*y = Fone + Curve25519.E.d*(x*x)*(y*y))%F)
    (Qx, Qy) HQ : Curve25519.E.point).
  pose (Qopp := @AffineProofs.E.opp _ _ _ _ F.opp F.add F.sub F.mul _ _
    Curve25519.field _ Curve25519.E.a Curve25519.E.d
    Curve25519.E.nonzero_a Qt).
  pose (D := Curve25519.E.add Pt Qopp).
  assert (Hcoord_D : E.coordinates D
                     = (sub_affine_x (Px, Py) (Qx, Qy),
                        sub_affine_y (Px, Py) (Qx, Qy)))
    by reflexivity.
  rewrite Hx, Hy in Hcoord_D.
  assert (HT4n : (Curve25519.E.a * (F.opp SQRT_M1 * F.opp SQRT_M1) + Fzero * Fzero
                  = Fone + Curve25519.E.d * (F.opp SQRT_M1 * F.opp SQRT_M1)
                           * (Fzero * Fzero))%F).
  { Transparent SQRT_M1 Curve25519.E.d.
    unfold Curve25519.E.a, Curve25519.E.d, SQRT_M1; Decidable.vm_decide. }
  Opaque SQRT_M1 Curve25519.E.d.
  pose (T4n := exist (fun xy => let '(x, y) := xy in
    (Curve25519.E.a*(x*x) + y*y = Fone + Curve25519.E.d*(x*x)*(y*y))%F)
    (F.opp SQRT_M1, Fzero) HT4n : Curve25519.E.point).
  assert (HD_T4n : E.eq D T4n).
  1:unfold E.eq, T4n; rewrite Hcoord_D; simpl; split; reflexivity.
  pose proof (@AffineProofs.E.edwards_curve_commutative_group _ _ _ _
                F.opp F.add F.sub F.mul _ _
                Curve25519.field Curve25519.char_ge_3 _
                Curve25519.E.a Curve25519.E.d
                Curve25519.E.nonzero_a
                Curve25519.E.square_a
                Curve25519.E.nonsquare_d) as Hgrp.
  assert (HPt_eq : E.eq Pt (Curve25519.E.add T4n Qt)).
  1:rewrite <- HD_T4n; unfold D, Qopp;
    rewrite <- (associative Pt (E.opp Qt) Qt);
    rewrite (left_inverse Qt); rewrite (right_identity Pt); reflexivity.
  assert (HT4nQt_coord : E.coordinates (Curve25519.E.add T4n Qt)
                       = (F.opp SQRT_M1 * Qy, F.opp SQRT_M1 * Qx)%F).
  { unfold Curve25519.E.add, E.add, T4n, Qt, E.coordinates; cbv [fst snd].
    apply pair_equal_spec. split.
    - field. Decidable.vm_decide.
    - unfold Curve25519.E.a. field. Decidable.vm_decide. }
  assert (HPxy : (Px, Py) = (F.opp SQRT_M1 * Qy, F.opp SQRT_M1 * Qx)%F).
  1:rewrite <- HT4nQt_coord;
    destruct HPt_eq as [Hx' Hy'];
    unfold Pt, E.coordinates in Hx', Hy';
    destruct (E.coordinates (Curve25519.E.add T4n Qt)) as [x2 y2] eqn:E;
    injection (eq_sym (E : E.coordinates _ = _)) as Hcx Hcy;
    subst x2 y2; cbn in Hx', Hy'; subst; reflexivity.
  inversion HPxy as [[HPx HPy]]. subst Px Py.
  Transparent SQRT_M1 Curve25519.E.d.
  unfold ristretto_encode_bytes, ristretto_encode, to_extended.
  f_equal.
  (* Mirror of order4_pos: the Hamburg flip [encode_aux_rotate] with
     [c := -SQRT_M1].  The hypothesis [c^2 = -1] holds because
     [(-i)*(-i) = i*i = -1]. *)
  assert (Hcc : (F.opp SQRT_M1 * F.opp SQRT_M1)%F = F.opp Fone)
    by (rewrite opp_mul_opp; exact SQRT_M1_sq).
  apply (encode_aux_rotate (F.opp SQRT_M1) Qx Qy Hcc HQ).
Qed.
