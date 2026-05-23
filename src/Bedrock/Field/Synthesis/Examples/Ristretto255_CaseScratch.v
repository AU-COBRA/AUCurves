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
  (* Remaining encoder-invariance goal (the "Hamburg flip"):
       ristretto_encode_aux (SQRT_M1*Qy) (SQRT_M1*Qx) Fone (SQRT_M1*Qy*(SQRT_M1*Qx))
       = ristretto_encode_aux Qx Qy Fone (Qx*Qy)
     The two sqrt_ratio_m1 arguments are
       LHS = (Fone + Qx^2) * (Qx*Qy)^2   [since (1+i*Qx)(1-i*Qx) = 1 - i^2 Qx^2]
       RHS = (Fone - Qy^2) * (Qx*Qy)^2
     which are NOT a clean scalar multiple of one another; the relation
     between (1+Qx^2) and (1-Qy^2) goes through the curve equation HQ and
     the constant INVSQRT_A_MINUS_D = 1/sqrt(a-d).  Closing this requires
     [sqrt_ratio_m1_correct] (PROVEN in Ristretto255_Sqrt.v) plus a full
     rotate-branch case analysis.  Left ADMITTED. *)
Admitted.

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
  (* Mirror of order4_pos with SQRT_M1 -> -SQRT_M1.  Same Hamburg-flip
     encoder-invariance goal; relies on [sqrt_ratio_m1_correct] and the
     rotate/Y-negate branch analysis.  Left ADMITTED. *)
Admitted.
