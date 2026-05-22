(** * Ristretto255_TorsionCases — the four 4-torsion case lemmas split
      out of [Ristretto255_RoundTrip.v] so the file is reachable through
      MCP (RoundTrip.v hits the 600s PET load timeout, and a full dune
      compile of RoundTrip.v ran 60+ min without completing).

    See the parent file's PROGRESS block for the geometric content.
    These are the four cases of [is_4torsion_affine] that combine into
    [canonical_rep_selection] (encoder is invariant on E[4]-cosets).

    PROGRESS (2026-05-22):

    Loadable via MCP (verified: rocq_start succeeds in <30s).
    Tried [fsatz] on the simplest case (identity) and it TIMES OUT — the
    [nsatz_compute] step chokes on the concrete value of
    [Curve25519.E.d = F.div (F.opp 121665) 121666].  The abstract
    Edwards proofs in [fiat-crypto/src/Curves/Edwards/AffineProofs.v]
    succeed with [fsatz] because they treat [d] as a parameter; once
    you specialise to the concrete d, the polynomial system explodes.

    Correct approach (sketch, ~200-400 LoC):
      - Lift (Px, Py) and (Qx, Qy) to typed [Curve25519.E.point] via
        [exist _ (Px, Py) HP] (HP is the on-curve hypothesis).
      - Use [edwards_curve_commutative_group] (Qed in AffineProofs.v)
        to obtain group cancellation: [P + (-Q) = 0 ⟹ P = Q]
        (as [E.eq], which is coordinate-wise equality).
      - Apply [Proper_coordinates] to extract [Px = Qx /\ Py = Qy]
        from [E.eq P Q].
      - Substitute into [ristretto_encode_bytes (to_extended _)] by
        [f_equal].

    For [order2] / [order4_pos] / [order4_neg], the sub_affine result
    is non-identity 4-torsion.  Strategy: explicit coordinate-flip
    relationships:
      - order2:    Q = (-Px, -Py)        (encoder invariant under negate-both)
      - order4_*:  Q = (sign·Py·SQRT_M1, Px·SQRT_M1) (Hamburg rotate)
    Each then proves [ristretto_encode_aux ...] congruence by
    destructing the [rotate]/sign branches and showing each branch
    matches its partner under the coordinate flip.
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import micromega.Lia.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Algebra.Hierarchy.
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

(** Make the Curve25519 field instance available locally, plus register
    a stdlib [Field] structure for the [field] tactic.  Avoids the
    [field_simplify_eq] timeout on the concrete value of
    [Curve25519.E.d] when only small coefficients appear in the
    numerator / denominator. *)
Local Existing Instance Curve25519.field.
Local Existing Instance Curve25519.char_ge_3.

Add Field _curve25519_field_local :
  (Algebra.Field.field_theory_for_stdlib_tactic(T:=F (2^255-19)%positive))
  (morphism (F.ring_morph (2^255-19)%positive),
   constants [F.is_constant],
   div (F.morph_div_theory (2^255-19)%positive),
   power_tac (F.power_theory (2^255-19)%positive) [F.is_pow_constant]).

(* === replicated from Ristretto255_RoundTrip.v so this file is self-contained === *)

Definition to_extended (xy : Fp * Fp) : Fp * Fp * Fp * Fp :=
  let '(x, y) := xy in (x, y, Fone, (x * y)%F).

Definition is_4torsion_affine (xy : Fp * Fp) : Prop :=
  let '(x, y) := xy in
     (x = Fzero /\ y = Fone)
  \/ (x = Fzero /\ y = F.opp Fone)
  \/ (x = SQRT_M1 /\ y = Fzero)
  \/ (x = F.opp SQRT_M1 /\ y = Fzero).

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

(* === case lemmas === *)

(** ** Identity case — sub_affine P Q = (0, 1) ⇒ Px = Qx ∧ Py = Qy.

    Proof strategy: lift (Px, Py) and (Qx, Qy) to typed E.point values
    [Pt] and [Qt].  Form [D := Pt + (-Qt)] via [Curve25519.E.add].  The
    hypotheses give [coordinates D = (0, 1) = coordinates E.zero], so
    [E.eq D E.zero].  By group cancellation ([inv_unique] + [inv_inv]),
    [Pt = Qt] as [E.eq] (= coordinate-wise on Curve25519), so
    [Px = Qx /\ Py = Qy], and the encoder agrees by [reflexivity]. *)
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

(** ** Order-2 case — sub_affine P Q = (0, -1) ⇒ Qx = -Px, Qy = -Py.

    Algebraic-cancellation half (PROVEN below): lift to typed points,
    show [E.eq D T2] where [T2 := (0, -1)] is the order-2 torsion
    element, rearrange to [Pt = T2 + Qt], compute [T2 + Qt] coordinates
    via [field] to get [(Px, Py) = (-Qx, -Qy)].

    Encoder-invariance half (ADMITTED): after substituting [Px = -Qx],
    [Py = -Qy], the residual goal reduces to encoder invariance under
    [(X,Y) ↦ (-X,-Y)] (keeping [Z=1], [T=X*Y]).  In the [u1, u2] and
    derived [invsqrt, den1, den2, z_inv, rotate] computations the
    sign flips cancel.  In the [ix0, iy0, X', Y0, Y'] dispatch
    chain, the sign flip propagates through three nested
    [is_negative] tests; correctness rests on
      [Lemma is_negative_opp_nonzero : forall s,
          s <> Fzero -> is_negative (F.opp s) = negb (is_negative s)]
    (uses oddness of [p = 2^255-19]), plus the observation that when
    the inner [X' * z_inv = 0] we always have [den_inv = 0] (forces
    output = 0). *)
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
  (* Algebraic-cancellation half (PROVEN). *)
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
  (* Encoder-invariance half (ADMITTED) — see header note. *)
Admitted.

(** ** Order-4 positive case — sub_affine P Q = (SQRT_M1, 0) ⇒
    Px = SQRT_M1*Qy, Py = SQRT_M1*Qx.

    Same algebraic-cancellation/encoder-invariance split as order2.
    [T4 := (SQRT_M1, 0)] is on the curve because [a*SQRT_M1^2 = 1]
    (a = -1 and SQRT_M1^2 = -1).  The coordinate computation gives
    the "Hamburg flip" formulas (Decaf §5 eq (4)).  The encoder's
    [rotate] branch absorbs the i-rotation.

    Status: ADMITTED.  The algebraic-cancellation half (showing
    [(Px, Py) = (SQRT_M1*Qy, SQRT_M1*Qx)] via the typed E.point lift)
    follows the same blueprint as [canonical_rep_case_order2].  The
    only obstruction is that [field; Decidable.vm_decide] (the
    workhorse of order2) hangs >500s when the goal contains [SQRT_M1]
    (a ~256-bit literal) on both sides — [field]'s morphism step
    tries to reduce SQRT_M1 to canonical form.  Generalising [SQRT_M1]
    (and [Curve25519.E.d, Curve25519.E.a]) to opaque variables before
    [field] is the obvious fix but loses the [Decidable.vm_decide]
    discharge of [a <> 0].  Two viable completion paths:
      (a)  Manual ring rewriting: [rewrite F.mul_0_l, F.add_0_l,
           F.mul_0_r, F.div_1_r] etc, avoiding [field] entirely.
      (b)  Add [Strategy 0 [SQRT_M1 Curve25519.E.d Curve25519.E.a]]
           hints, then call [field].
    The encoder-invariance half (after the coord substitution) needs
    a [rotate]-branch case analysis identical to order2's structure.
    See the order2 proof and header note for the helper-lemma
    decomposition. *)
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
Admitted.

(** ** Order-4 negative case — sub_affine P Q = (-SQRT_M1, 0) ⇒
    Px = -SQRT_M1*Qy, Py = -SQRT_M1*Qx.

    Mirror of order4_pos with [SQRT_M1 ↦ -SQRT_M1].  Same status and
    blocker as [canonical_rep_case_order4_pos]; see that lemma's note. *)
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
Admitted.
