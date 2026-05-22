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
Require Import Crypto.Spec.Curve25519.
Require Import Crypto.Spec.CompleteEdwardsCurve.
Require Import Bedrock.Field.Synthesis.Examples.Ristretto255_Encode.
Import ListNotations.
Local Open Scope F_scope.

Local Notation Fp := (F.F (2^255 - 19)).
Local Notation Fzero := (F.of_Z _ 0).
Local Notation Fone  := (F.of_Z _ 1).

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

(** ** Identity case — sub_affine P Q = (0, 1) ⇒ Px = Qx ∧ Py = Qy. *)
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
Admitted.

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
Admitted.

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
