(** * Top-level G2 hash-to-curve correctness theorem.

    Assembles the SWU correctness, isogeny correctness, and closure
    properties into the main theorem:

      forall msg dst, on_curve_E2_opt (hash_to_curve_g2 msg dst).

    Key trick: make map_to_curve_g2, point_add_g2, clear_cofactor_g2
    Opaque before the list destruct to prevent Coq from trying to
    reduce the huge cofactor constant. Use numbered goal selectors
    (1,2,4: exact I) instead of [try exact I] to avoid timeouts. *)

From Stdlib Require Import ZArith List Bool.
Import ListNotations.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Spec.HashToCurve.
Require Import Spec.HashToCurveG2.
Require Import Spec.HashToCurveClosureProof_G2.
Require Import Spec.HashToCurveIsogenyProof_G2.
Require Import Spec.HashToCurveSWUProof_G2.

Local Open Scope F_scope.

Local Transparent map_to_curve_g2 point_add_g2 clear_cofactor_g2.

(** map_to_curve_g2 always produces a point on E2. *)
Lemma map_to_curve_g2_on_curve : forall u : Fp2,
  on_curve_E2 (map_to_curve_g2 u).
Proof.
  intro u. unfold map_to_curve_g2.
  exact (iso_map_g2_on_curve _ (swu_g2_maps_to_E2prime u)).
Qed.

Local Opaque map_to_curve_g2 point_add_g2 clear_cofactor_g2.

(** hash_to_curve_g2 always produces a point on E2 (or the identity). *)
Theorem hash_to_curve_g2_on_curve :
  forall msg dst, on_curve_E2_opt (hash_to_curve_g2 msg dst).
Proof.
  intros msg dst. unfold hash_to_curve_g2.
  destruct (hash_to_field_fp2 msg dst 2) as [|u0 [|u1 [|? ?]]].
  1,2,4: exact I.
  apply clear_cofactor_g2_preserves.
  apply (point_add_g2_preserves (Some (map_to_curve_g2 u0)) (Some (map_to_curve_g2 u1)));
    exact (map_to_curve_g2_on_curve _).
Qed.

(** encode_to_curve_g2 always produces a point on E2 (or the identity). *)
Theorem encode_to_curve_g2_on_curve :
  forall msg dst, on_curve_E2_opt (encode_to_curve_g2 msg dst).
Proof.
  intros msg dst. unfold encode_to_curve_g2.
  destruct (hash_to_field_fp2 msg dst 1) as [|u0 [|? ?]].
  1,3: exact I.
  apply clear_cofactor_g2_preserves. exact (map_to_curve_g2_on_curve u0).
Qed.
