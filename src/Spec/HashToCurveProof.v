(** * Hash-to-curve correctness: the full pipeline produces curve points.

    Assembles [map_produces_curve_points] from:
    - [swu_maps_to_Eprime] (SWU output is on E')
    - [iso_map_on_curve] (isogeny maps ALL E' points to E)

    No axioms required. The projective iso_map handles kernel points
    correctly by returning (0, 2) ∈ E when xden * yden = 0. *)

From Stdlib Require Import ZArith.
Require Import Spec.HashToCurve.
Require Import Spec.HashToCurveFieldSetup.
Require Import Spec.HashToCurveSWUProof.
Require Import Spec.HashToCurveIsogenyProof.

Theorem map_produces_curve_points_proof : map_produces_curve_points.
Proof.
  unfold map_produces_curve_points, map_to_curve_g1.
  intro u.
  apply iso_map_on_curve.
  exact (swu_maps_to_Eprime_proof u).
Qed.
