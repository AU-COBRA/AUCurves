(** * Ed25519 Edwards XYZT atoms — 64-bit port (Step 1 of Phase 1.3).
 *
 * Mirror of [fiat-crypto/.../X25519/EdwardsXYZT.v] but instantiated at
 * 64-bit BasicC64Semantics + Field25519_64's frep25519. The bedrock2
 * `func` syntax trees are width-agnostic; the proofs need 64-bit
 * field-representation hints.
 *
 * Status (Step 1 in progress, iteration 1 — bootstrap):
 *   - Imports + 64-bit instances set up.
 *   - Structure definitions (projective_coords, etc.) pending sub-task 1.1.
 *   - func definitions pending sub-task 1.2.
 *   - _ok lemmas pending sub-tasks 1.3-1.5.
 *
 * See [option-b-64bit-port-plan.md] for the full Step 1 plan. *)

From Stdlib Require Import String List ZArith.
Require Import Crypto.Spec.ModularArithmetic.
From coqutil.Tactics Require Import Tactics.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import bedrock2.Syntax.
Require Import bedrock2.BasicC64Semantics.
Require Import coqutil.Word.Bitwidth64.
Require Import Crypto.Spec.Curve25519.
Require Import Crypto.Spec.CompleteEdwardsCurve.
Require Import Crypto.Curves.Edwards.XYZT.Basic.
Require Import Crypto.Curves.Edwards.XYZT.Precomputed.
Require Import Crypto.Curves.Edwards.XYZT.Readdition.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Bedrock.End2End.X25519_64.Field25519_64.

(* 64-bit word + field-rep instances. *)
#[export] Existing Instances
  BasicC64Semantics.word
  BasicC64Semantics.wordok
  Bitwidth64.BW64
  BasicC64Semantics.mem
  BasicC64Semantics.mapok.

#[export] Existing Instance field_parameters.
#[export] Existing Instance frep25519.
#[export] Existing Instance frep25519_ok.

Local Existing Instance Curve25519.field.
Local Existing Instance Curve25519.char_ge_3.

Module Ed25519XYZT64.

  (** Ed25519 Edwards curve parameters (from Curve25519.E).
      Use F_scope so unqualified `*`, `+`, `-`, `^` resolve to the
      F-arithmetic versions throughout the structure definitions. *)
  Local Open Scope F_scope.
  Local Notation a := Curve25519.E.a.
  Local Notation d := Curve25519.E.d.
  Local Notation point := (@Extended.point _ Logic.eq F.zero F.add F.mul a d).
  Local Notation precomputed_point := (@Precomputed.precomputed_point _ Logic.eq
                                         F.zero F.one F.opp F.add F.sub F.mul a d).
  Local Notation cached := (@Readdition.cached _ Logic.eq
                             F.zero F.one F.opp F.add F.sub F.mul F.inv F.div a d).

  (** ** Sub-task 1.1: structure definitions (projective/precomputed/cached
      coords with bounds). Verbatim port from
      [fiat-crypto/.../X25519/EdwardsXYZT.v] lines 222-294. The
      `felem` and `feval` resolve to our 64-bit [frep25519] instance
      via Existing Instance above; bounds (`tight_bounds`,
      `loose_bounds`) come from the same. *)

  Definition valid_projective_coords (X Y Z Ta Tb : felem):=
    ((a * (feval X)^2*(feval Z)^2 + (feval Y)^2*(feval Z)^2 = ((feval Z)^2)^2 + d * (feval X)^2 * (feval Y)^2)%F /\
    ((feval X) * (feval Y) = (feval Z) * (feval Ta) * (feval Tb))%F /\
    ((feval Z) <> 0)%F).

  Definition projective_coords := { c | let '(X,Y,Z,Ta,Tb) := c in
    valid_projective_coords X Y Z Ta Tb /\
    bounded_by tight_bounds X /\ bounded_by tight_bounds Y /\ bounded_by tight_bounds Z /\
    bounded_by loose_bounds Ta /\ bounded_by loose_bounds Tb }.

  Definition feval_projective_coords (c : projective_coords) :=
    let '(X, Y, Z, Ta, Tb) := proj1_sig c in (feval X, feval Y, feval Z, feval Ta, feval Tb).

  Definition coords_to_point (c : projective_coords) : point.
    refine (exist _ (feval_projective_coords c) _).
    abstract (destruct_head' projective_coords;
      cbv [proj1_sig feval_projective_coords valid_projective_coords] in *;
      destruct_head' prod; destruct_head' and; ssplit; assumption).
  Defined.

  Definition valid_precomputed_coords (half_ypx half_ymx xyd : felem) :=
    let x := (feval half_ypx) - (feval half_ymx) in
    let y := (feval half_ypx) + (feval half_ymx) in
    (a*x^2 + y^2 = 1 + d*x^2*y^2)
    /\ (feval xyd) = x * y * d.

  Definition precomputed_coords := { c | let '(half_ypx, half_ymx, xyd) := c in
                              valid_precomputed_coords half_ypx half_ymx xyd /\
                              bounded_by loose_bounds half_ymx /\ bounded_by loose_bounds half_ypx /\
                              bounded_by loose_bounds xyd }.

  Definition feval_precomputed_coords (c : precomputed_coords) :=
    let '(half_ypx, half_ymx, xyd) := proj1_sig c in (feval half_ypx, feval half_ymx, feval xyd).

  Definition precomputed_coords_to_precomputed (c : precomputed_coords) : precomputed_point.
    refine (exist _ (feval_precomputed_coords c) _).
    abstract (destruct_head' precomputed_coords; destruct_head' prod;
    destruct_head' and; cbv [feval_precomputed_coords valid_precomputed_coords proj1_sig] in *; assumption).
  Defined.

  Definition valid_cached_coords (half_YmX half_YpX Z Td : felem):=
    let X := (feval half_YpX) - (feval half_YmX) in
    let Y := (feval half_YpX) + (feval half_YmX) in
    let T := (feval Td) / d in
    let Z := (feval Z) in
      a * X^2*Z^2 + Y^2*Z^2 = (Z^2)^2 + d * X^2 * Y^2 /\
      X * Y = Z * T /\
      Z <> 0.

  Definition cached_coords := { c | let '(half_YmX, half_YpX, Z, Td) := c in
                              valid_cached_coords half_YmX half_YpX Z Td /\
                              bounded_by loose_bounds half_YmX /\ bounded_by loose_bounds half_YpX /\
                              bounded_by loose_bounds Z /\ bounded_by loose_bounds Td }.

  Definition feval_cached_coords (c : cached_coords) :=
    let '(half_YmX, half_YpX, Z, Td) := proj1_sig c in (feval half_YmX, feval half_YpX, feval Z, feval Td).

  Definition cached_coords_to_cached (c : cached_coords) : cached.
    refine (exist _ (feval_cached_coords c) _).
    abstract (destruct_head' cached_coords; destruct_head' prod;
    destruct_head' and;
      cbv [valid_cached_coords proj1_sig] in *; assumption).
  Defined.

  (** ** Sub-task 1.2: bedrock2 funcs (add_precomputed, double, to_cached,
      readd). Pending — copy from upstream lines 78-145. The syntax
      trees are width-agnostic; just need the 64-bit instances active. *)

  (** ** Sub-tasks 1.3-1.5: spec_of declarations + _ok proofs. Pending. *)

End Ed25519XYZT64.
