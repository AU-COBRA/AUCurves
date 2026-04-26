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

  (** Ed25519 Edwards curve parameters (from Curve25519.E). *)
  Local Notation "x ^ 2" := (F.mul x x) (at level 30).
  Local Notation a := Curve25519.E.a.
  Local Notation d := Curve25519.E.d.
  Local Notation point := (@Extended.point _ Logic.eq F.zero F.add F.mul a d).
  Local Notation precomputed_point := (@Precomputed.precomputed_point _ Logic.eq
                                         F.zero F.one F.opp F.add F.sub F.mul a d).
  Local Notation cached := (@Readdition.cached _ Logic.eq
                             F.zero F.one F.opp F.add F.sub F.mul F.inv F.div a d).

  (** ** Sub-task 1.1: structure definitions (projective/precomputed/cached
      coords with bounds). Pending — copy from
      [fiat-crypto/.../X25519/EdwardsXYZT.v] lines 222-294 with `felem`
      coming from our 64-bit [frep25519]. *)

  (* TODO: sub-task 1.1 — projective_coords, precomputed_coords,
     cached_coords, valid_*_coords, feval_*_coords, *_coords_to_*. *)

  (** ** Sub-task 1.2: bedrock2 funcs (add_precomputed, double, to_cached,
      readd). Pending — copy from upstream lines 78-145. The syntax
      trees are width-agnostic; just need the 64-bit instances active. *)

  (** ** Sub-tasks 1.3-1.5: spec_of declarations + _ok proofs. Pending. *)

End Ed25519XYZT64.
