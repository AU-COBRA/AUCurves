(** * Ed25519 Edwards scalarmult — bedrock2 interface.
 *
 * Phase 1.3/1.4 prerequisite: Sign.v needs `r·B` and `a·B`; Verify.v
 * needs `s·B - k·A` (decomposed as `s·B` and `k·A` then add/negate).
 * No bedrock2 Edwards scalarmult function exists in fiat-crypto or
 * AUCurves — only the atomic operations [add_precomputed], [double],
 * [to_cached], [readd] in [fiat-crypto/.../X25519/EdwardsXYZT.v]
 * (lines 78-145, all Qed at lines 477-580).
 *
 * This file is the [Parameter] interface that Sign.v / Verify.v
 * consume. Discharge target is [Scalarmult_Impl.v.todo] (sibling),
 * which when enabled will define the bedrock2 body and prove
 * correctness against the spec-level [E.mul] in
 * [Crypto.Spec.CompleteEdwardsCurve].
 *
 * Two implementation paths considered (deferred to a separate session):
 *
 *   (a) Native double-and-add over the bedrock2 [add_precomputed] /
 *       [double] primitives. Standard Edwards scalarmult: 256
 *       doublings + ~128 conditional adds. Constant-time discipline
 *       required for the [a·B] caller (a is the secret scalar);
 *       variable-time fine for [r·B] / [s·B] / [k·A] (no secret
 *       dependency). Estimated ~150-250 LoC bedrock2 + ~200-400 LoC
 *       WP proof composing the existing primitive _ok lemmas.
 *
 *   (b) Reuse [montladder] (X25519's Montgomery ladder) via the
 *       Edwards-Montgomery birational map
 *       [Curves/EdwardsMontgomery25519.v]. Lower scope for the
 *       scalarmult itself but adds a non-trivial recovery routine
 *       (Montgomery ladder yields only u-coord; recovering full
 *       Edwards (X,Y,Z,T) needs a y-coordinate recovery which is
 *       its own ~50-100 LoC routine + proof). Net likely similar
 *       work to (a); no reuse-of-existing-bedrock2 shortcut.
 *
 * Recommended path: (a). Cleanest dependency story; one new file
 * (Scalarmult_Impl.v); proof composes the atom _ok lemmas with a
 * standard loop invariant.
 *
 * Status (2026-04-26): Parameters declared. Implementation pending.
 *)

From Stdlib Require Import String List ZArith.
Require Import bedrock2.Syntax.
Require Import coqutil.Word.LittleEndianList.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.Curve25519.
Require Import Crypto.Spec.CompleteEdwardsCurve.
Require Import Crypto.Curves.Edwards.XYZT.Basic.
Require Import Bedrock.End2End.Ed25519.EdwardsXYZT25519.

Module Ed25519Scalarmult.

  (** Decode a 32-byte little-endian scalar into a [nat] index for
      [E.mul] / [scalarmult]. Range: [0, 2^256).
      (Reduction mod L is the caller's responsibility; the bedrock2
      function operates on the raw 256-bit integer.) *)
  Definition decode_le_scalar (bs : list Byte.byte) : nat :=
    Z.to_nat (LittleEndianList.le_combine bs).

  (** Constant-time scalarmult against the Ed25519 basepoint.
      Inputs: [out : ptr to projective point (5 felems)], [scalar : ptr to 32 bytes].
      Output: [out] populated with [scalar · B].
      Constant-time discipline required for the secret-key path. *)
  Parameter ed25519_scalarmult_base : Syntax.func.

  (** General scalarmult against an arbitrary point (variable-time OK).
      Inputs: [out], [scalar : ptr to 32 bytes], [P : ptr to projective point].
      Output: [out] populated with [scalar · P]. *)
  Parameter ed25519_scalarmult : Syntax.func.

  (** Spec connection (real Hoare-triple wrapping pending in
      [Scalarmult_Impl.v.todo]). The intent: bedrock2
      [ed25519_scalarmult_base scalar] outputs bytes that decode to a
      projective point whose affine projection equals
      [E.mul (decode_le_scalar scalar) Curve25519.E.B]. The full
      sep-logic wrapping requires field-representation predicates that
      bind the bedrock2 byte/limb buffer to [Extended.point].

      The expected spec function name to compose with is
      [Ed25519XYZT.scalarmult], whose correctness is the Closed
      [Ed25519XYZT.scalarmult_correct] theorem.

      Spec is left as `True` placeholder until the implementation
      lands and the sep-logic wrapping can be stated precisely. *)
  Axiom ed25519_scalarmult_base_correct :
    forall (scalar : list Byte.byte),
      length scalar = 32%nat -> True.

  Axiom ed25519_scalarmult_correct :
    forall (scalar : list Byte.byte),
      length scalar = 32%nat -> True.

End Ed25519Scalarmult.
