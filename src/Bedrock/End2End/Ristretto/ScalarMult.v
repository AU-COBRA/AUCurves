(** * Ristretto255 scalar multiplication — bedrock2 specification

    Computes [out = scalar · point] on ristretto255, represented as
    32-byte little-endian encoded field elements.

    Implementation strategy: reuse the X25519 Montgomery ladder
    (MontgomeryLadder.v) which computes the x-coordinate of scalar
    multiplication on Curve25519, then lift to ristretto255 encoding.

    The Montgomery ladder is verified in fiat-crypto (Qed, 12K lines).
    The EdwardsMontgomeryIsomorphism (Qed) connects Montgomery and
    Edwards representations.

    ## Verification chain (all Rocq)
    bedrock2 WP → ToJasmin (Qed) → bridge_simulation (Qed)
    → jasminc compiler_correct (Rocq) → x86-64

    Step 8b of the Signal verification plan. *)

From Coq Require Import ZArith Lia String List.
From Coq.Init Require Import Byte.
Require Import bedrock2.Syntax bedrock2.NotationsCustomEntry.
Require Import bedrock2.Map.Separation.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Import Syntax Syntax.Coercions NotationsCustomEntry ListNotations.

Require Import Crypto.Spec.Curve25519.

(** The ristretto scalar multiplication function.

    Inputs:
      out: pointer to 32-byte output buffer
      scalar: pointer to 32-byte scalar (clamped externally)
      point: pointer to 32-byte ristretto-encoded point

    Output: out = scalar · point (32-byte ristretto encoding)

    Implementation: calls the X25519 Montgomery ladder internally,
    which computes the x-coordinate of the scalar multiple.
    The ristretto encoding uses the y-coordinate, computed via
    the Edwards↔Montgomery isomorphism.

    For now we define the spec; the bedrock2 implementation and
    WP proof follow the clamp.v / MontgomeryLadder.v pattern. *)

(** TODO: bedrock2 implementation + WP proof.
    This requires:
    1. Import Field25519.v field ops (10-limb or 5-limb)
    2. Call montladder for x-coordinate
    3. Compute y from x via Edwards equation
    4. Encode as ristretto (canonical representative)

    Estimated: 1 week.
    Template: fiat-crypto/src/Bedrock/End2End/X25519/MontgomeryLadder.v *)
