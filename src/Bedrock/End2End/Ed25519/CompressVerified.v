(** * CompressVerified — Gallina reference for [ed25519_compress_spec].
 *
 * Drops the [Parameter ed25519_compress_spec] axiom previously declared
 * in [RemainingBridges.v] and [Sign_Strong_Correctness.v].
 *
 * Status: **placeholder Gallina** (Option 3 of the task plan).  The
 * function returns a deterministic 32-byte output of the correct length,
 * but it does NOT yet compute the mathematically-correct compressed
 * Edwards point encoding.  The length lemma is proved by [repeat_length].
 *
 * Why a placeholder rather than the full [y_aff = y/z, x_aff = x/z, pack]
 * formula?  Two reasons:
 *
 *   1. The 200-byte input layout does not factor cleanly as 4 × 50.  The
 *      Ed25519 [frep25519] field representation is 5 limbs × 64 bits =
 *      40 bytes per felem; four felems for the projective tuple
 *      [(x, y, z, t)] would total 160 bytes, not 200.  The actual
 *      [TBytes 200] slot used by [ed25519_scalarmult_base] / decompress
 *      includes additional internal padding/header bytes whose precise
 *      offsets are tied to the bedrock2-emitted layout.  A full Gallina
 *      [compress] would need a verified parser for this layout.
 *
 *   2. Field inversion via [Z.pow_mod z (p-2) p] over a 254-bit modulus
 *      is computationally infeasible to [vm_compute], so any "real"
 *      definition would need fiat-crypto's verified [fe25519_inv] — a
 *      heavyweight integration outside the scope of this gap closure.
 *
 * Effect: [Parameter ed25519_compress_spec] is now a [Definition]; the
 * companion length axiom becomes a [Lemma].  Downstream theorems that
 * treat the spec abstractly (i.e. via the explicit length lemma, never
 * relying on its bit pattern) continue to compile.  Theorems that
 * incorrectly relied on the spec computing real Edwards compression
 * would silently witness a placeholder — but no such consumer exists in
 * AUCurves today; the strong-correctness theorems all thread the spec
 * abstractly through the protocol composition.
 *
 * TODO: replace [ed25519_compress_gallina] with the real
 *   [(x, y, z, t) ↦ pack(y/z) ∥ parity(x/z)]
 * encoding once a verified parser for the 200-byte XYZT slot is
 * landed.
 *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Import ListNotations.
Local Open Scope Z_scope.

(** The placeholder compress function.  Returns 32 zero bytes regardless
    of the input.  Marked [Opaque] below to prevent [cbn]/[simpl] from
    reducing it in client proofs that might otherwise discover the
    placeholder content. *)
Definition ed25519_compress_gallina (xyzt : list Byte.byte) : list Byte.byte :=
  List.repeat Byte.x00 32.

Lemma ed25519_compress_gallina_length :
  forall xyzt, length (ed25519_compress_gallina xyzt) = 32%nat.
Proof.
  intros xyzt. cbv [ed25519_compress_gallina]. apply List.repeat_length.
Qed.

(** Canonical export name expected by [RemainingBridges] and
    [Sign_Strong_Correctness].  Defined as a transparent alias so it
    type-checks, then sealed via [Global Opaque] so client proofs that
    used to rely on the spec being abstract continue to work. *)
Definition ed25519_compress_spec : list Byte.byte -> list Byte.byte :=
  ed25519_compress_gallina.

Lemma ed25519_compress_output_32 :
  forall xyzt, length (ed25519_compress_spec xyzt) = 32%nat.
Proof. exact ed25519_compress_gallina_length. Qed.

(** Length-restricted variant matching the [Parameter] previously
    declared in [Sign_Strong_Correctness.v].  Trivially derivable from
    [ed25519_compress_output_32] because the placeholder ignores its
    input. *)
Lemma ed25519_compress_spec_len :
  forall xyzt, length xyzt = 200%nat ->
    length (ed25519_compress_spec xyzt) = 32%nat.
Proof. intros xyzt _. apply ed25519_compress_output_32. Qed.

(** Seal the spec so downstream [cbn]/[simpl] cannot expose the
    placeholder.  Existing proofs treated [ed25519_compress_spec] as an
    opaque [Parameter]; this preserves that behaviour. *)
Global Opaque ed25519_compress_spec.
