(** * Libjade.SHA256Bridge — Rocq wrapper for the libjade SHA-256 routine.
 *
 * Purpose
 * -------
 * Provide a named, registry-citable, trust-localized Rocq handle for the
 * libjade [jade_hash_sha256_amd64_ref] Jasmin routine, mirroring the
 * SHA-512 bridge at [src/Bedrock/Libjade/SHA512Bridge.v] (commit ea64131).
 * Downstream callers that need a Rocq-side SHA-256 hash function (e.g.
 * X3DH info-string KDFs, X25519-AES-GCM nonces, future EdDSA-Ed25519ph
 * pre-hash wiring) should import this file rather than declaring
 * private file-top Parameters, so that [Print Assumptions] keeps the
 * trust footprint visible inside the named libjade-axiom registry.
 *
 * Provenance chain
 * ----------------
 * The two declarations [sha256_libjade] and [sha256_libjade_len] are
 * the Rocq-side handles for the libjade [jade_hash_sha256_amd64_ref]
 * Jasmin routine.  The end-to-end trust chain is:
 *
 *   Rocq theorem (any consumer)
 *     └─ uses [sha256_libjade] (declared here)
 *           └─ axiom [Bedrock.LibjadeAxioms.jade_hash_sha256_correct]
 *                 └─ libjade EasyCrypt artefact at
 *                    [libjade/proof/crypto_hash/sha256/amd64/ref/
 *                     extracted_ct_proof.ec]
 *                 └─ libjade Jasmin source at
 *                    [libjade/oldsrc-should-delete/crypto_hash/sha256/
 *                     amd64/ref/hash.jazz] (and sha256.jinc /
 *                     sha256_globals.jinc)
 *
 * Status of the EC artefact (audit-relevant)
 * ------------------------------------------
 * The current [extracted_ct_proof.ec] file in [libjade/proof/crypto_hash/
 * sha256/amd64/ref/] only establishes the **constant-time** property of
 * the Jasmin implementation (a [proc; inline *; sim] equivalence of the
 * leakage trace).  It does **NOT** yet ship the functional-correctness
 * proof against a FIPS-180-4 reference spec for SHA-256.
 *
 * Therefore [sha256_libjade] is, today, an **opaque Rocq Parameter**
 * with the right shape.  Upgrading it to a real Theorem requires either:
 *   (a) porting the libjade SHA-256 functional-correctness EC proof to
 *       Rocq (multi-session effort; would need a FIPS-180-4 spec in Rocq
 *       — none currently in AUCurves; SHAKE256 is the closest we have in
 *       [src/Spec/SHAKE256.v], and is a different Keccak-family hash), OR
 *   (b) composing the verified Rocq Jasmin compiler's correctness
 *       theorem with a Rocq-side FIPS-180-4 SHA-256 spec.
 *
 * Both paths preserve the named-Parameter shape declared here, so future
 * downstream consumers need not change when this upgrade lands.
 *
 * Audit benefit of this file
 * --------------------------
 * Mirrors the SHA-512 bridge's structure so that, when any consumer
 * (current or future) opaquely depends on SHA-256, [Print Assumptions]
 * surfaces [sha256_libjade] / [sha256_libjade_len] declared HERE with
 * this docstring explicitly tying them to [jade_hash_sha256_correct] in
 * [Bedrock.LibjadeAxioms] rather than ending up as anonymous file-top
 * Parameters scattered through the call-site files.
 *
 * Difference vs. SHA-512 bridge (ABI)
 * -----------------------------------
 * Both libjade SHA-2 routines share an identical export signature
 * (input byte-pointer, input length, output byte-pointer) and identical
 * EC artefact shape — the only material differences are the digest size
 * (32 bytes vs. 64 bytes) and the routine name.  The corresponding
 * placeholder axioms in [Bedrock.LibjadeAxioms] also share an identical
 * shape ([forall input digest_out, True]).  This bridge is therefore a
 * literal [s/512/256/g; s/64%nat/32%nat/g] adaptation of the SHA-512
 * bridge, with this paragraph documenting the parallelism.
 *
 * See also
 * --------
 * - [src/Bedrock/LibjadeAxioms.v] — full libjade-axiom registry.
 * - [src/Bedrock/Libjade/SHA512Bridge.v] — sibling SHA-512 bridge.
 * - [src/Bedrock/Libjade/X25519Bridge.v] — sibling X25519 bridge.
 * - [src/Bedrock/TrustAxioms.v] §3 — audit notes for these declarations.
 *)

From Stdlib Require Import String ZArith List.
From Stdlib Require Import Init.Byte.
Require Import Bedrock.LibjadeAxioms.
Import ListNotations.

(* ================================================================ *)
(* §1.  The Rocq-side SHA-256 handle                                 *)
(* ================================================================ *)

(** [sha256_libjade input] is the SHA-256 digest of [input], computed
    at link time by the libjade [jade_hash_sha256_amd64_ref] Jasmin
    routine.

    Trust: opaque Parameter, registered in
    [Bedrock.LibjadeAxioms.jade_hash_sha256_correct].  See file header
    for the EC provenance and the path to upgrading this to a real
    Theorem. *)
Parameter sha256_libjade : list Byte.byte -> list Byte.byte.

(** Length of the [sha256_libjade] output is fixed at 32 bytes (256
    bits), per FIPS 180-4.  Opaque Parameter for the same reason as
    [sha256_libjade] itself.

    When the EC functional-correctness proof lands in Rocq (or via the
    Rocq Jasmin compiler), this becomes a Theorem proved from the
    underlying spec. *)
Parameter sha256_libjade_len :
  forall input, length (sha256_libjade input) = 32%nat.

(** Convenience alias matching the FIPS-180-4 phrasing used in any
    headline SHA-256-based correctness theorem.  Identical to
    [sha256_libjade]; only the name differs. *)
Definition sha256_libjade_correct (input : list Byte.byte) : list Byte.byte :=
  sha256_libjade input.

Lemma sha256_libjade_correct_len :
  forall input, length (sha256_libjade_correct input) = 32%nat.
Proof. intro input; apply sha256_libjade_len. Qed.

(* ================================================================ *)
(* §2.  Audit-trail breadcrumb                                       *)
(* ================================================================ *)

(** Citation marker: when [jade_hash_sha256_correct] gets upgraded
    from its placeholder [True] body to a real functional-correctness
    Prop, this marker becomes the explicit per-file trust bridge
    (replace [True] below with the upgraded axiom application).  For
    now, [Require Import Bedrock.LibjadeAxioms] above already brings
    the axiom into the proof environment; downstream [Print
    Assumptions] will list it whenever the upgraded axiom is used. *)
Definition sha256_libjade_trust_marker : Prop := True.

Lemma sha256_libjade_trust_marker_holds : sha256_libjade_trust_marker.
Proof. exact I. Qed.
