(** * Libjade.SHA512Bridge — Rocq wrapper for the libjade SHA-512 routine.
 *
 * Purpose
 * -------
 * Consolidate the [sha512_full_spec] / [sha512_full_spec_len] pair that
 * was previously declared as file-top Parameters at
 *   [src/Bedrock/End2End/Ed25519/Sign_Strong_Correctness.v:70-72]
 * into a single named, registry-citable trust-localized handle that
 * lives next to the other libjade trust assumptions (registered in
 * [src/Bedrock/LibjadeAxioms.v]).
 *
 * Provenance chain
 * ----------------
 * The two declarations [sha512_libjade] and [sha512_libjade_len] are
 * the Rocq-side handles for the libjade [jade_hash_sha512_amd64_ref]
 * Jasmin routine.  The end-to-end trust chain is:
 *
 *   Rocq theorem (e.g. [ed25519_sign_strong_correct])
 *     └─ uses [sha512_libjade] (declared here)
 *           └─ axiom [Bedrock.LibjadeAxioms.jade_hash_sha512_correct]
 *                 └─ libjade EasyCrypt artefact at
 *                    [libjade/proof/crypto_hash/sha512/amd64/ref/
 *                     extracted_ct_proof.ec]
 *                 └─ libjade Jasmin source at
 *                    [libjade/oldsrc-should-delete/crypto_hash/sha512/
 *                     amd64/ref/hash.jazz] (and sha512.jinc / sha512_globals.jinc)
 *
 * Status of the EC artefact (audit-relevant)
 * ------------------------------------------
 * The current [extracted_ct_proof.ec] file in [libjade/proof/crypto_hash/
 * sha512/amd64/ref/] only establishes the **constant-time** property of
 * the Jasmin implementation (a [proc; inline *; sim] equivalence of the
 * leakage trace).  It does **NOT** yet ship the functional-correctness
 * proof against a FIPS-180-4 reference spec for SHA-512.
 *
 * Therefore [sha512_libjade] is, today, an **opaque Rocq Parameter**
 * with the right shape.  Upgrading it to a real Theorem requires either:
 *   (a) porting the libjade SHA-512 functional-correctness EC proof to
 *       Rocq (multi-session effort; would need a FIPS-180-4 spec in Rocq
 *       — none currently in AUCurves; SHAKE256 is the closest we have in
 *       [src/Spec/SHAKE256.v], and is a different Keccak-family hash), OR
 *   (b) composing the verified Rocq Jasmin compiler's correctness
 *       theorem with a Rocq-side FIPS-180-4 SHA-512 spec.
 *
 * Both paths preserve the named-Parameter shape declared here, so
 * downstream consumers ([Sign_Strong_Correctness], [Verify_Strong_Correctness],
 * [Schnorr.Strong_Correctness], [XEdDSA.Sign_Strong_Correctness]) need
 * not change when this upgrade lands.
 *
 * Audit benefit of this file
 * --------------------------
 * Before this bridge, [Print Assumptions ed25519_sign_strong_correct]
 * reported [sha512_full_spec] and [sha512_full_spec_len] as anonymous
 * file-top Parameters not visible in the trust registry — flagged by
 * the 2026-05-13 trust audit (commit b7db253) as a documentation gap.
 * After this bridge, the same Print Assumptions output points at
 * [sha512_libjade] / [sha512_libjade_len] declared HERE, with this
 * docstring explicitly tying them to [jade_hash_sha512_correct] in
 * [Bedrock.LibjadeAxioms].
 *
 * See also
 * --------
 * - [src/Bedrock/LibjadeAxioms.v] — full libjade-axiom registry.
 * - [src/Bedrock/TrustAxioms.v] §3 — audit notes for these declarations.
 * - [src/Bedrock/End2End/Ed25519/SHA512Bridge.v] — bedrock2 fnspec /
 *   refinement bridge for the [sha512_64] callee (different file,
 *   same target Jasmin routine).
 *)

From Stdlib Require Import String ZArith List.
From Stdlib Require Import Init.Byte.
Require Import Bedrock.LibjadeAxioms.
Import ListNotations.

(* ================================================================ *)
(* §1.  The Rocq-side SHA-512 handle                                 *)
(* ================================================================ *)

(** [sha512_libjade input] is the SHA-512 digest of [input], computed
    at link time by the libjade [jade_hash_sha512_amd64_ref] Jasmin
    routine.

    Trust: opaque Parameter, registered in
    [Bedrock.LibjadeAxioms.jade_hash_sha512_correct].  See file header
    for the EC provenance and the path to upgrading this to a real
    Theorem. *)
Parameter sha512_libjade : list Byte.byte -> list Byte.byte.

(** Length of the [sha512_libjade] output is fixed at 64 bytes (512
    bits), per FIPS 180-4.  Opaque Parameter for the same reason as
    [sha512_libjade] itself.

    When the EC functional-correctness proof lands in Rocq (or via the
    Rocq Jasmin compiler), this becomes a Theorem proved from the
    underlying spec. *)
Parameter sha512_libjade_len :
  forall input, length (sha512_libjade input) = 64%nat.

(** Convenience alias matching the FIPS-180-4 phrasing used in the
    headline ed25519/xeddsa correctness theorems.  Identical to
    [sha512_libjade]; only the name differs. *)
Definition sha512_libjade_correct (input : list Byte.byte) : list Byte.byte :=
  sha512_libjade input.

Lemma sha512_libjade_correct_len :
  forall input, length (sha512_libjade_correct input) = 64%nat.
Proof. intro input; apply sha512_libjade_len. Qed.

(* ================================================================ *)
(* §2.  Audit-trail breadcrumb                                       *)
(* ================================================================ *)

(** Citation marker: when [jade_hash_sha512_correct] gets upgraded
    from its placeholder [True] body to a real functional-correctness
    Prop, this marker becomes the explicit per-file trust bridge
    (replace [True] below with the upgraded axiom application).  For
    now, [Require Import Bedrock.LibjadeAxioms] above already brings
    the axiom into the proof environment; downstream [Print
    Assumptions] will list it whenever the upgraded axiom is used. *)
Definition sha512_libjade_trust_marker : Prop := True.

Lemma sha512_libjade_trust_marker_holds : sha512_libjade_trust_marker.
Proof. exact I. Qed.
