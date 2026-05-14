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
 *     └─ uses [sha512_libjade] (now declared in [Bedrock.LibjadeAxioms])
 *           └─ axiom [Bedrock.LibjadeAxioms.jade_hash_sha512_correct]
 *                 └─ libjade EasyCrypt artefact at
 *                    [libjade/proof/crypto_hash/sha512/amd64/ref/
 *                     extracted_ct_proof.ec]
 *                 └─ libjade Jasmin source at
 *                    [libjade/oldsrc-should-delete/crypto_hash/sha512/
 *                     amd64/ref/hash.jazz] (and sha512.jinc / sha512_globals.jinc)
 *
 * 2026-05-14 upgrade (this commit)
 * --------------------------------
 * The registry slot [jade_hash_sha512_correct] was upgraded from its
 * earlier [True] placeholder body to a concrete byte equality against
 * a Rocq-side FIPS-180-4 SHA-512 reference spec:
 *   [Bedrock.Libjade.SHA512Spec.sha512_spec].
 *
 * Trust footprint after this upgrade:
 *   - [sha512_libjade] (Parameter, in [Bedrock.LibjadeAxioms]): the
 *     symbol that the Rust [extern "C" jade_hash_sha512_amd64_ref] FFI
 *     resolves to at link time.  Cannot be a Theorem until either the
 *     libjade EC proof is ported to Rocq, or the verified Rocq Jasmin
 *     compiler is composed with [SHA512Spec.sha512_spec].
 *   - [jade_hash_sha512_correct] (Axiom, in [Bedrock.LibjadeAxioms]):
 *     the byte-equality between the FFI symbol and the reference spec.
 *
 * Both remain trust assumptions until the EC port or the Jasmin
 * compiler composition lands.
 *
 * Status of the EC artefact (audit-relevant)
 * ------------------------------------------
 * The current [extracted_ct_proof.ec] file in [libjade/proof/crypto_hash/
 * sha512/amd64/ref/] only establishes the **constant-time** property of
 * the Jasmin implementation (a [proc; inline *; sim] equivalence of the
 * leakage trace).  It does **NOT** yet ship the functional-correctness
 * proof against a FIPS-180-4 reference spec for SHA-512.
 *
 * Upgrading [jade_hash_sha512_correct] to a real Theorem requires
 * either:
 *   (a) porting the libjade SHA-512 functional-correctness EC proof to
 *       Rocq.  The reference spec in [Bedrock.Libjade.SHA512Spec] is
 *       now in place to be the target of such a port.
 *   (b) composing the verified Rocq Jasmin compiler's correctness
 *       theorem with [Bedrock.Libjade.SHA512Spec.sha512_spec].
 *
 * Both paths preserve the named-Parameter shape declared in
 * [Bedrock.LibjadeAxioms], so downstream consumers
 * ([Sign_Strong_Correctness], [Verify_Strong_Correctness],
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
 * [Bedrock.LibjadeAxioms.sha512_libjade] /
 * [Bedrock.LibjadeAxioms.jade_hash_sha512_correct], with this
 * docstring explicitly tying them to [SHA512Spec.sha512_spec].
 *
 * See also
 * --------
 * - [src/Bedrock/LibjadeAxioms.v]       — full libjade-axiom registry.
 * - [src/Bedrock/Libjade/SHA512Spec.v]  — FIPS-180-4 SHA-512 reference spec.
 * - [src/Bedrock/Libjade/SHA256Bridge.v] — sibling SHA-256 bridge (A107).
 * - [src/Bedrock/TrustAxioms.v] §3      — audit notes for these declarations.
 * - [src/Bedrock/End2End/Ed25519/SHA512Bridge.v] — bedrock2 fnspec /
 *   refinement bridge for the [sha512_64] callee (different file,
 *   same target Jasmin routine).
 *)

From Stdlib Require Import String ZArith List.
From Stdlib Require Import Init.Byte.
Require Import Bedrock.LibjadeAxioms.
Require Import Bedrock.Libjade.SHA512Spec.
Import ListNotations.

(* ================================================================ *)
(* §1.  The Rocq-side SHA-512 handle                                 *)
(* ================================================================ *)

(** [sha512_libjade input] is the SHA-512 digest of [input], computed
    at link time by the libjade [jade_hash_sha512_amd64_ref] Jasmin
    routine.

    Now declared as the Parameter in [Bedrock.LibjadeAxioms] (so the
    [jade_hash_sha512_correct] axiom can directly reference it as a byte
    equality against the Rocq FIPS-180-4 reference spec); this bridge
    re-exports the symbol for downstream call sites that historically
    imported it from this file.  See file header for the EC provenance
    and the path to upgrading this to a real Theorem. *)
Notation sha512_libjade := Bedrock.LibjadeAxioms.sha512_libjade (only parsing).

(** Length of the [sha512_libjade] output is fixed at 64 bytes (512
    bits), per FIPS 180-4.  Now provable as a [Lemma] from the
    [jade_hash_sha512_correct] axiom plus [sha512_spec_length]; no
    additional axiom is needed.

    Before 2026-05-14 this was an opaque Parameter; concretizing the
    registry slot lets us discharge it from the spec's length theorem. *)
Lemma sha512_libjade_len :
  forall input, length (sha512_libjade input) = 64%nat.
Proof.
  intro input.
  rewrite jade_hash_sha512_correct.
  apply sha512_spec_length.
Qed.

(** Convenience alias matching the FIPS-180-4 phrasing used in the
    headline ed25519/xeddsa correctness theorems.  Identical to
    [sha512_libjade]; only the name differs. *)
Definition sha512_libjade_correct (input : list Byte.byte) : list Byte.byte :=
  sha512_libjade input.

Lemma sha512_libjade_correct_len :
  forall input, length (sha512_libjade_correct input) = 64%nat.
Proof. intro input; apply sha512_libjade_len. Qed.

(** Headline byte equality: the libjade Jasmin output and the Rocq
    FIPS-180-4 spec agree bytewise on every input.  Re-export of
    [Bedrock.LibjadeAxioms.jade_hash_sha512_correct] under the bridge's
    naming convention. *)
Lemma jade_hash_sha512_correct_byte_eq :
  forall input, sha512_libjade input = sha512_spec input.
Proof. intro input; apply jade_hash_sha512_correct. Qed.

(* ================================================================ *)
(* §2.  Audit-trail breadcrumb                                       *)
(* ================================================================ *)

(** Citation marker for the trust audit: 2026-05-14, the
    [jade_hash_sha512_correct] axiom was upgraded from a [True]
    placeholder to a concrete byte equality against
    [Bedrock.Libjade.SHA512Spec.sha512_spec].  Downstream [Print
    Assumptions] now lists the upgraded axiom (citing [sha512_spec])
    instead of the placeholder. *)
Definition sha512_libjade_trust_marker : Prop :=
  forall input, sha512_libjade input = sha512_spec input.

Lemma sha512_libjade_trust_marker_holds : sha512_libjade_trust_marker.
Proof. exact jade_hash_sha512_correct. Qed.
