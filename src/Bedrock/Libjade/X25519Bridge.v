(** * Libjade.X25519Bridge — Rocq wrapper for the libjade X25519 routines.
 *
 * Purpose
 * -------
 * Consolidate the Rocq-side handles for the libjade
 *   [jade_scalarmult_curve25519_amd64_mulx]            (variable-base) and
 *   [jade_scalarmult_curve25519_amd64_mulx_base]       (base-point)
 * Jasmin routines into a single named, registry-citable trust-localized
 * pair that lives next to the other libjade trust assumptions
 * (registered in [src/Bedrock/LibjadeAxioms.v]).
 *
 * Provenance chain
 * ----------------
 * The two declarations [x25519_libjade] and [x25519_libjade_base] are the
 * Rocq-side handles for the libjade scalarmult routines on Curve25519.
 * The end-to-end trust chain is:
 *
 *   Rocq theorem (downstream consumer)
 *     └─ uses [x25519_libjade] / [x25519_libjade_base] (declared here)
 *           └─ axioms
 *              [Bedrock.LibjadeAxioms.jade_curve25519_x25519_correct]
 *              [Bedrock.LibjadeAxioms.jade_curve25519_x25519_base_correct]
 *                 └─ libjade EasyCrypt artefact at
 *                    [libjade/proof/crypto_scalarmult/curve25519/amd64/
 *                     mulx/extracted_ct_proof.ec]
 *                 └─ functional-correctness skeleton at
 *                    [formosa-25519/proof/crypto_scalarmult/curve25519/
 *                     amd64/mulx/CorrectnessProof_Mulx.ec]
 *                 └─ libjade Jasmin source at
 *                    [libjade/oldsrc-should-delete/crypto_scalarmult/
 *                     curve25519/amd64/mulx/scalarmult.jazz]
 *                    (export functions
 *                       [jade_scalarmult_curve25519_amd64_mulx],
 *                       [jade_scalarmult_curve25519_amd64_mulx_base]).
 *
 * Reference Rocq spec
 * -------------------
 * The mathematical specification of X25519 (RFC 7748 §5) is captured in
 * the bedrock2 fiat-crypto pipeline at
 *   [src/Bedrock/End2End/X25519_64/MontgomeryLadder64.v]
 * via [Crypto.Spec.Curve25519] (clamp / Montgomery ladder / encode).
 * The bridge below is intentionally agnostic to a particular Rocq spec:
 * the [_correct] theorems state byte-array equality with whatever
 * abstract spec is wired through [LibjadeAxioms].
 *
 * Status of the EC artefacts (audit-relevant)
 * -------------------------------------------
 * - [libjade/proof/.../extracted_ct_proof.ec] proves constant-time only
 *   (a [proc; inline *; sim] equivalence of the leakage trace).
 * - [formosa-25519/proof/.../CorrectnessProof_Mulx.ec] contains the
 *   skeleton for functional correctness against [Curve25519_Spec.ec]'s
 *   [spec_scalarmult] / [spec_scalarmult_base], but several leaf
 *   lemmas (e.g. [h_mul_a24_mulx], [h_mul_rsr_mulx], [h_sqr_rr_mulx])
 *   are presently [admit]ted in the source — see lines 12-43 of that
 *   file.  The high-level ladder/encode composition is closed modulo
 *   those leaf admits.
 *
 * Therefore [x25519_libjade] and [x25519_libjade_base] are, today,
 * opaque Rocq [Parameter]s with the right shape, and the two
 * [_correct] theorems are [Admitted] with breadcrumbs naming the
 * missing import infrastructure.  Upgrading them to real Theorems
 * requires either:
 *   (a) porting the formosa-25519 EC functional-correctness proof
 *       (and discharging its open [admit]s) to Rocq, OR
 *   (b) composing the verified Rocq Jasmin compiler's correctness
 *       theorem with a Rocq-side RFC 7748 X25519 spec
 *       (which exists in fiat-crypto via the [montladder] /
 *       [Crypto.Spec.Curve25519] chain).
 *
 * Both paths preserve the named-Parameter and named-[Admitted]-theorem
 * shapes declared here, so downstream consumers need not change when
 * this upgrade lands.
 *
 * Audit benefit of this file
 * --------------------------
 * Before this bridge, downstream callers had to either reference the
 * raw libjade FFI symbol or restate ad-hoc parameters at the point of
 * use.  After this bridge, [Print Assumptions] on any consumer points
 * at [x25519_libjade] / [x25519_libjade_base] declared HERE, with this
 * docstring explicitly tying them to
 * [jade_curve25519_x25519_correct] and
 * [jade_curve25519_x25519_base_correct] in [Bedrock.LibjadeAxioms].
 *
 * See also
 * --------
 * - [src/Bedrock/LibjadeAxioms.v] §2 — full libjade-axiom registry
 *   (X25519 mulx/ref4/ref5 variants).
 * - [src/Bedrock/TrustAxioms.v] — top-level trust registry.
 * - [src/Bedrock/End2End/X25519_64/MontgomeryLadder64.v] — fiat-crypto
 *   reference Rocq spec for X25519 (Montgomery ladder + clamp).
 * - [src/Bedrock/Libjade/SHA512Bridge.v] — sibling bridge for SHA-512;
 *   same Parameter+Admitted pattern.
 *)

From Stdlib Require Import String ZArith List.
From Stdlib Require Import Init.Byte.
Require Import Bedrock.LibjadeAxioms.
Require Import Bedrock.Libjade.X25519Spec.
Import ListNotations.

(* ================================================================ *)
(* §1.  The Rocq-side X25519 handles                                 *)
(* ================================================================ *)

(** [x25519_libjade scalar point] is the 32-byte X25519 shared-secret
    output computed at link time by the libjade
    [jade_scalarmult_curve25519_amd64_mulx] Jasmin routine on the
    32-byte [scalar] (clamped per RFC 7748) and 32-byte little-endian
    [point] (u-coordinate, high bit cleared).

    Now declared as the Parameter [x25519_libjade] in
    [Bedrock.LibjadeAxioms] (so the [jade_curve25519_x25519_correct]
    axiom can directly reference it as a byte equality against the Rocq
    RFC 7748 reference spec [Bedrock.Libjade.X25519Spec.x25519_spec]);
    this bridge re-exports the symbol for downstream call sites that
    historically imported it from this file.  Upgraded 2026-05-14 from
    local opaque Parameter to Notation re-export of the registry-level
    Parameter (A109). *)
Notation x25519_libjade :=
  Bedrock.LibjadeAxioms.x25519_libjade (only parsing).

(** [x25519_libjade_base scalar] is the 32-byte X25519 public-key
    output computed at link time by the libjade
    [jade_scalarmult_curve25519_amd64_mulx_base] Jasmin routine on the
    32-byte [scalar] (clamped per RFC 7748) and the fixed base-point
    u-coordinate (u = 9, little-endian).

    Now declared as the Parameter [x25519_base_libjade] in
    [Bedrock.LibjadeAxioms] (so the [jade_curve25519_x25519_base_correct]
    axiom can directly reference it as a byte equality against the Rocq
    RFC 7748 reference spec [Bedrock.Libjade.X25519Spec.x25519_base_spec]);
    this bridge re-exports the symbol under the historical name
    [x25519_libjade_base] for downstream call sites that imported it
    from this file.  Upgraded 2026-05-14 from local opaque Parameter to
    Notation re-export of the registry-level Parameter (A110). *)
Notation x25519_libjade_base := Bedrock.LibjadeAxioms.x25519_base_libjade (only parsing).

(** Length of the [x25519_libjade] output is fixed at 32 bytes per
    RFC 7748 §5.  Now provable as a [Lemma] from the
    [jade_curve25519_x25519_correct] axiom plus [x25519_spec_length];
    the previous [Parameter] form (which additionally required
    [length scalar = 32] and [length point = 32]) was removed on
    2026-05-14 in favor of the unconditional length lemma below. *)
Lemma x25519_libjade_len :
  forall (scalar point : list Byte.byte),
    length (x25519_libjade scalar point) = 32%nat.
Proof.
  intros scalar point.
  rewrite jade_curve25519_x25519_correct.
  apply x25519_spec_length.
Qed.

(** Length of the [x25519_libjade_base] output is fixed at 32 bytes per
    RFC 7748 §6.1.  Now provable as a [Lemma] from the
    [jade_curve25519_x25519_base_correct] axiom plus
    [x25519_base_spec_length]; the previous [Parameter] form (which
    additionally required [length scalar = 32]) was removed on
    2026-05-14 in favor of the unconditional length lemma below. *)
Lemma x25519_libjade_base_len :
  forall (scalar : list Byte.byte),
    length (x25519_libjade_base scalar) = 32%nat.
Proof.
  intro scalar.
  rewrite jade_curve25519_x25519_base_correct.
  apply x25519_base_spec_length.
Qed.

(* ================================================================ *)
(* §2.  Correctness theorems (Admitted — see breadcrumbs)            *)
(* ================================================================ *)

(** [x25519_libjade_correct]: byte-for-byte agreement between the
    libjade-extracted [jade_scalarmult_curve25519_amd64_mulx] Jasmin
    routine and the Rocq RFC 7748 §5 reference spec.

    Statement shape: for any 32-byte [scalar] and 32-byte [point], the
    output of [x25519_libjade scalar point] is exactly the RFC 7748 §5
    X25519 shared-secret — i.e. [montladder] of [clamp(scalar)] applied
    to [decode_u(point)], re-encoded to 32 little-endian bytes — as
    computed by [Bedrock.Libjade.X25519Spec.x25519_spec].

    Upgraded 2026-05-14 from [True] placeholder to concrete byte
    equality against [x25519_spec] (A109). *)
Theorem x25519_libjade_correct :
  forall (scalar point : list Byte.byte),
    x25519_libjade scalar point = x25519_spec scalar point.
Proof.
  intros scalar point; apply jade_curve25519_x25519_correct.
Qed.

(** Headline byte equality re-export under the bridge's naming
    convention.  Identical to [x25519_libjade_correct]; only the name
    differs. *)
Lemma jade_curve25519_x25519_correct_byte_eq :
  forall (scalar point : list Byte.byte),
    x25519_libjade scalar point = x25519_spec scalar point.
Proof. intros scalar point; apply jade_curve25519_x25519_correct. Qed.

(** Length of the [x25519_libjade_correct] alias is fixed at 32 bytes. *)
Lemma x25519_libjade_correct_len :
  forall (scalar point : list Byte.byte),
    length (x25519_libjade scalar point) = 32%nat.
Proof. intros scalar point; apply x25519_libjade_len. Qed.

(** [x25519_libjade_base_correct]: byte-for-byte agreement between the
    libjade-extracted [jade_scalarmult_curve25519_amd64_mulx_base] Jasmin
    routine and the Rocq RFC 7748 §6.1 reference spec at u = 9.

    Upgraded 2026-05-14 from [True] placeholder to concrete byte equality
    against [Bedrock.Libjade.X25519Spec.x25519_base_spec] (A110). *)
Theorem x25519_libjade_base_correct :
  forall (scalar : list Byte.byte),
    x25519_libjade_base scalar = x25519_base_spec scalar.
Proof.
  intro scalar; apply jade_curve25519_x25519_base_correct.
Qed.

(** Headline byte equality re-export under the bridge's naming
    convention.  Identical to [x25519_libjade_base_correct]; only the
    name differs. *)
Lemma jade_curve25519_x25519_base_correct_byte_eq :
  forall (scalar : list Byte.byte),
    x25519_libjade_base scalar = x25519_base_spec scalar.
Proof. intro scalar; apply jade_curve25519_x25519_base_correct. Qed.

(** Length of the [x25519_libjade_base] output is fixed at 32 bytes per
    RFC 7748 §6.1.  Now provable as a [Lemma] from the
    [jade_curve25519_x25519_base_correct] axiom plus
    [x25519_base_spec_length]; no additional axiom is needed.

    Before 2026-05-14 this was an opaque Parameter; concretizing the
    registry slot lets us discharge it from the spec's length theorem. *)
Lemma x25519_libjade_base_correct_len :
  forall scalar, length (x25519_libjade_base scalar) = 32%nat.
Proof.
  intro scalar.
  rewrite jade_curve25519_x25519_base_correct.
  apply x25519_base_spec_length.
Qed.

(* ================================================================ *)
(* §3.  Audit-trail breadcrumb                                       *)
(* ================================================================ *)

(** Citation marker for the trust audit: 2026-05-14, both
    [jade_curve25519_x25519_correct] and
    [jade_curve25519_x25519_base_correct] axioms were upgraded from
    [True] placeholders to concrete byte equalities against
    [Bedrock.Libjade.X25519Spec.x25519_spec] /
    [...x25519_base_spec].  This file's locally-introduced [Parameter]s
    were also removed in favor of [Notation] re-exports of the
    registry-level Parameters, and the previous [Parameter] length
    statements are now Qed [Lemma]s derived from the registry axioms.

    The [_registered] lemmas assert that those two registry axioms are
    usable from this file's namespace, ensuring [Print Assumptions] on
    any consumer of the [_correct] theorems names them explicitly. *)
Lemma x25519_libjade_registered :
  forall (scalar point : list Byte.byte),
    x25519_libjade scalar point = x25519_spec scalar point.
Proof. intros scalar point. exact (jade_curve25519_x25519_correct scalar point). Qed.

(** The base-point registry axiom is usable from this file's namespace,
    ensuring [Print Assumptions] on any consumer of the [_correct]
    theorems names it explicitly.  Upgraded 2026-05-14 from the [True]
    placeholder form to the concrete byte-equality form. *)
Lemma x25519_libjade_base_registered :
  forall (scalar : list Byte.byte),
    x25519_libjade_base scalar = x25519_base_spec scalar.
Proof. intro scalar. exact (jade_curve25519_x25519_base_correct scalar). Qed.
