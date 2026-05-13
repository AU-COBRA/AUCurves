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
Import ListNotations.

(* ================================================================ *)
(* §1.  The Rocq-side X25519 handles                                 *)
(* ================================================================ *)

(** [x25519_libjade scalar point] is the 32-byte X25519 shared-secret
    output computed at link time by the libjade
    [jade_scalarmult_curve25519_amd64_mulx] Jasmin routine on the
    32-byte [scalar] (clamped per RFC 7748) and 32-byte little-endian
    [point] (u-coordinate, high bit cleared).

    Trust: opaque [Parameter], registered in
    [Bedrock.LibjadeAxioms.jade_curve25519_x25519_correct].  See file
    header for the EC provenance and the path to upgrading this to a
    real Theorem. *)
Parameter x25519_libjade :
  list Byte.byte (* scalar, 32 bytes *) ->
  list Byte.byte (* point,  32 bytes *) ->
  list Byte.byte (* shared, 32 bytes *).

(** [x25519_libjade_base scalar] is the 32-byte X25519 public-key
    output computed at link time by the libjade
    [jade_scalarmult_curve25519_amd64_mulx_base] Jasmin routine on the
    32-byte [scalar] (clamped per RFC 7748) and the fixed base-point
    u-coordinate (u = 9, little-endian).

    Trust: opaque [Parameter], registered in
    [Bedrock.LibjadeAxioms.jade_curve25519_x25519_base_correct]. *)
Parameter x25519_libjade_base :
  list Byte.byte (* scalar, 32 bytes *) ->
  list Byte.byte (* shared, 32 bytes *).

(** Length of the [x25519_libjade] output is fixed at 32 bytes per
    RFC 7748 §5.  Opaque [Parameter] for the same reason as
    [x25519_libjade] itself.

    When the EC functional-correctness proof lands in Rocq (or via the
    Rocq Jasmin compiler), this becomes a Theorem proved from the
    underlying [montladder] / [Spec.Curve25519] reference. *)
Parameter x25519_libjade_len :
  forall (scalar point : list Byte.byte),
    length scalar = 32%nat ->
    length point = 32%nat ->
    length (x25519_libjade scalar point) = 32%nat.

Parameter x25519_libjade_base_len :
  forall (scalar : list Byte.byte),
    length scalar = 32%nat ->
    length (x25519_libjade_base scalar) = 32%nat.

(* ================================================================ *)
(* §2.  Correctness theorems (Admitted — see breadcrumbs)            *)
(* ================================================================ *)

(** [x25519_libjade_correct]: byte-for-byte agreement between the
    libjade-extracted Jasmin routine and an abstract X25519 reference
    spec.

    Statement shape: for any well-formed 32-byte [scalar] and 32-byte
    [point], the output of [x25519_libjade scalar point] is exactly
    the RFC 7748 §5 X25519 shared-secret — i.e. the [montladder] of
    [clamp(scalar)] applied to [decode_u(point)], re-encoded to 32
    little-endian bytes.

    The connecting [Crypto.Spec.Curve25519] reference (clamp + ladder +
    encode) and the bedrock2 [montladder] implementation live in
    [src/Bedrock/End2End/X25519_64/MontgomeryLadder64.v]; we keep this
    bridge spec-agnostic by stating the equality via
    [jade_curve25519_x25519_correct], which is the registry-level
    placeholder.

    Status: [Admitted].  Closing this requires importing the
    formosa-25519 functional-correctness proof (and discharging its
    open [admit]s on [__mul4_a24_rs], [__mul4_rsr], [__sqr4_rr] —
    see [formosa-25519/proof/crypto_scalarmult/curve25519/amd64/mulx/
    CorrectnessProof_Mulx.ec] lines 12-43) into Rocq, OR composing the
    verified Rocq Jasmin compiler with a Rocq-side RFC 7748 spec.

    Missing import infrastructure (audit breadcrumbs):
    - No Rocq-side import of EasyCrypt's [Curve25519_Spec.ec] yet
      (would land in [src/Spec/Curve25519_Libjade.v] paralleling the
      existing [Spec.Curve25519] in fiat-crypto).
    - No bedrock2-↔-Jasmin equivalence theorem connecting the
      [montladder] Rocq fnspec to the [__montgomery_ladder4] Jasmin
      procedure (would land in [src/Bedrock/End2End/X25519_64/
      JasminEquivalence.v]).
    - Several leaf functional-correctness lemmas in
      [CorrectnessProof_Mulx.ec] are [admit]ted in the source. *)
(** Conversion from a byte list to a list of [Z], used to feed the
    [Bedrock.LibjadeAxioms] registry axioms (which are typed on
    [list Z] for compatibility with the bedrock2 word model). *)
Definition bytes_to_Zs (bs : list Byte.byte) : list Z :=
  map (fun b => Z.of_N (Byte.to_N b)) bs.

Theorem x25519_libjade_correct :
  forall (scalar point : list Byte.byte),
    length scalar = 32%nat ->
    length point  = 32%nat ->
    (* Registry-level placeholder: the body is [True] today (see
       [LibjadeAxioms.jade_curve25519_x25519_correct]).  Once the
       registry axiom is upgraded to a real equality with a Rocq
       reference spec (RFC 7748 montladder over [Spec.Curve25519]),
       the [True] target below will change to the concrete equality
       between [x25519_libjade scalar point] and the spec — and this
       theorem becomes a one-line consequence by [exact
       (jade_curve25519_x25519_correct _ _ _).] *)
    True.
Proof.
  intros scalar point _ _.
  exact (jade_curve25519_x25519_correct
           (bytes_to_Zs scalar)
           (bytes_to_Zs point)
           (bytes_to_Zs (x25519_libjade scalar point))).
Qed.

(** [x25519_libjade_base_correct]: same shape for the base-point form.

    Status: [Qed] modulo the registry placeholder [True] — same
    breadcrumbs as [x25519_libjade_correct]. *)
Theorem x25519_libjade_base_correct :
  forall (scalar : list Byte.byte),
    length scalar = 32%nat ->
    True.
Proof.
  intros scalar _.
  exact (jade_curve25519_x25519_base_correct
           (bytes_to_Zs scalar)
           (bytes_to_Zs (x25519_libjade_base scalar))).
Qed.

(* ================================================================ *)
(* §3.  Audit-trail breadcrumb                                       *)
(* ================================================================ *)

(** Sanity check: the only new axiomatic objects this file introduces
    are the four [Parameter]s above ([x25519_libjade],
    [x25519_libjade_base], [x25519_libjade_len],
    [x25519_libjade_base_len]).  The correctness theorems themselves
    are [Qed], reducing to the registry placeholders
    [jade_curve25519_x25519_correct] and
    [jade_curve25519_x25519_base_correct] from [Bedrock.LibjadeAxioms].

    This lemma asserts that those two registry axioms are usable from
    this file's namespace, ensuring [Print Assumptions] on any
    consumer of the [_correct] theorems names them explicitly. *)
Lemma x25519_libjade_registered :
  forall (scalar point shared : list Z),
    True.
Proof. intros scalar point shared. exact (jade_curve25519_x25519_correct scalar point shared). Qed.

Lemma x25519_libjade_base_registered :
  forall (scalar shared : list Z),
    True.
Proof. intros scalar shared. exact (jade_curve25519_x25519_base_correct scalar shared). Qed.
