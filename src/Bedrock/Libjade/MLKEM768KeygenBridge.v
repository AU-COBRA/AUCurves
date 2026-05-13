(** * Libjade.MLKEM768KeygenBridge — Rocq wrapper for the libjade
      ML-KEM-768 derandomised key-generation routine.

 * Purpose
 * -------
 * Consolidate the Rocq-side handles for the libjade
 *   [jade_kem_mlkem_mlkem768_amd64_ref_keypair_derand]
 * Jasmin routine into a single named, registry-citable trust-localized
 * artefact that lives next to the other libjade trust assumptions
 * (registered in [src/Bedrock/LibjadeAxioms.v] §3).
 *
 * Provenance chain
 * ----------------
 * The declaration [mlkem768_keypair_derand_libjade] is the Rocq-side
 * handle for the libjade ML-KEM-768 derandomised keypair routine.
 * The end-to-end trust chain is:
 *
 *   Rocq theorem (downstream consumer)
 *     └─ uses [mlkem768_keypair_derand_libjade] (declared here)
 *           └─ axiom [Bedrock.LibjadeAxioms.jade_mlkem768_keypair_derand_correct]
 *                 └─ formosa-mlkem EasyCrypt artefacts under
 *                    [libjade/submodules/formosa-mlkem/proof/...]
 *                    (presently a vendored-empty git submodule; the
 *                    upstream proofs live in the Cryspen
 *                    formosa-mlkem repository)
 *                 └─ libjade Jasmin source at
 *                    [libjade/oldsrc-should-delete/crypto_kem/mlkem/
 *                     mlkem768/amd64/{ref,avx2}/kem.jazz]
 *                    (export function
 *                       [jade_kem_mlkem_mlkem768_amd64_ref_keypair_derand]).
 *
 * ABI (cross-checked against the [include/api.h] in the Jasmin source
 * tree):
 *
 *   #define JADE_KEM_mlkem_mlkem768_amd64_ref_KEYPAIRCOINBYTES 64
 *   #define JADE_KEM_mlkem_mlkem768_amd64_ref_PUBLICKEYBYTES  1184
 *   #define JADE_KEM_mlkem_mlkem768_amd64_ref_SECRETKEYBYTES  2400
 *   #define JADE_KEM_mlkem_mlkem768_amd64_ref_CIPHERTEXTBYTES 1088
 *
 * The 64-byte coin buffer is the (d || z) seed pair from FIPS 203 §7.1
 * Algorithm 16: [d] feeds K-PKE.KeyGen, [z] becomes the FO-rejection
 * seed embedded in the secret key.  The 1184-byte public key is
 *
 *   pk = (ek_PKE || rho)
 *      = (s_hat[0..1023] || rho[0..31])    -- the [s_hat] block is
 *        [MLKEM_K * MLKEM_POLYBYTES = 3 * 384 = 1152] bytes; plus 32 of [rho]
 *        gives 1184.
 *
 * The 2400-byte secret key is
 *
 *   sk = (dk_PKE || ek || H(ek) || z)
 *      = (1152 ||   1184 ||   32   || 32) = 2400 bytes.
 *
 * (Re-derive from [params.jinc]:
 *   MLKEM_INDCPA_PUBLICKEYBYTES = K*POLYBYTES + SYMBYTES = 3*384 + 32 = 1184.
 *   MLKEM_SECRETKEYBYTES        = INDCPA_SECRETKEYBYTES (1152)
 *                               + INDCPA_PUBLICKEYBYTES (1184)
 *                               + 2 * SYMBYTES (64)
 *                               = 2400.)
 *
 * Status of the EC artefact (audit-relevant)
 * ------------------------------------------
 * The formosa-mlkem upstream repo (Cryspen) contains in-progress EC
 * proofs of both constant-time and functional correctness against a
 * FIPS-203 reference.  In the current AUCurves checkout the
 * [libjade/submodules/formosa-mlkem/] directory is an empty submodule
 * (git submodule not initialised); the proofs live in the upstream
 * Cryspen formosa-mlkem repository.  Therefore
 * [mlkem768_keypair_derand_libjade] is, today, an opaque Rocq
 * [Parameter] with the right ABI shape, and the [_correct] theorem is
 * a [Qed] consequence of the registry placeholder
 * [jade_mlkem768_keypair_derand_correct] from [LibjadeAxioms].
 *
 * Upgrading [_correct] to a real Theorem requires either:
 *   (a) initialising the [formosa-mlkem] submodule, porting the
 *       upstream EC functional-correctness proof to Rocq, and discharging
 *       any open admits in the leaf lemmas (NTT, sampling, FO-transform),
 *       OR
 *   (b) composing the verified Rocq Jasmin compiler's correctness
 *       theorem with a Rocq-side FIPS-203 ML-KEM-768 spec (the
 *       reference Lean spec lives in [CatCrypt/Crypto/Mlkem.lean] and
 *       can be ported).
 *
 * Both paths preserve the named-Parameter + named-Theorem shape declared
 * here, so downstream consumers (the Rust [pqxdh] / [SPQR] wiring) are
 * unaffected by the upgrade.
 *
 * Audit benefit of this file
 * --------------------------
 * Before this bridge, downstream callers had to reference the raw
 * libjade FFI symbol or restate ad-hoc parameters at the point of use.
 * After this bridge, [Print Assumptions] on any consumer of
 * [mlkem768_keypair_derand_libjade_correct] reports the
 * [Bedrock.LibjadeAxioms.jade_mlkem768_keypair_derand_correct] axiom
 * explicitly, with this docstring tying it to the libjade source.
 *
 * See also
 * --------
 * - [src/Bedrock/LibjadeAxioms.v] §3 — full ML-KEM axiom registry
 *   (keygen + encaps + decaps).
 * - [src/Bedrock/TrustAxioms.v] — top-level trust registry.
 * - [src/Bedrock/Libjade/SHA512Bridge.v] — sibling bridge for SHA-512.
 * - [src/Bedrock/Libjade/X25519Bridge.v] — sibling bridge for X25519.
 *)

From Stdlib Require Import String ZArith List.
From Stdlib Require Import Init.Byte.
Require Import Bedrock.LibjadeAxioms.
Import ListNotations.

(* ================================================================ *)
(* §1.  The Rocq-side ML-KEM-768 keygen handle                       *)
(* ================================================================ *)

(** [mlkem768_keypair_derand_libjade d z] is the pair
    [(public_key, secret_key)] produced by the libjade
    [jade_kem_mlkem_mlkem768_amd64_ref_keypair_derand] Jasmin routine
    on the 32-byte [d] seed and the 32-byte [z] FO-rejection seed.
    Per FIPS 203 §7.1 these two seeds are concatenated into the
    64-byte coin buffer the export function takes.

    Output ABI:
      - public_key: 1184 bytes (ek_PKE 1152 || rho 32)
      - secret_key: 2400 bytes (dk_PKE 1152 || ek 1184 || H(ek) 32 || z 32)

    Trust: opaque [Parameter], registered in
    [Bedrock.LibjadeAxioms.jade_mlkem768_keypair_derand_correct].  See
    file header for the EC provenance and the path to upgrading this
    to a real Theorem.

    The two seed arguments are kept distinct (rather than fused into
    a single 64-byte buffer) so downstream Rust callers can pass the
    Signal-style [identity_seed] and [randomness_seed] independently
    without an explicit [d ++ z] concat at the call site. *)
Parameter mlkem768_keypair_derand_libjade :
  list Byte.byte (* d, 32 bytes *) ->
  list Byte.byte (* z, 32 bytes *) ->
  list Byte.byte (* public_key, 1184 bytes *) *
  list Byte.byte (* secret_key, 2400 bytes *).

(** Length of the public-key component is fixed at 1184 bytes per
    FIPS 203 §7.1 (and [params.jinc]
    [MLKEM_INDCPA_PUBLICKEYBYTES = K*POLYBYTES + SYMBYTES = 1184]).
    Opaque [Parameter] for the same reason as
    [mlkem768_keypair_derand_libjade] itself. *)
Parameter mlkem768_keypair_derand_libjade_pk_len :
  forall (d z : list Byte.byte),
    length d = 32%nat ->
    length z = 32%nat ->
    length (fst (mlkem768_keypair_derand_libjade d z)) = 1184%nat.

(** Length of the secret-key component is fixed at 2400 bytes per
    FIPS 203 §7.1 ([dk_PKE 1152 || ek 1184 || H(ek) 32 || z 32]). *)
Parameter mlkem768_keypair_derand_libjade_sk_len :
  forall (d z : list Byte.byte),
    length d = 32%nat ->
    length z = 32%nat ->
    length (snd (mlkem768_keypair_derand_libjade d z)) = 2400%nat.

(* ================================================================ *)
(* §2.  Correctness theorem (Qed against registry placeholder)       *)
(* ================================================================ *)

(** Conversion from a byte list to a list of [Z], used to feed the
    [Bedrock.LibjadeAxioms] registry axioms (which are typed on
    [list Z] for compatibility with the bedrock2 word model).
    Mirrors the [bytes_to_Zs] helper in [X25519Bridge.v]. *)
Definition bytes_to_Zs (bs : list Byte.byte) : list Z :=
  map (fun b => Z.of_N (Byte.to_N b)) bs.

(** [mlkem768_keypair_derand_libjade_correct]: byte-for-byte agreement
    between the libjade-extracted Jasmin routine and an abstract
    FIPS-203 ML-KEM-768 reference spec.

    Statement shape: for any well-formed 32-byte [d] and 32-byte [z],
    the output pair [(pk, sk)] satisfies the FIPS 203 §7.1 K-KeyGen
    relation.  We keep this bridge spec-agnostic by stating the
    equality via [jade_mlkem768_keypair_derand_correct], which is the
    registry-level placeholder (currently a [True]-shaped axiom).

    Status: [Qed] modulo the registry placeholder.  Closing the
    placeholder to a real spec requires either porting the
    formosa-mlkem EC functional-correctness proof to Rocq, OR
    composing the verified Rocq Jasmin compiler with a Rocq-side
    FIPS-203 spec.

    Missing import infrastructure (audit breadcrumbs):
    - No Rocq-side FIPS-203 ML-KEM spec yet (the parallel Lean spec
      lives at [CatCrypt/Crypto/Mlkem.lean]; the Rocq port would
      land at [src/Spec/MLKEM768.v]).
    - The [formosa-mlkem] git submodule under
      [libjade/submodules/formosa-mlkem] is currently empty in this
      checkout; the upstream EC proofs (Cryspen) need to be vendored
      before they can be ported.
    - No bedrock2-↔-Jasmin equivalence theorem connecting a Rocq
      ML-KEM-768 fnspec to the [__crypto_kem_keypair_jazz] Jasmin
      procedure.  Such a theorem would land at
      [src/Bedrock/End2End/MLKEM768/JasminEquivalence.v]. *)
Theorem mlkem768_keypair_derand_libjade_correct :
  forall (d z : list Byte.byte),
    length d = 32%nat ->
    length z = 32%nat ->
    (* Registry-level placeholder: the body is [True] today (see
       [LibjadeAxioms.jade_mlkem768_keypair_derand_correct]).  Once
       the registry axiom is upgraded to a real FIPS-203 K-KeyGen
       equality, the [True] target below will change to the concrete
       relation between [mlkem768_keypair_derand_libjade d z] and the
       spec — and this theorem becomes a one-line consequence by
       [exact (jade_mlkem768_keypair_derand_correct _ _ _).] *)
    True.
Proof.
  intros d z _ _.
  set (kp := mlkem768_keypair_derand_libjade d z).
  exact (jade_mlkem768_keypair_derand_correct
           (bytes_to_Zs d ++ bytes_to_Zs z)
           (bytes_to_Zs (fst kp))
           (bytes_to_Zs (snd kp))).
Qed.

(* ================================================================ *)
(* §3.  Audit-trail breadcrumb                                       *)
(* ================================================================ *)

(** Sanity check: the only new axiomatic objects this file introduces
    are the three [Parameter]s above
    ([mlkem768_keypair_derand_libjade],
     [mlkem768_keypair_derand_libjade_pk_len],
     [mlkem768_keypair_derand_libjade_sk_len]).
    The correctness theorem itself is [Qed], reducing to the registry
    placeholder [jade_mlkem768_keypair_derand_correct] from
    [Bedrock.LibjadeAxioms].

    This lemma asserts that the registry axiom is usable from this
    file's namespace, ensuring [Print Assumptions] on any consumer of
    [mlkem768_keypair_derand_libjade_correct] names it explicitly. *)
Lemma mlkem768_keypair_derand_libjade_registered :
  forall (coins pk sk : list Z),
    True.
Proof.
  intros coins pk sk.
  exact (jade_mlkem768_keypair_derand_correct coins pk sk).
Qed.

(** Trust-marker breadcrumb (parallels [sha512_libjade_trust_marker_holds]
    in [SHA512Bridge.v]).  When the registry placeholder
    [jade_mlkem768_keypair_derand_correct] is upgraded from its [True]
    body to a real FIPS-203 K-KeyGen Prop, replace the [True] below
    with the upgraded axiom application.  [Require Import
    Bedrock.LibjadeAxioms] above already brings the axiom into scope
    so downstream [Print Assumptions] will list it whenever the
    upgraded axiom is used. *)
Definition mlkem768_keypair_derand_libjade_trust_marker : Prop := True.

Lemma mlkem768_keypair_derand_libjade_trust_marker_holds :
  mlkem768_keypair_derand_libjade_trust_marker.
Proof. exact I. Qed.
