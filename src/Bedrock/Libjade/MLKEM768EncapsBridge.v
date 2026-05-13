(** * Libjade.MLKEM768EncapsBridge — Rocq wrapper for the libjade
      ML-KEM-768 derandomised encapsulation routine.

 * Purpose
 * -------
 * Consolidate the Rocq-side handles for the libjade
 *   [jade_kem_mlkem_mlkem768_amd64_ref_enc_derand]
 * Jasmin routine into a single named, registry-citable trust-localized
 * artefact that lives next to the other libjade trust assumptions
 * (registered in [src/Bedrock/LibjadeAxioms.v] §3).
 *
 * This file mirrors the sibling [MLKEM768KeygenBridge.v] for the
 * encapsulation half of the FIPS 203 §7.2 K-Encaps_internal interface.
 *
 * Provenance chain
 * ----------------
 * The declaration [mlkem768_enc_derand_libjade] is the Rocq-side
 * handle for the libjade ML-KEM-768 derandomised encapsulation routine.
 * The end-to-end trust chain is:
 *
 *   Rocq theorem (downstream consumer)
 *     └─ uses [mlkem768_enc_derand_libjade] (declared here)
 *           └─ axiom [Bedrock.LibjadeAxioms.jade_mlkem768_enc_derand_correct]
 *                 └─ formosa-mlkem EasyCrypt artefacts under
 *                    [libjade/submodules/formosa-mlkem/proof/...]
 *                    (presently a vendored-empty git submodule; the
 *                    upstream proofs live in the Cryspen
 *                    formosa-mlkem repository)
 *                 └─ libjade Jasmin source at
 *                    [libjade/oldsrc-should-delete/crypto_kem/mlkem/
 *                     mlkem768/amd64/{ref,avx2}/kem.jazz]
 *                    (export function
 *                       [jade_kem_mlkem_mlkem768_amd64_ref_enc_derand]).
 *
 * ABI (cross-checked against the [include/api.h] in the Jasmin source
 * tree, and against the Rust-side wrapper at
 * [curve25519-jasmin-rs/src/ffi_safe.rs::mlkem768_enc_derand]):
 *
 *   #define JADE_KEM_mlkem_mlkem768_amd64_ref_PUBLICKEYBYTES  1184
 *   #define JADE_KEM_mlkem_mlkem768_amd64_ref_CIPHERTEXTBYTES 1088
 *   #define JADE_KEM_mlkem_mlkem768_amd64_ref_ENCCOINBYTES      32
 *   #define JADE_KEM_mlkem_mlkem768_amd64_ref_BYTES             32
 *
 *   int jade_kem_mlkem_mlkem768_amd64_ref_enc_derand(
 *     uint8_t       *ciphertext,     /* 1088 bytes */
 *     uint8_t       *shared_secret,  /*   32 bytes */
 *     const uint8_t *public_key,     /* 1184 bytes */
 *     const uint8_t *coins           /*   32 bytes */
 *   );
 *
 * The 32-byte [coins] buffer IS the FIPS 203 message [m] —
 * derandomised encapsulation in libjade takes a single 32-byte
 * randomness buffer, which K-Encaps_internal then hashes (together
 * with H(ek)) into the K-PKE.Encrypt randomness and the shared
 * secret.  There is no separate "message" argument in the libjade
 * ABI; what FIPS 203 §7.2 Algorithm 17 calls [m] is what libjade
 * names [fixedrand]/[coins].
 *
 * The 1088-byte ciphertext layout is
 *   ct = (c1 || c2)
 *      = (K*MLKEM_POLYCOMPRESSEDBYTES_D10 || MLKEM_POLYCOMPRESSEDBYTES_D4)
 *      = (3 * 320 || 128)
 *      = (960 || 128) = 1088 bytes.
 *
 * (Re-derive from [params.jinc]:
 *   MLKEM_INDCPA_BYTES = K*POLYCOMPRESSEDBYTES_D10 + POLYCOMPRESSEDBYTES_D4
 *                      = 3*320 + 128 = 1088.)
 *
 * The 32-byte shared secret is the FIPS 203 §7.2 K = J(K_bar || c)
 * output (32 bytes per SHAKE-256 truncation).
 *
 * Status of the EC artefact (audit-relevant)
 * ------------------------------------------
 * As with the keygen bridge, the formosa-mlkem upstream repo (Cryspen)
 * contains in-progress EC proofs of both constant-time and functional
 * correctness against a FIPS-203 reference.  In the current AUCurves
 * checkout the [libjade/submodules/formosa-mlkem/] directory is an
 * empty submodule; the proofs live in the upstream Cryspen
 * formosa-mlkem repository.  Therefore [mlkem768_enc_derand_libjade]
 * is, today, an opaque Rocq [Parameter] with the right ABI shape, and
 * the [_correct] theorem is a [Qed] consequence of the registry
 * placeholder [jade_mlkem768_enc_derand_correct] from [LibjadeAxioms].
 *
 * Upgrading [_correct] to a real Theorem requires either:
 *   (a) initialising the [formosa-mlkem] submodule, porting the
 *       upstream EC functional-correctness proof to Rocq, and
 *       discharging any open admits in the leaf lemmas (NTT,
 *       sampling, FO-transform K-encaps decomposition), OR
 *   (b) composing the verified Rocq Jasmin compiler's correctness
 *       theorem with a Rocq-side FIPS-203 ML-KEM-768 spec (the
 *       reference Lean spec lives in [CatCrypt/Crypto/Mlkem.lean]
 *       and can be ported).
 *
 * Both paths preserve the named-Parameter + named-Theorem shape
 * declared here, so downstream consumers (the Rust [pqxdh] / [SPQR]
 * wiring at [curve25519-jasmin-rs/src/pqxdh.rs]) are unaffected by
 * the upgrade.
 *
 * Audit benefit of this file
 * --------------------------
 * Before this bridge, downstream callers had to reference the raw
 * libjade FFI symbol or restate ad-hoc parameters at the point of
 * use.  After this bridge, [Print Assumptions] on any consumer of
 * [mlkem768_enc_derand_libjade_correct] reports the
 * [Bedrock.LibjadeAxioms.jade_mlkem768_enc_derand_correct] axiom
 * explicitly, with this docstring tying it to the libjade source.
 *
 * See also
 * --------
 * - [src/Bedrock/Libjade/MLKEM768KeygenBridge.v] — sibling bridge
 *   for the K-KeyGen half.
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
(* §1.  The Rocq-side ML-KEM-768 encaps handle                       *)
(* ================================================================ *)

(** [mlkem768_enc_derand_libjade pk coins] is the pair
    [(ciphertext, shared_secret)] produced by the libjade
    [jade_kem_mlkem_mlkem768_amd64_ref_enc_derand] Jasmin routine on
    the 1184-byte public key [pk] and the 32-byte randomness buffer
    [coins].  Per FIPS 203 §7.2 the 32-byte [coins] argument IS the
    K-Encaps_internal message [m]; libjade fuses the "message" and
    "coins" of the FIPS spec into a single 32-byte buffer because
    K-Encaps_internal is itself derandomised by [m] alone.

    Input ABI:
      - public_key: 1184 bytes (ek_PKE 1152 || rho 32)
      - coins:        32 bytes (= FIPS 203 message [m])

    Output ABI:
      - ciphertext:   1088 bytes (c1 = 3*320 || c2 = 128)
      - shared_secret: 32 bytes (K = J(K_bar || c))

    Trust: opaque [Parameter], registered in
    [Bedrock.LibjadeAxioms.jade_mlkem768_enc_derand_correct].  See
    file header for the EC provenance and the path to upgrading this
    to a real Theorem. *)
Parameter mlkem768_enc_derand_libjade :
  list Byte.byte (* public_key, 1184 bytes *) ->
  list Byte.byte (* coins, 32 bytes (= FIPS 203 message m) *) ->
  list Byte.byte (* ciphertext, 1088 bytes *) *
  list Byte.byte (* shared_secret, 32 bytes *).

(** Length of the ciphertext component is fixed at 1088 bytes per
    FIPS 203 §7.2 (and [params.jinc]
    [MLKEM_INDCPA_BYTES = K*POLYCOMPRESSEDBYTES_D10
                        + POLYCOMPRESSEDBYTES_D4
                        = 3*320 + 128 = 1088]).
    Opaque [Parameter] for the same reason as
    [mlkem768_enc_derand_libjade] itself. *)
Parameter mlkem768_enc_derand_libjade_ct_len :
  forall (pk coins : list Byte.byte),
    length pk = 1184%nat ->
    length coins = 32%nat ->
    length (fst (mlkem768_enc_derand_libjade pk coins)) = 1088%nat.

(** Length of the shared-secret component is fixed at 32 bytes
    (SHAKE-256 truncated to [MLKEM_SYMBYTES = 32] per FIPS 203
    §7.2). *)
Parameter mlkem768_enc_derand_libjade_ss_len :
  forall (pk coins : list Byte.byte),
    length pk = 1184%nat ->
    length coins = 32%nat ->
    length (snd (mlkem768_enc_derand_libjade pk coins)) = 32%nat.

(* ================================================================ *)
(* §2.  Correctness theorem (Qed against registry placeholder)       *)
(* ================================================================ *)

(** Conversion from a byte list to a list of [Z], used to feed the
    [Bedrock.LibjadeAxioms] registry axioms (which are typed on
    [list Z] for compatibility with the bedrock2 word model).
    Mirrors the [bytes_to_Zs] helper in [MLKEM768KeygenBridge.v] and
    [X25519Bridge.v]. *)
Definition bytes_to_Zs (bs : list Byte.byte) : list Z :=
  map (fun b => Z.of_N (Byte.to_N b)) bs.

(** [mlkem768_enc_derand_libjade_correct]: byte-for-byte agreement
    between the libjade-extracted Jasmin routine and an abstract
    FIPS-203 ML-KEM-768 reference spec.

    Statement shape: for any well-formed 1184-byte public key [pk]
    and 32-byte randomness [coins], the output pair [(ct, ss)]
    satisfies the FIPS 203 §7.2 K-Encaps_internal relation.  We
    keep this bridge spec-agnostic by stating the equality via
    [jade_mlkem768_enc_derand_correct], which is the registry-level
    placeholder (currently a [True]-shaped axiom).

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
      ML-KEM-768 fnspec to the [__crypto_kem_enc_jazz] Jasmin
      procedure.  Such a theorem would land at
      [src/Bedrock/End2End/MLKEM768/JasminEquivalence.v]. *)
Theorem mlkem768_enc_derand_libjade_correct :
  forall (pk coins : list Byte.byte),
    length pk = 1184%nat ->
    length coins = 32%nat ->
    (* Registry-level placeholder: the body is [True] today (see
       [LibjadeAxioms.jade_mlkem768_enc_derand_correct]).  Once the
       registry axiom is upgraded to a real FIPS-203 K-Encaps_internal
       equality, the [True] target below will change to the concrete
       relation between [mlkem768_enc_derand_libjade pk coins] and
       the spec — and this theorem becomes a one-line consequence by
       [exact (jade_mlkem768_enc_derand_correct _ _ _ _).] *)
    True.
Proof.
  intros pk coins _ _.
  set (ctss := mlkem768_enc_derand_libjade pk coins).
  exact (jade_mlkem768_enc_derand_correct
           (bytes_to_Zs pk)
           (bytes_to_Zs coins)
           (bytes_to_Zs (fst ctss))
           (bytes_to_Zs (snd ctss))).
Qed.

(* ================================================================ *)
(* §3.  Audit-trail breadcrumb                                       *)
(* ================================================================ *)

(** Sanity check: the only new axiomatic objects this file introduces
    are the three [Parameter]s above
    ([mlkem768_enc_derand_libjade],
     [mlkem768_enc_derand_libjade_ct_len],
     [mlkem768_enc_derand_libjade_ss_len]).
    The correctness theorem itself is [Qed], reducing to the registry
    placeholder [jade_mlkem768_enc_derand_correct] from
    [Bedrock.LibjadeAxioms].

    This lemma asserts that the registry axiom is usable from this
    file's namespace, ensuring [Print Assumptions] on any consumer
    of [mlkem768_enc_derand_libjade_correct] names it explicitly. *)
Lemma mlkem768_enc_derand_libjade_registered :
  forall (pk coins ct ss : list Z),
    True.
Proof.
  intros pk coins ct ss.
  exact (jade_mlkem768_enc_derand_correct pk coins ct ss).
Qed.

(** Trust-marker breadcrumb (parallels
    [mlkem768_keypair_derand_libjade_trust_marker_holds] in the
    keygen bridge, and [sha512_libjade_trust_marker_holds] in
    [SHA512Bridge.v]).  When the registry placeholder
    [jade_mlkem768_enc_derand_correct] is upgraded from its [True]
    body to a real FIPS-203 K-Encaps_internal Prop, replace the
    [True] below with the upgraded axiom application.  [Require
    Import Bedrock.LibjadeAxioms] above already brings the axiom
    into scope so downstream [Print Assumptions] will list it
    whenever the upgraded axiom is used. *)
Definition mlkem768_enc_derand_libjade_trust_marker : Prop := True.

Lemma mlkem768_enc_derand_libjade_trust_marker_holds :
  mlkem768_enc_derand_libjade_trust_marker.
Proof. exact I. Qed.
