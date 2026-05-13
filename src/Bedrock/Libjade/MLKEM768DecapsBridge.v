(** * Libjade.MLKEM768DecapsBridge — Rocq wrapper for the libjade
      ML-KEM-768 decapsulation routine.

 * Purpose
 * -------
 * Consolidate the Rocq-side handles for the libjade
 *   [jade_kem_mlkem_mlkem768_amd64_ref_dec]
 * Jasmin routine into a single named, registry-citable trust-localized
 * artefact that lives next to the other libjade trust assumptions
 * (registered in [src/Bedrock/LibjadeAxioms.v] §3).
 *
 * This is the decapsulation sibling of [MLKEM768KeygenBridge.v] and
 * [MLKEM768EncapsBridge.v]; together they cover the full ML-KEM-768
 * KEM ABI (keygen / enc / dec) exposed by the libjade reference
 * implementation.  Tier 3 R9 of the closure plan.
 *
 * Provenance chain
 * ----------------
 * The declaration [mlkem768_dec_libjade] is the Rocq-side handle for
 * the libjade ML-KEM-768 decapsulation routine.  The end-to-end trust
 * chain is:
 *
 *   Rocq theorem (downstream consumer)
 *     └─ uses [mlkem768_dec_libjade] (declared here)
 *           └─ axiom [Bedrock.LibjadeAxioms.jade_mlkem768_dec_correct]
 *                 └─ formosa-mlkem EasyCrypt artefacts under
 *                    [libjade/submodules/formosa-mlkem/proof/...]
 *                    (presently a vendored-empty git submodule; the
 *                    upstream proofs live in the Cryspen
 *                    formosa-mlkem repository)
 *                 └─ libjade Jasmin source at
 *                    [libjade/oldsrc-should-delete/crypto_kem/mlkem/
 *                     mlkem768/amd64/{ref,avx2}/kem.jazz]
 *                    (export function
 *                       [jade_kem_mlkem_mlkem768_amd64_ref_dec]).
 *
 * ABI (cross-checked against the [include/api.h] in the Jasmin source
 * tree):
 *
 *   #define JADE_KEM_mlkem_mlkem768_amd64_ref_SECRETKEYBYTES  2400
 *   #define JADE_KEM_mlkem_mlkem768_amd64_ref_CIPHERTEXTBYTES 1088
 *   #define JADE_KEM_mlkem_mlkem768_amd64_ref_BYTES             32
 *
 *   int jade_kem_mlkem_mlkem768_amd64_ref_dec(
 *     uint8_t *shared_secret,        // 32 bytes (OUT)
 *     const uint8_t *ciphertext,     // 1088 bytes (IN)
 *     const uint8_t *secret_key      // 2400 bytes (IN)
 *   );
 *
 * Implicit-rejection (FO-transform) nuance
 * ----------------------------------------
 * Per FIPS 203 §7.3 Algorithm 18 (ML-KEM.Decaps), the routine always
 * returns a 32-byte shared secret — even on adversarial / malformed
 * ciphertexts.  The structure of the routine is:
 *
 *   1.  Parse sk into (dk_PKE, ek_PKE, H(ek), z).
 *   2.  m'        := K-PKE.Decrypt(dk_PKE, ct).
 *   3.  (K', r')  := G(m' || H(ek)).               -- candidate SS + coins
 *   4.  c'        := K-PKE.Encrypt(ek_PKE, m', r'). -- re-encryption check
 *   5.  K_bar     := J(z || ct).                    -- implicit-rejection SS
 *   6.  if c == c' then return K' else return K_bar.
 *
 * The branch in step 6 is implemented constant-time in the Jasmin
 * source (see [verify.jinc]'s [__verify] + [__cmov] helpers).  The
 * caller cannot observe via this bridge's signature whether the
 * implicit-rejection branch was taken — the output is always 32 bytes
 * of either K' or K_bar.
 *
 * This means downstream protocol consumers (PQXDH, SPQR) get
 * FIPS-203-compliant IND-CCA2 security automatically: a malformed
 * ciphertext yields a key K_bar that is pseudorandom and
 * indistinguishable (to anyone without [z]) from a fresh random
 * 32-byte string, so protocol-level key confirmation will fail
 * silently — exactly the desired behaviour.
 *
 * (Re-derive from [params.jinc]:
 *   MLKEM_SYMBYTES         = 32.
 *   MLKEM_CIPHERTEXTBYTES  = MLKEM_INDCPA_BYTES
 *                          = K*POLYCOMPRESSEDBYTES + POLYCOMPRESSEDBYTES_DV
 *                          = 3 * 320 + 128
 *                          = 1088.
 *   MLKEM_SECRETKEYBYTES   = 2400 (see keygen bridge for breakdown).
 *   MLKEM_SSBYTES          = MLKEM_SYMBYTES = 32.)
 *
 * Status of the EC artefact (audit-relevant)
 * ------------------------------------------
 * The formosa-mlkem upstream repo (Cryspen) contains in-progress EC
 * proofs of both constant-time and functional correctness against a
 * FIPS-203 reference.  In the current AUCurves checkout the
 * [libjade/submodules/formosa-mlkem/] directory is an empty submodule
 * (git submodule not initialised); the proofs live in the upstream
 * Cryspen formosa-mlkem repository.  Therefore [mlkem768_dec_libjade]
 * is, today, an opaque Rocq [Parameter] with the right ABI shape, and
 * the [_correct] theorem is a [Qed] consequence of the registry
 * placeholder [jade_mlkem768_dec_correct] from [LibjadeAxioms].
 *
 * Upgrading [_correct] to a real Theorem requires either:
 *   (a) initialising the [formosa-mlkem] submodule, porting the
 *       upstream EC functional-correctness proof to Rocq, and
 *       discharging any open admits in the leaf lemmas (NTT, sampling,
 *       FO-transform / implicit-rejection branch),
 *       OR
 *   (b) composing the verified Rocq Jasmin compiler's correctness
 *       theorem with a Rocq-side FIPS-203 ML-KEM-768 spec (the
 *       reference Lean spec lives in [CatCrypt/Crypto/Mlkem.lean] and
 *       can be ported).
 *
 * Both paths preserve the named-Parameter + named-Theorem shape
 * declared here, so downstream consumers (the Rust [pqxdh] / [SPQR]
 * wiring) are unaffected by the upgrade.
 *
 * Audit benefit of this file
 * --------------------------
 * Before this bridge, downstream callers had to reference the raw
 * libjade FFI symbol or restate ad-hoc parameters at the point of
 * use.  After this bridge, [Print Assumptions] on any consumer of
 * [mlkem768_dec_libjade_correct] reports the
 * [Bedrock.LibjadeAxioms.jade_mlkem768_dec_correct] axiom explicitly,
 * with this docstring tying it to the libjade source.
 *
 * See also
 * --------
 * - [src/Bedrock/LibjadeAxioms.v] §3 — full ML-KEM axiom registry
 *   (keygen + encaps + decaps).
 * - [src/Bedrock/Libjade/MLKEM768KeygenBridge.v] — sibling bridge
 *   for ML-KEM-768 keygen.
 * - [src/Bedrock/TrustAxioms.v] — top-level trust registry.
 * - [src/Bedrock/Libjade/SHA512Bridge.v] — sibling bridge for SHA-512.
 * - [src/Bedrock/Libjade/X25519Bridge.v] — sibling bridge for X25519.
 *)

From Stdlib Require Import String ZArith List.
From Stdlib Require Import Init.Byte.
Require Import Bedrock.LibjadeAxioms.
Import ListNotations.

(* ================================================================ *)
(* §1.  The Rocq-side ML-KEM-768 decaps handle                       *)
(* ================================================================ *)

(** [mlkem768_dec_libjade ct sk] is the 32-byte shared secret
    produced by the libjade
    [jade_kem_mlkem_mlkem768_amd64_ref_dec] Jasmin routine
    on the 1088-byte ciphertext [ct] and the 2400-byte secret key
    [sk].

    Input ABI:
      - ciphertext: 1088 bytes (FIPS 203 §7.2 K-PKE ciphertext).
      - secret_key: 2400 bytes (dk_PKE 1152 || ek 1184 || H(ek) 32 || z 32).

    Output ABI:
      - shared_secret: 32 bytes.  This is *always* 32 bytes per FIPS
        203 §7.3 Algorithm 18: on a malformed / adversarial
        ciphertext, the routine returns the FO-transform implicit
        rejection key K_bar = J(z || ct) instead of K' from K-PKE
        decryption.  The bridge signature does not distinguish the
        two cases; the implicit-rejection branch is invisible at this
        level of abstraction.  See the file header for the
        IND-CCA2 / protocol-confirmation discussion.

    Trust: opaque [Parameter], registered in
    [Bedrock.LibjadeAxioms.jade_mlkem768_dec_correct].  See file
    header for the EC provenance and the path to upgrading this to a
    real Theorem. *)
Parameter mlkem768_dec_libjade :
  list Byte.byte (* ct, 1088 bytes *) ->
  list Byte.byte (* sk, 2400 bytes *) ->
  list Byte.byte (* shared_secret, 32 bytes *).

(** Length of the shared-secret output is fixed at 32 bytes per FIPS
    203 §7.3 (and [params.jinc]
    [MLKEM_SSBYTES = MLKEM_SYMBYTES = 32]).  This holds on EVERY
    input — including malformed ciphertexts — because the
    implicit-rejection branch [K_bar = J(z || ct)] also produces 32
    bytes (J = SHAKE-256-32).  Opaque [Parameter] for the same reason
    as [mlkem768_dec_libjade] itself. *)
Parameter mlkem768_dec_libjade_ss_len :
  forall (ct sk : list Byte.byte),
    length ct = 1088%nat ->
    length sk = 2400%nat ->
    length (mlkem768_dec_libjade ct sk) = 32%nat.

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

(** [mlkem768_dec_libjade_correct]: byte-for-byte agreement between
    the libjade-extracted Jasmin routine and an abstract FIPS-203
    ML-KEM-768 decapsulation reference spec.

    Statement shape: for any well-formed 1088-byte [ct] and 2400-byte
    [sk], the 32-byte output [ss] satisfies the FIPS 203 §7.3
    K-Decaps relation, which itself decomposes into:
      (i)  parse sk into (dk_PKE, ek_PKE, H(ek), z),
      (ii) m' := K-PKE.Decrypt(dk_PKE, ct),
      (iii) (K', r') := G(m' || H(ek)),
      (iv) c' := K-PKE.Encrypt(ek_PKE, m', r'),
      (v)  K_bar := J(z || ct),
      (vi) ss = if ct == c' then K' else K_bar.

    We keep this bridge spec-agnostic by stating the equality via
    [jade_mlkem768_dec_correct], which is the registry-level
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
      ML-KEM-768 fnspec to the [__crypto_kem_dec_jazz] Jasmin
      procedure.  Such a theorem would land at
      [src/Bedrock/End2End/MLKEM768/JasminEquivalence.v]. *)
Theorem mlkem768_dec_libjade_correct :
  forall (ct sk : list Byte.byte),
    length ct = 1088%nat ->
    length sk = 2400%nat ->
    (* Registry-level placeholder: the body is [True] today (see
       [LibjadeAxioms.jade_mlkem768_dec_correct]).  Once the registry
       axiom is upgraded to a real FIPS-203 K-Decaps equality, the
       [True] target below will change to the concrete relation
       between [mlkem768_dec_libjade ct sk] and the spec — and this
       theorem becomes a one-line consequence by
       [exact (jade_mlkem768_dec_correct _ _ _).] *)
    True.
Proof.
  intros ct sk _ _.
  set (ss := mlkem768_dec_libjade ct sk).
  exact (jade_mlkem768_dec_correct
           (bytes_to_Zs sk)
           (bytes_to_Zs ct)
           (bytes_to_Zs ss)).
Qed.

(* ================================================================ *)
(* §3.  Audit-trail breadcrumb                                       *)
(* ================================================================ *)

(** Sanity check: the only new axiomatic objects this file introduces
    are the two [Parameter]s above
    ([mlkem768_dec_libjade],
     [mlkem768_dec_libjade_ss_len]).
    The correctness theorem itself is [Qed], reducing to the registry
    placeholder [jade_mlkem768_dec_correct] from
    [Bedrock.LibjadeAxioms].

    This lemma asserts that the registry axiom is usable from this
    file's namespace, ensuring [Print Assumptions] on any consumer of
    [mlkem768_dec_libjade_correct] names it explicitly. *)
Lemma mlkem768_dec_libjade_registered :
  forall (sk ct ss : list Z),
    True.
Proof.
  intros sk ct ss.
  exact (jade_mlkem768_dec_correct sk ct ss).
Qed.

(** Trust-marker breadcrumb (parallels
    [mlkem768_keypair_derand_libjade_trust_marker_holds] in
    [MLKEM768KeygenBridge.v] and [sha512_libjade_trust_marker_holds]
    in [SHA512Bridge.v]).  When the registry placeholder
    [jade_mlkem768_dec_correct] is upgraded from its [True] body to a
    real FIPS-203 K-Decaps Prop, replace the [True] below with the
    upgraded axiom application.  [Require Import
    Bedrock.LibjadeAxioms] above already brings the axiom into scope
    so downstream [Print Assumptions] will list it whenever the
    upgraded axiom is used. *)
Definition mlkem768_dec_libjade_trust_marker : Prop := True.

Lemma mlkem768_dec_libjade_trust_marker_holds :
  mlkem768_dec_libjade_trust_marker.
Proof. exact I. Qed.
