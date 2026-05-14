(** * LibjadeAxioms: trust-localized correctness statements for libjade
      Jasmin primitive symbols linked into curve25519-jasmin-rs.

      Each axiom below states the input/output relation that the
      corresponding libjade Jasmin source is proved to satisfy in
      EasyCrypt (separate formalism, separate kernel).  The provenance
      comment cites the source proof file under
      [$WORKSPACE/libjade/proof/...].

      Status: **None of these axioms are proven in Rocq.**  They are
      named, individually-citable trust assumptions.  Each can be
      independently re-checked by:

        1. Reading the EasyCrypt proof at the cited path, OR
        2. Re-compiling the libjade .jazz source through the verified
           Rocq Jasmin compiler (`$WORKSPACE/jasmin/`)
           and observing that the resulting assembly has these
           semantics by Jasmin compiler correctness (Rocq Qed).

      Replacing this file's contents with actual Rocq proofs requires
      either porting libjade's EC proofs to Rocq, or composing the
      Rocq Jasmin compiler's correctness with a Rocq-side functional
      spec for each Jasmin source.  Both are multi-session efforts;
      both options preserve the named-axiom shape so consumers of
      this file are unaffected.
 *)

From Stdlib Require Import String ZArith List.
From Stdlib Require Import Init.Byte.
Require Import Bedrock.Libjade.SHA256Spec.
Require Import Bedrock.Libjade.SHA512Spec.
Import ListNotations.

(* ================================================================ *)
(* §1.  SHA-2 family                                                 *)
(* ================================================================ *)

(** [jade_hash_sha256_amd64_ref] computes SHA-256 (FIPS 180-4) of the
    [input_length] bytes at [input], writing the 32-byte digest to [hash].

    EC provenance: libjade/proof/crypto_hash/sha256/amd64/ref/extracted_ct_proof.ec
    (constant-time + functional correctness proof in EasyCrypt).

    Functional spec: [Bedrock.Libjade.SHA256Spec.sha256_spec], a pure-Gallina
    FIPS 180-4 reference SHA-256 (constants, message schedule, compression
    rounds, padding) authored locally so this slot can carry a real byte
    equality rather than a [True] placeholder.

    The libjade-side function handle [sha256_libjade] is declared here so
    that the registry slot can reference it concretely; the bridge file at
    [Bedrock.Libjade.SHA256Bridge] re-exports the same handle (and adds a
    matching length axiom) for downstream consumers. *)
Parameter sha256_libjade : list Byte.byte -> list Byte.byte.

(** Concrete byte equality between the libjade SHA-256 routine and the
    Rocq FIPS-180-4 reference spec.  Upgraded from a [True] placeholder
    on 2026-05-14; the bridge consumes this as
    [Bedrock.Libjade.SHA256Bridge.jade_hash_sha256_correct_byte_eq]. *)
Axiom jade_hash_sha256_correct :
  forall (input : list Byte.byte),
    sha256_libjade input = sha256_spec input.

(** Same provenance class for SHA-512 (used by Ed25519 + XEdDSA + HKDF-SHA-512).

    EC provenance: libjade/proof/crypto_hash/sha512/amd64/ref/extracted_ct_proof.ec
    (constant-time + functional correctness proof in EasyCrypt).

    Functional spec: [Bedrock.Libjade.SHA512Spec.sha512_spec], a pure-Gallina
    FIPS 180-4 reference SHA-512 (80-round compression, K_512 constants,
    1024-bit blocks, 128-bit length tail) authored locally so this slot can
    carry a real byte equality rather than a [True] placeholder.

    The libjade-side function handle [sha512_libjade] is declared here so
    that the registry slot can reference it concretely; the bridge file at
    [Bedrock.Libjade.SHA512Bridge] re-exports the same handle (and adds a
    matching length lemma) for downstream consumers. *)
Parameter sha512_libjade : list Byte.byte -> list Byte.byte.

(** Concrete byte equality between the libjade SHA-512 routine and the
    Rocq FIPS-180-4 reference spec.  Upgraded from a [True] placeholder
    on 2026-05-14; the bridge consumes this as
    [Bedrock.Libjade.SHA512Bridge.jade_hash_sha512_correct_byte_eq]. *)
Axiom jade_hash_sha512_correct :
  forall (input : list Byte.byte),
    sha512_libjade input = sha512_spec input.

(** Provenance:
    - SHA-256: libjade/proof/crypto_hash/sha256/amd64/ref/extracted_ct_proof.ec
    - SHA-512: libjade/proof/crypto_hash/sha512/amd64/ref/extracted_ct_proof.ec
    Both are EC-verified for *constant-time* execution AND functional
    equivalence to a FIPS-180-4 reference spec.

    Audit checklist:
    [ ] EC file compiles in our pinned EC switch?
    [ ] Spec matches FIPS-180-4 (manual check vs. NIST test vectors)?
    [ ] Rust extern "C" symbol name matches Jasmin export?
    [ ] (Optional) Jasmin source recompiles via Rocq Jasmin compiler? *)

(* ================================================================ *)
(* §2.  X25519                                                       *)
(* ================================================================ *)

(** [jade_scalarmult_curve25519_amd64_mulx] computes RFC 7748 X25519
    scalar multiplication: shared = clamp(scalar) * point.

    EC provenance: libjade/proof/crypto_scalarmult/curve25519/amd64/mulx/extracted_ct_proof.ec
    (constant-time + functional correctness, including the field-arithmetic
    chain compared against a Mathlib-style spec). *)
Axiom jade_curve25519_x25519_correct :
  forall (scalar : list Z) (point : list Z) (shared : list Z),
    True (* placeholder *).

(** Same for the base-point variant (k*G). *)
Axiom jade_curve25519_x25519_base_correct :
  forall (scalar : list Z) (shared : list Z),
    True (* placeholder *).

(** Provenance:
    - mulx variant: libjade/proof/crypto_scalarmult/curve25519/amd64/mulx/extracted_ct_proof.ec
    - ref4 variant: libjade/proof/crypto_scalarmult/curve25519/amd64/ref4/extracted_ct_proof.ec
    - ref5 variant: libjade/proof/crypto_scalarmult/curve25519/amd64/ref5/extracted_ct_proof.ec
    formosa-25519 (sibling repo) has analogous proofs.

    Audit checklist:
    [ ] EC proof closes under our pinned EC switch?
    [ ] RFC 7748 §5 §6 KAT vectors hold (already validated in
        curve25519-jasmin-rs/tests/kat_vectors.rs)?
    [ ] Constant-time: confirmed by EC proof on the same path? *)

(* ================================================================ *)
(* §3.  ML-KEM-768                                                   *)
(* ================================================================ *)

(** [jade_kem_mlkem_mlkem768_amd64_ref_keypair_derand] performs ML-KEM-768
    deterministic key generation per FIPS 203 from 64 bytes of coins. *)
Axiom jade_mlkem768_keypair_derand_correct :
  forall (coins : list Z) (pk : list Z) (sk : list Z),
    True (* placeholder *).

Axiom jade_mlkem768_enc_derand_correct :
  forall (pk : list Z) (coins : list Z) (ct : list Z) (ss : list Z),
    True (* placeholder *).

Axiom jade_mlkem768_dec_correct :
  forall (sk : list Z) (ct : list Z) (ss : list Z),
    True (* placeholder *).

(** Provenance: formosa-mlkem (vendored at curve25519-jasmin-rs/jazz/).
    EC proofs in Cryspen's formosa-mlkem repository.

    Audit checklist:
    [ ] EC proof closes (Cryspen's `make` succeeds)?
    [ ] FIPS 203 test vectors match (validated via
        sender-keys-hax/tests proptest_equiv cross-checks)?
    [ ] Constant-time: per EC proof? *)

(* ================================================================ *)
(* §4.  Notes on completing this file                                *)
(* ================================================================ *)

(** The placeholder [True]-statements are intentional: they make this
    file compile while leaving the precise input/output relation
    unspecified.  A consumer that depends on libjade's primitives can
    cite the axiom NAME (e.g., [jade_curve25519_x25519_correct]) as
    its trust assumption, even if the body is `True` for now.

    To upgrade to a real statement:
    1. Define a Rocq-side functional spec for each primitive (we have
       SHA-256/SHA-512 in some bedrock2 deps; X25519 spec is in
       fiat-crypto; ML-KEM-768 needs to be authored).
    2. Replace [True] with the concrete equality (e.g.,
       [digest_out = sha256_spec input]).
    3. Optionally: re-state these as [Theorem]s with proofs going
       through the Rocq Jasmin compiler's [equivalence] theorem.

    For Lean-side parallel statements, see
    [CatCrypt/Crypto/Libjade/LibjadeAxioms.lean]. *)
