(** * SHAKE-256 via verified Keccak — concrete definition, 0 axioms.

    SHAKE-256 = Keccak sponge with rate=136, domain separator=0x1F.
    Output length is a parameter (64 bytes for XEdDSA).

    The Keccak permutation is fully verified in [Spec/Keccak.v].
    This file provides the SHAKE-256 wrapper and length lemma.

    Discharges the [hash_512] axiom in [Signal/theories/SHA512_axiom.v]. *)

From Stdlib Require Import ZArith List Lia.
From Stdlib.Init Require Import Byte.
Require Import Crypto.Spec.Keccak.
Import ListNotations.

(** SHAKE-256: Keccak sponge, rate=136, dsep=0x1F. Concrete. *)
Definition SHAKE256 (msg : list Byte.byte) (outlen : nat) : list Byte.byte :=
  Keccak.keccak_sponge 136 Byte.x1f msg outlen.

Lemma SHAKE256_length : forall msg outlen,
  length (SHAKE256 msg outlen) = outlen.
Proof. intros. unfold SHAKE256. apply Keccak.keccak_sponge_length; lia. Qed.

(** 64-byte hash for XEdDSA (replaces SHA-512). *)
Definition hash_512 (msg : list Byte.byte) : list Byte.byte :=
  SHAKE256 msg 64.

Lemma hash_512_length : forall msg,
  length (hash_512 msg) = 64%nat.
Proof. intros. unfold hash_512. apply SHAKE256_length. Qed.

(** This discharges:
    - [Signal/theories/SHA512_axiom.v:Axiom hash_512]
    - [Signal/theories/SHA512_axiom.v:Axiom hash_512_length]

    To link: in any file that needs the concrete definition,
    [Require Import Crypto.Spec.SHAKE256] instead of importing
    the axiom from Signal/. *)
