(** * SHAKE-256 hash for XEdDSA (axiomatized for self-contained build)

    We DEFINE the hash as SHAKE-256 (Keccak sponge, rate=136, dsep=0x1F)
    with 64-byte output, replacing SHA-512 in the XEdDSA protocol.

    The Keccak permutation is fully verified in fiat-crypto (Keccak.v).
    We axiomatize here to avoid a build dependency on fiat-crypto.
    The axioms are dischargeable by:
      Definition hash_512 msg := Keccak.keccak_sponge 136 Byte.x1f msg 64.
      Lemma hash_512_length msg : length (hash_512 msg) = 64.
      Proof. apply Keccak.keccak_sponge_length; lia. Qed.

    SSProve security proofs model the hash as a RandomOracle —
    the concrete function is irrelevant for security. *)

From Stdlib Require Import List ZArith NArith.
Require Import Stdlib.Strings.Byte.
Import ListNotations.

(** SHAKE-256 with 64-byte output.

    DISCHARGED: The concrete definition is in
      [AUCurves/src/Spec/SHAKE256.v : hash_512]
    which defines [hash_512 msg := Keccak.keccak_sponge 136 Byte.x1f msg 64]
    with [hash_512_length] proved from [keccak_sponge_length].

    This file keeps the axiom for self-contained Signal/ builds.
    When linking with AUCurves, import [Crypto.Spec.SHAKE256] instead. *)
Axiom hash_512 : list Byte.byte -> list Byte.byte.
Axiom hash_512_length : forall msg, length (hash_512 msg) = 64%nat.

(** Scalar reduction: interpret 64-byte hash as integer mod l. *)
Definition bytes_to_Z (bs : list Byte.byte) : Z :=
  List.fold_left (fun acc b => acc * 256 + Z.of_N (Byte.to_N b))%Z bs 0%Z.

Definition scalar_from_hash (h : list Byte.byte) (l : Z) : Z :=
  (bytes_to_Z h mod l)%Z.
