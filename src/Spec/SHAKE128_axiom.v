(** * SHAKE-128 via Keccak + expand_message_xof for RFC 9380.

    SHAKE-128 is defined concretely via [Keccak.v] — no axiom for the
    hash function itself.  The only remaining axiom is [SHAKE128_length]
    (output length = requested length), pending a proof from the sponge
    structure.

    This file is standalone (no ModularArithmetic dependency) so it
    compiles without the full fiat-crypto build.  The [hash_to_field]
    integration with [F p] lives in [HashToCurve_XOF.v] which DOES
    import ModularArithmetic. *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Strings.Byte.
Import ListNotations.

Require Import Crypto.Spec.Keccak.

Local Open Scope N_scope.

(* ================================================================== *)
(** * SHAKE-128 (concrete definition, no axiom)                        *)
(* ================================================================== *)

Definition SHAKE128 (msg : list Byte.byte) (out_len : nat) : list Byte.byte :=
  Keccak.SHAKE128 msg out_len.

(** Output length = requested length. Proved from sponge structure. *)
Lemma SHAKE128_length : forall msg out_len,
  length (SHAKE128 msg out_len) = out_len.
Proof. intros. unfold SHAKE128. apply Keccak.SHAKE128_length. Qed.

(* ================================================================== *)
(** * I2OSP helper (inlined from SHA256_axiom to avoid dependency)     *)
(* ================================================================== *)

Fixpoint I2OSP_aux (n : nat) (x : N) : list Byte.byte :=
  match n with
  | O => []
  | S n' =>
    let lo := N.land x 255 in
    let hi := N.shiftr x 8 in
    I2OSP_aux n' hi ++
    [match Byte.of_N lo with Some b => b | None => Byte.x00 end]
  end.

Definition I2OSP (x : N) (k : nat) : list Byte.byte := I2OSP_aux k x.

(* ================================================================== *)
(** * expand_message_xof (RFC 9380 §5.3.2)                             *)
(* ================================================================== *)

Definition expand_message_xof
  (msg : list Byte.byte) (dst : list Byte.byte) (len_in_bytes : nat)
  : list Byte.byte :=
  let DST_prime := dst ++ I2OSP (N.of_nat (length dst)) 1 in
  let msg_prime := msg ++ I2OSP (N.of_nat len_in_bytes) 2 ++ DST_prime in
  SHAKE128 msg_prime len_in_bytes.

(* ================================================================== *)
(** * Length lemmas                                                    *)
(* ================================================================== *)

Lemma expand_message_xof_length :
  forall msg dst len, length (expand_message_xof msg dst len) = len.
Proof.
  intros. unfold expand_message_xof. apply SHAKE128_length.
Qed.
