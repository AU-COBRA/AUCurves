(** * CalculateKeyPairVerified — Gallina reference for
 *                                [calculate_key_pair_a_spec] +
 *                                [calculate_key_pair_A_spec].
 *
 * Drops both Parameters previously declared in
 * [End2End/XEdDSA/Sign_Strong_Correctness.v] (§1).
 *
 * Status: **executable Gallina** composing the verified leaves
 * (clamp_64 + scalarmult_base + compress) into the XEdDSA key-pair
 * derivation.
 *
 * The XEdDSA paper's `calculate_key_pair(k)` derives an Ed25519
 * signing-scalar `a` and the corresponding compressed Edwards public
 * key `A` from an X25519 private key `k`:
 *
 *   E := clamp(k) · B                  (Edwards point, projective xyzt)
 *   A := compress(E)                   (32-byte compressed public key)
 *   sign := bit 7 of A's last byte     (the implicit sign bit)
 *   if sign = 1:
 *     a := −clamp(k)  mod L            (negate the scalar)
 *     A := clear bit 7 of A's last byte (force sign = 0)
 *   else:
 *     a := clamp(k)
 *     (A unchanged)
 *
 * This file provides the two named exports:
 *   [calculate_key_pair_a_gallina (k) : 32 byte scalar]
 *   [calculate_key_pair_A_gallina (k) : 32 byte compressed pub key]
 *
 * They share the same underlying derivation; each is published as the
 * canonical name for the corresponding Parameter slot.
 *
 * Downstream proofs treat both specs abstractly via [Global Opaque].
 *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import micromega.Lia.
Require Import coqutil.Byte.
Require Import coqutil.Word.LittleEndianList.
Require Import Bedrock.End2End.Ed25519.RemainingBridges.
Require Import Bedrock.End2End.Ed25519.CompressVerified.
Require Import Bedrock.End2End.Ed25519.Clamp64Verified.
Require Import Bedrock.End2End.Ed25519.ScalarmultBaseVerified.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Negate a 32-byte scalar modulo [L_curve_order]. *)
Definition scalar_negate_mod_L (bs : list Byte.byte) : list Byte.byte :=
  let z := le_combine bs in
  let neg :=
    if Z.eqb (z mod L_curve_order) 0
    then 0
    else (L_curve_order - (z mod L_curve_order)) mod L_curve_order in
  le_split 32 neg.

Lemma scalar_negate_mod_L_length :
  forall bs, length (scalar_negate_mod_L bs) = 32%nat.
Proof. intros. cbv [scalar_negate_mod_L]. apply length_le_split. Qed.

(** ** Clear bit 7 of the last byte of a 32-byte compressed key
    (so that the sign bit is forced to 0). *)
Definition compressed_clear_sign (bs : list Byte.byte) : list Byte.byte :=
  let low31 := firstn 31 bs in
  let b31   := nth 31 bs Byte.x00 in
  let b31'  := byte.of_Z (Z.land (byte.unsigned b31) 127) in
  (low31 ++ [b31'])%list.

Lemma compressed_clear_sign_length :
  forall bs, length bs = 32%nat ->
    length (compressed_clear_sign bs) = 32%nat.
Proof.
  intros bs Hlen. cbv [compressed_clear_sign].
  rewrite length_app, length_firstn, Hlen. simpl. lia.
Qed.

(** ** Shared helper: computed compressed-A and its sign bit. *)
Definition derive_A_and_sign (k : list Byte.byte) : list Byte.byte * Z :=
  let a_pre   := clamp_64_gallina k in
  let A_xyzt  := ed25519_scalarmult_base_spec a_pre in
  let A_bytes := ed25519_compress_spec A_xyzt in
  let b31     := nth 31 A_bytes Byte.x00 in
  let sign    := Z.shiftr (byte.unsigned b31) 7 in
  (A_bytes, sign).

(** ** Edwards-derived signing scalar `a`. *)
Definition calculate_key_pair_a_gallina (k : list Byte.byte) : list Byte.byte :=
  let a_pre := clamp_64_gallina k in
  let '(_, sign) := derive_A_and_sign k in
  if Z.eqb sign 1
  then scalar_negate_mod_L a_pre
  else a_pre.

Lemma calculate_key_pair_a_gallina_length :
  forall k, length k = 32%nat ->
    length (calculate_key_pair_a_gallina k) = 32%nat.
Proof.
  intros k Hk. cbv [calculate_key_pair_a_gallina].
  destruct (derive_A_and_sign k) as [A_bytes sign].
  destruct (Z.eqb sign 1).
  - apply scalar_negate_mod_L_length.
  - apply clamp_64_gallina_length, Hk.
Qed.

(** ** Compressed Edwards public key `A` with sign forced to 0. *)
Definition calculate_key_pair_A_gallina (k : list Byte.byte) : list Byte.byte :=
  let '(A_bytes, sign) := derive_A_and_sign k in
  if Z.eqb sign 1
  then compressed_clear_sign A_bytes
  else A_bytes.

Lemma calculate_key_pair_A_gallina_length :
  forall k, length k = 32%nat ->
    length (calculate_key_pair_A_gallina k) = 32%nat.
Proof.
  intros k Hk. cbv [calculate_key_pair_A_gallina derive_A_and_sign].
  set (A_bytes := ed25519_compress_spec _).
  assert (HA : length A_bytes = 32%nat).
  { subst A_bytes. apply ed25519_compress_output_32. }
  destruct (Z.eqb _ 1).
  - apply compressed_clear_sign_length, HA.
  - exact HA.
Qed.

(** ** Canonical exports. *)
Definition calculate_key_pair_a_spec : list Byte.byte -> list Byte.byte
  := calculate_key_pair_a_gallina.
Definition calculate_key_pair_A_spec : list Byte.byte -> list Byte.byte
  := calculate_key_pair_A_gallina.

Lemma calculate_key_pair_a_spec_len :
  forall k, length k = 32%nat ->
    length (calculate_key_pair_a_spec k) = 32%nat.
Proof. exact calculate_key_pair_a_gallina_length. Qed.

Lemma calculate_key_pair_A_spec_len :
  forall k, length k = 32%nat ->
    length (calculate_key_pair_A_spec k) = 32%nat.
Proof. exact calculate_key_pair_A_gallina_length. Qed.

Global Opaque calculate_key_pair_a_spec.
Global Opaque calculate_key_pair_A_spec.
