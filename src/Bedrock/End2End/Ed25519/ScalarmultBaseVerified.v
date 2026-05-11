(** * ScalarmultBaseVerified — Gallina reference for [ed25519_scalarmult_base_spec].
 *
 * Drops the [Parameter ed25519_scalarmult_base_spec] axiom previously
 * declared in [RemainingBridges.v] and [Sign_Strong_Correctness.v].
 *
 * Status: **executable Gallina** specialising
 * [ed25519_scalarmult_gallina] to the fixed Ed25519 base point B.
 *
 * The base point B in extended-twisted-Edwards (X, Y, Z, T) form is:
 *
 *   B_x = 15112221349535400772501151409588531511454012693041857206046113283949847762202
 *   B_y = 46316835694926478169428394003475163141307993866256225615783033603165251855960
 *   B_z = 1
 *   B_T = B_x · B_y / B_z mod p
 *
 * We encode it as a 200-byte slot using [le_split 40] per felem; the
 * Ta and Tb factors are chosen so that Ta · Tb / Z = B_T mod p — the
 * simplest choice is Ta = B_x, Tb = B_y (so Ta · Tb = B_x · B_y, and
 * since Z = 1, T = Ta · Tb).
 *
 * Downstream proofs treat the spec abstractly via [Global Opaque].
 *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import coqutil.Word.LittleEndianList.
Require Import Bedrock.End2End.Ed25519.ScalarmultVerified.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Ed25519 base point B = (Bx, By, 1, Bx·By). *)
Definition ed25519_Bx : Z :=
  15112221349535400772501151409588531511454012693041857206046113283949847762202.

Definition ed25519_By : Z :=
  46316835694926478169428394003475163141307993866256225615783033603165251855960.

(** ** Base point packed into a 200-byte xyzt slot.
    (Ta, Tb) := (Bx, By) so that T = Ta · Tb / Z = Bx · By (since Z = 1). *)
Definition base_point_xyzt : list Byte.byte :=
  (le_split 40 ed25519_Bx
   ++ le_split 40 ed25519_By
   ++ le_split 40 1
   ++ le_split 40 ed25519_Bx
   ++ le_split 40 ed25519_By)%list.

Lemma base_point_xyzt_length : length base_point_xyzt = 200%nat.
Proof.
  cbv [base_point_xyzt].
  repeat rewrite app_length, length_le_split. reflexivity.
Qed.

(** ** Fixed-generator scalar multiplication. *)
Definition ed25519_scalarmult_base_gallina (scalar : list Byte.byte)
  : list Byte.byte
  := ed25519_scalarmult_spec scalar base_point_xyzt.

Lemma ed25519_scalarmult_base_gallina_length :
  forall scalar, length (ed25519_scalarmult_base_gallina scalar) = 200%nat.
Proof.
  intros scalar. cbv [ed25519_scalarmult_base_gallina].
  apply ed25519_scalarmult_spec_len.
Qed.

(** ** Canonical export. *)
Definition ed25519_scalarmult_base_spec
  : list Byte.byte -> list Byte.byte
  := ed25519_scalarmult_base_gallina.

Lemma ed25519_scalarmult_base_spec_len :
  forall scalar, length scalar = 32%nat ->
    length (ed25519_scalarmult_base_spec scalar) = 200%nat.
Proof.
  intros scalar _. apply ed25519_scalarmult_base_gallina_length.
Qed.

(** Length lemma matching the [RemainingBridges] Parameter signature
    (no length precondition). *)
Lemma ed25519_scalarmult_base_output_200 :
  forall scalar, length (ed25519_scalarmult_base_spec scalar) = 200%nat.
Proof. intros scalar. apply ed25519_scalarmult_base_gallina_length. Qed.

Global Opaque ed25519_scalarmult_base_spec.
