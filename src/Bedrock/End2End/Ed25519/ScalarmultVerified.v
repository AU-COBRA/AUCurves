(** * ScalarmultVerified — Gallina reference for [ed25519_scalarmult_spec].
 *
 * Drops the [Parameter ed25519_scalarmult_spec] axiom previously
 * declared in [Verify_Strong_Correctness.v].
 *
 * Status: **executable Gallina** computing variable-base scalar
 * multiplication on the 200-byte projective xyzt encoding via
 * left-to-right binary double-and-add.
 *
 * Signature: [scalar : list byte (32 bytes)] -> [P : list byte (200 bytes)]
 *         -> [result : list byte (200 bytes)] = [scalar · P]
 *
 * Algorithm: classical double-and-add, MSB to LSB, 256 bit positions
 * (scalar is 256-bit little-endian, but we walk it MSB-first by indexing
 * [Z.testbit scalar_z (Z.of_nat n)] with [n] decreasing).
 *
 *   accum := identity_xyzt
 *   for n = 255 downto 0:
 *     accum := double(accum)
 *     if testbit(scalar, n) then accum := accum + P
 *   return accum
 *
 * Identity element in extended-twisted-Edwards coordinates:
 *   (X, Y, Z, T) = (0, 1, 1, 0) — stored as (Ta=0, Tb=0, Z=1).
 *
 * Computability: a single call is ~256 doubles + ~128 additions on
 * average, each ~10 field multiplications, each a 504-bit multiply.
 * A concrete [vm_compute] would take a long time; not exercised here.
 * Downstream proofs treat the spec abstractly via [Global Opaque].
 *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import micromega.Lia.
Require Import coqutil.Word.LittleEndianList.
Require Import Bedrock.End2End.Ed25519.XyztAddVerified.
Require Import Bedrock.End2End.Ed25519.XyztDoubleVerified.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Identity point in 200-byte xyzt encoding.
    (X, Y, Z, Ta, Tb) = (0, 1, 1, 0, 0). *)
Definition identity_xyzt : list Byte.byte :=
  (le_split 40 0
   ++ le_split 40 1
   ++ le_split 40 1
   ++ le_split 40 0
   ++ le_split 40 0)%list.

Lemma identity_xyzt_length : length identity_xyzt = 200%nat.
Proof.
  cbv [identity_xyzt].
  repeat rewrite app_length, length_le_split. reflexivity.
Qed.

(** ** Inner double-and-add loop.
    [bits] counts down (255, 254, ..., 0); [scalar_z] is the integer
    scalar; [P] is the 200-byte input point; [accum] is the running
    200-byte result.  We test bit position [bits-1] (i.e., MSB at the
    first iteration when [bits = 256]). *)
Fixpoint scalarmult_aux
    (bits : nat) (scalar_z : Z) (P accum : list Byte.byte) : list Byte.byte :=
  match bits with
  | O => accum
  | S n =>
      let accum' := ed25519_xyzt_double_gallina accum in
      let bit := Z.testbit scalar_z (Z.of_nat n) in
      let accum'' := if bit then ed25519_xyzt_add_spec accum' P else accum' in
      scalarmult_aux n scalar_z P accum''
  end.

Lemma scalarmult_aux_length :
  forall bits scalar_z P accum,
    length accum = 200%nat ->
    length (scalarmult_aux bits scalar_z P accum) = 200%nat.
Proof.
  induction bits as [|n IH]; intros scalar_z P accum Hlen; cbn.
  - exact Hlen.
  - apply IH.
    destruct (Z.testbit scalar_z (Z.of_nat n)).
    + apply ed25519_xyzt_add_spec_len.
    + apply ed25519_xyzt_double_gallina_length.
Qed.

(** ** Variable-base scalar multiplication (top-level Gallina). *)
Definition ed25519_scalarmult_gallina
    (scalar : list Byte.byte) (P : list Byte.byte) : list Byte.byte :=
  let scalar_z := le_combine scalar in
  scalarmult_aux 256 scalar_z P identity_xyzt.

Lemma ed25519_scalarmult_gallina_length :
  forall scalar P, length (ed25519_scalarmult_gallina scalar P) = 200%nat.
Proof.
  intros scalar P. cbv [ed25519_scalarmult_gallina].
  apply scalarmult_aux_length, identity_xyzt_length.
Qed.

(** ** Canonical export. *)
Definition ed25519_scalarmult_spec
  : list Byte.byte -> list Byte.byte -> list Byte.byte
  := ed25519_scalarmult_gallina.

Lemma ed25519_scalarmult_spec_len :
  forall scalar P, length (ed25519_scalarmult_spec scalar P) = 200%nat.
Proof. intros; apply ed25519_scalarmult_gallina_length. Qed.

Global Opaque ed25519_scalarmult_spec.
