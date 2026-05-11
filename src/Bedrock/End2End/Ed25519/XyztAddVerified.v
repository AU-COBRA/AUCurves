(** * XyztAddVerified — Gallina reference for [ed25519_xyzt_add_spec].
 *
 * Drops the [Parameter ed25519_xyzt_add_spec] axiom previously declared
 * in [Verify_Strong_Correctness.v].
 *
 * Status: **executable Gallina** computing Hisil–Wong–Carter–Dawson
 * extended-twisted-Edwards addition on the 200-byte projective xyzt
 * encoding of [CompressVerified.v].
 *
 * Layout (5 felems × 40 bytes each = 200 bytes total):
 *   bytes [  0..40)  = X
 *   bytes [ 40..80)  = Y
 *   bytes [ 80..120) = Z
 *   bytes [120..160) = Ta  (extended coord, T = Ta · Tb / Z by convention)
 *   bytes [160..200) = Tb
 *
 * Each felem parses via [CompressVerified.parse_felem] (5 limbs × 8
 * bytes, weights [2^(51·i)] mod [ed25519_p]).
 *
 * Addition formulas (Hisil–Wong–Carter–Dawson 2008,
 * "Twisted Edwards Curves Revisited", §3.1, formulas for adding two
 * points represented in extended coordinates):
 *
 *   T_i := Ta_i · Tb_i / Z_i           (extended T coordinate)
 *   A   := (Y1 − X1) · (Y2 − X2)        mod p
 *   B   := (Y1 + X1) · (Y2 + X2)        mod p
 *   C   := T1 · 2d · T2                 mod p
 *   D   := 2 · Z1 · Z2                  mod p
 *   E   := B − A
 *   F   := D − C
 *   G   := D + C
 *   H   := B + A
 *   X3  := E · F
 *   Y3  := G · H
 *   Z3  := F · G
 *   T3  := E · H  (encoded by Ta3 := E, Tb3 := H, with the same convention)
 *
 * Here [d_25519 = −121665 · 121666^(−1) mod p].  For computation we
 * use the standard concrete value
 *   d_25519 = 37095705934669439343138083508754565189542113879843219016388785533085940283555.
 *
 * Each output felem is packed back to 40 bytes via [le_split 40 v]
 * (reducing the [Z] mod [2^320]; downstream consumers re-parse mod p).
 *
 * Computability: a single call is ~10 field multiplications.  This
 * does NOT match the bedrock2 implementation byte-for-byte (which
 * uses unsaturated-solinas limb decomposition); we provide it as the
 * abstract reference.  Downstream proofs treat the spec abstractly
 * via [Global Opaque] below.
 *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import micromega.Lia.
Require Import coqutil.Word.LittleEndianList.
Require Import Bedrock.End2End.Ed25519.CompressVerified.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Curve constant [d_25519 = −121665 / 121666 mod p]. *)
Definition ed25519_d : Z :=
  37095705934669439343138083508754565189542113879843219016388785533085940283555.

(** ** Parse extended coordinates from a 200-byte xyzt slot.
    Returns (X, Y, Z, Ta, Tb) as [Z] values mod [ed25519_p]. *)
Definition parse_xyzt5 (xyzt : list Byte.byte)
  : Z * Z * Z * Z * Z :=
  let x_bytes  := firstn 40 xyzt in
  let y_bytes  := firstn 40 (skipn 40 xyzt) in
  let z_bytes  := firstn 40 (skipn 80 xyzt) in
  let ta_bytes := firstn 40 (skipn 120 xyzt) in
  let tb_bytes := firstn 40 (skipn 160 xyzt) in
  (parse_felem x_bytes,
   parse_felem y_bytes,
   parse_felem z_bytes,
   parse_felem ta_bytes,
   parse_felem tb_bytes).

(** ** Pack five field elements back into a 200-byte xyzt slot. *)
Definition pack_xyzt5 (x y z ta tb : Z) : list Byte.byte :=
  (le_split 40 x
   ++ le_split 40 y
   ++ le_split 40 z
   ++ le_split 40 ta
   ++ le_split 40 tb)%list.

Lemma pack_xyzt5_length : forall x y z ta tb,
  length (pack_xyzt5 x y z ta tb) = 200%nat.
Proof.
  intros x y z ta tb. cbv [pack_xyzt5].
  repeat rewrite length_app, length_le_split. reflexivity.
Qed.

(** ** Compute the extended T from the stored (Ta, Tb, Z).
    Convention: [T = Ta · Tb / Z mod p]. *)
Definition extended_T (ta tb z : Z) : Z :=
  (ta * tb * pow_mod z (ed25519_p - 2) ed25519_p) mod ed25519_p.

(** ** Hisil et al. extended-twisted-Edwards addition (Gallina). *)
Definition ed25519_xyzt_add_gallina
    (p1 p2 : list Byte.byte) : list Byte.byte :=
  if andb (Nat.eqb (length p1) 200) (Nat.eqb (length p2) 200) then
    let '(x1, y1, z1, ta1, tb1) := parse_xyzt5 p1 in
    let '(x2, y2, z2, ta2, tb2) := parse_xyzt5 p2 in
    let t1 := extended_T ta1 tb1 z1 in
    let t2 := extended_T ta2 tb2 z2 in
    let a  := ((y1 - x1) * (y2 - x2)) mod ed25519_p in
    let b  := ((y1 + x1) * (y2 + x2)) mod ed25519_p in
    let c  := (t1 * (2 * ed25519_d) * t2) mod ed25519_p in
    let d  := (2 * z1 * z2) mod ed25519_p in
    let e  := (b - a) mod ed25519_p in
    let f  := (d - c) mod ed25519_p in
    let g  := (d + c) mod ed25519_p in
    let h  := (b + a) mod ed25519_p in
    let x3 := (e * f) mod ed25519_p in
    let y3 := (g * h) mod ed25519_p in
    let z3 := (f * g) mod ed25519_p in
    pack_xyzt5 x3 y3 z3 e h
  else
    List.repeat Byte.x00 200.

Lemma ed25519_xyzt_add_gallina_length :
  forall p1 p2, length (ed25519_xyzt_add_gallina p1 p2) = 200%nat.
Proof.
  intros p1 p2. cbv [ed25519_xyzt_add_gallina].
  destruct (andb (Nat.eqb (length p1) 200) (Nat.eqb (length p2) 200)).
  - destruct (parse_xyzt5 p1) as [[[[x1 y1] z1] ta1] tb1].
    destruct (parse_xyzt5 p2) as [[[[x2 y2] z2] ta2] tb2].
    apply pack_xyzt5_length.
  - apply List.repeat_length.
Qed.

(** ** Canonical export. *)
Definition ed25519_xyzt_add_spec
  : list Byte.byte -> list Byte.byte -> list Byte.byte
  := ed25519_xyzt_add_gallina.

Lemma ed25519_xyzt_add_spec_len :
  forall p1 p2, length (ed25519_xyzt_add_spec p1 p2) = 200%nat.
Proof. intros; apply ed25519_xyzt_add_gallina_length. Qed.

(** Seal so downstream proofs treat the spec abstractly, mirroring
    the original [Parameter] behaviour. *)
Global Opaque ed25519_xyzt_add_spec.
