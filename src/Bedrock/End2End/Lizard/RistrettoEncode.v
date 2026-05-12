(** * RistrettoEncode — faithful Ristretto255 encode in Gallina.
 *
 * Per §3.2.2 of draft-irtf-cfrg-ristretto255-decaf448-03.
 *
 * Input  : 200-byte xyzt slot encoding extended-twisted-Edwards
 *          coordinates (X, Y, Z, Ta, Tb) with the convention that the
 *          extended T equals Ta * Tb / Z.  (See [extended_T] in
 *          XyztAddVerified.v.)
 * Output : 32-byte canonical Ristretto255 encoding.
 *
 * The algorithm consumes the four felems and produces a single 32-byte
 * little-endian encoding of the canonical [s] field element.  Any two
 * Edwards representatives of the same Ristretto group element encode
 * to the same 32 bytes.
 *
 * Algorithm steps:
 *   u1 := (Z + Y) * (Z - Y)
 *   u2 := X * Y
 *   (_, invsqrt) := sqrt_ratio_m1(1, u1 * u2^2)
 *   D1 := invsqrt * u1
 *   D2 := invsqrt * u2
 *   Zinv := D1 * D2 * T
 *   ix := X * SQRT_M1
 *   iy := Y * SQRT_M1
 *   eden := D1 * INVSQRT_A_MINUS_D
 *   rotate := is_negative(T * Zinv)
 *   if rotate: X := iy, Y := ix, den_inv := eden
 *   else: den_inv := D2
 *   if is_negative(X * Zinv): Y := -Y
 *   s := den_inv * (Z - Y)
 *   if is_negative(s): s := -s
 *   output := le_split 32 (s mod p)
 *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import micromega.Lia.
Require Import coqutil.Byte.
Require Import coqutil.Word.LittleEndianList.
Require Import Bedrock.End2End.Ed25519.CompressVerified.
Require Import Bedrock.End2End.Ed25519.XyztAddVerified.
Require Import Bedrock.End2End.Lizard.RistrettoConsts.
Require Import Bedrock.End2End.Lizard.RistrettoHelpers.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Ristretto255 encode (faithful, §3.2.2). *)
Definition ristretto_encode_gallina (xyzt : list Byte.byte) : list Byte.byte :=
  if Nat.eqb (length xyzt) 200 then
    let '(x, y, z, ta, tb) := parse_xyzt5 xyzt in
    let t := extended_T ta tb z in
    (* Step 1: u1 = (z + y) * (z - y) *)
    let u1 := ((z + y) * (z - y)) mod ed25519_p in
    (* Step 2: u2 = x * y *)
    let u2 := (x * y) mod ed25519_p in
    (* Step 3: (_, invsqrt) = sqrt_ratio_m1(1, u1 * u2^2) *)
    let u2_sq := (u2 * u2) mod ed25519_p in
    let den := (u1 * u2_sq) mod ed25519_p in
    let '(_, invsqrt) := ristretto_sqrt_ratio_m1 1 den in
    (* Step 4: D1 = invsqrt * u1 *)
    let D1 := (invsqrt * u1) mod ed25519_p in
    (* Step 5: D2 = invsqrt * u2 *)
    let D2 := (invsqrt * u2) mod ed25519_p in
    (* Step 6: Zinv = D1 * D2 * T *)
    let Zinv := (D1 * D2 * t) mod ed25519_p in
    (* Step 7: ix = x * SQRT_M1, iy = y * SQRT_M1 *)
    let ix := (x * ristretto_SQRT_M1) mod ed25519_p in
    let iy := (y * ristretto_SQRT_M1) mod ed25519_p in
    (* Step 8: eden = D1 * INVSQRT_A_MINUS_D *)
    let eden := (D1 * ristretto_INVSQRT_A_MINUS_D) mod ed25519_p in
    (* Step 9: t * Zinv *)
    let tZinv := (t * Zinv) mod ed25519_p in
    let rotate := ristretto_is_negative tZinv in
    (* Step 10: if rotate, swap x ↔ iy, y ↔ ix; choose den_inv *)
    let x' := if rotate then iy else x in
    let y' := if rotate then ix else y in
    let den_inv := if rotate then eden else D2 in
    (* Step 11: x_z_inv = x' * Zinv *)
    let x_z_inv := (x' * Zinv) mod ed25519_p in
    (* Step 12: if is_negative(x_z_inv), y' := -y' *)
    let y'' := if ristretto_is_negative x_z_inv
               then ristretto_canonical_negate y'
               else (y' mod ed25519_p) in
    (* Step 13: s = den_inv * (z - y'') *)
    let s_raw := (den_inv * ((z - y'') mod ed25519_p)) mod ed25519_p in
    (* Step 14: if is_negative(s_raw), s := -s_raw *)
    let s := if ristretto_is_negative s_raw
             then ristretto_canonical_negate s_raw
             else s_raw in
    (* Step 15: serialize *)
    ristretto_pack_canonical_felem s
  else
    List.repeat Byte.x00 32.

Lemma ristretto_encode_gallina_length :
  forall xyzt, length (ristretto_encode_gallina xyzt) = 32%nat.
Proof.
  intros xyzt. unfold ristretto_encode_gallina.
  destruct (Nat.eqb (length xyzt) 200) eqn:Hlen.
  - destruct (parse_xyzt5 xyzt) as [[[[x y] z] ta] tb].
    set (t := extended_T ta tb z).
    set (u1 := _ mod ed25519_p).
    set (u2 := _ mod ed25519_p).
    set (u2_sq := _ mod ed25519_p).
    set (den := _ mod ed25519_p).
    destruct (ristretto_sqrt_ratio_m1 1 den) as [b r].
    apply ristretto_pack_canonical_felem_length.
  - apply List.repeat_length.
Qed.
