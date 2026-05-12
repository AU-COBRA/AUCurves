(** * RistrettoDecode — faithful Ristretto255 decode in Gallina.
 *
 * Per §3.2.1 of draft-irtf-cfrg-ristretto255-decaf448-03.
 *
 * Input  : 32-byte Ristretto255 encoding.
 * Output : 200-byte xyzt slot encoding extended-twisted-Edwards
 *          coordinates (x, y, 1, x, y).  On failure (non-canonical
 *          encoding, or [s] negative, or [v * u2^2] non-square modulo a
 *          rejection bit, or [y = 0], or final [t] negative), the spec
 *          returns a designated "bad point" — 200 bytes of 0x00.  This
 *          matches the totality requirement of [strong_callee_post_lizard]
 *          (the Rust slot always has 200 bytes after the call).  A future
 *          refinement could thread an [option] type through to the
 *          callee_post obligation; for now the "bad point" is documented
 *          here and recognised by downstream callers as failure.
 *
 * Algorithm steps:
 *   s := parse_canonical_field_element(input)   (returns None on reject)
 *   if reject: return BAD
 *   ss := s^2
 *   u1 := 1 - ss
 *   u2 := 1 + ss
 *   u2_sqr := u2^2
 *   v := -(d * u1^2) - u2_sqr
 *   (was_square, I) := sqrt_ratio_m1(1, v * u2_sqr)
 *   Dx := I * u2
 *   Dy := I * Dx * v
 *   x := 2 * s * Dx
 *   if is_negative(x): x := -x
 *   y := Dy * u1
 *   t := x * y
 *   if (not was_square) or is_negative(t) or y = 0: return BAD
 *   else: return pack_xyzt5(x, y, 1, x, y)
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

(** The designated "bad point" returned on decode failure.  All 200 bytes
    are zero. *)
Definition ristretto_bad_point : list Byte.byte := List.repeat Byte.x00 200.

Lemma ristretto_bad_point_length :
  length ristretto_bad_point = 200%nat.
Proof. apply List.repeat_length. Qed.

(** ** Ristretto255 decode (faithful, §3.2.1). *)
Definition ristretto_decode_gallina (bs : list Byte.byte) : list Byte.byte :=
  match ristretto_parse_canonical_felem bs with
  | None => ristretto_bad_point
  | Some s =>
      let ss := (s * s) mod ed25519_p in
      (* Step 3: u1 = 1 - ss *)
      let u1 := (1 - ss) mod ed25519_p in
      (* Step 4: u2 = 1 + ss *)
      let u2 := (1 + ss) mod ed25519_p in
      (* Step 5: u2_sqr *)
      let u2_sqr := (u2 * u2) mod ed25519_p in
      (* Step 6: v = -(d * u1^2) - u2_sqr *)
      let u1_sq := (u1 * u1) mod ed25519_p in
      let v := ((ed25519_p - (ed25519_d * u1_sq) mod ed25519_p) mod ed25519_p
                - u2_sqr) mod ed25519_p in
      (* Step 7: (was_square, I) = sqrt_ratio_m1(1, v * u2_sqr) *)
      let den := (v * u2_sqr) mod ed25519_p in
      let '(was_square, I_val) := ristretto_sqrt_ratio_m1 1 den in
      (* Step 8: Dx = I * u2 *)
      let Dx := (I_val * u2) mod ed25519_p in
      (* Step 9: Dy = I * Dx * v *)
      let Dy := (I_val * Dx * v) mod ed25519_p in
      (* Step 10: x = 2 * s * Dx, conditionally negated to non-negative *)
      let x_raw := (2 * s * Dx) mod ed25519_p in
      let x := if ristretto_is_negative x_raw
               then ristretto_canonical_negate x_raw
               else x_raw in
      (* Step 11: y = Dy * u1 *)
      let y := (Dy * u1) mod ed25519_p in
      (* Step 12: t = x * y *)
      let t := (x * y) mod ed25519_p in
      (* Step 13: failure conditions *)
      if orb (negb was_square)
             (orb (ristretto_is_negative t) (Z.eqb y 0))
      then ristretto_bad_point
      else pack_xyzt5 x y 1 x y
  end.

Lemma ristretto_decode_gallina_length :
  forall bs, length (ristretto_decode_gallina bs) = 200%nat.
Proof.
  intros bs. unfold ristretto_decode_gallina.
  destruct (ristretto_parse_canonical_felem bs) as [s|];
    [| apply ristretto_bad_point_length].
  destruct (ristretto_sqrt_ratio_m1 _ _) as [was_square I_val].
  destruct (orb (negb was_square)
                (orb (ristretto_is_negative _) (Z.eqb _ 0))).
  - apply ristretto_bad_point_length.
  - apply pack_xyzt5_length.
Qed.
