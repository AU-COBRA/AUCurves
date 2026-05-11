(** * CompressVerified — Gallina reference for [ed25519_compress_spec].
 *
 * Drops the [Parameter ed25519_compress_spec] axiom previously declared
 * in [RemainingBridges.v] and [Sign_Strong_Correctness.v].
 *
 * Status: **executable Gallina** computing the actual Ed25519 point
 * compression `(X, Y, Z, Ta, Tb) -> pack(Y/Z) | parity(X/Z)`.
 *
 * Layout: The 200-byte input is the 5-felem projective stack form used
 * by [Ed25519XYZT64.projective_coords]:
 *
 *   bytes [  0..40)  = X   (5 × 64-bit unsaturated-solinas limbs)
 *   bytes [ 40..80)  = Y
 *   bytes [ 80..120) = Z
 *   bytes [120..160) = Ta  (extended coord, T = Ta * Tb / Z)
 *   bytes [160..200) = Tb
 *
 * Each felem is 5 limbs × 8 bytes (little-endian), where the value of
 * felem [w0; w1; w2; w3; w4] is `Σ w_i · 2^(51·i)` mod `2^255 - 19`
 * (see [Crypto.Bedrock.Field.Synthesis.New.UnsaturatedSolinas] for the
 * limbwidth = 51 = 255/5 derivation).
 *
 * The compression formula:
 *   x_aff = X · Z^(-1) mod p
 *   y_aff = Y · Z^(-1) mod p
 *   out   = le_split 32 y_aff   with bit 7 of byte 31 ← parity(x_aff)
 *
 * Where Z^(-1) = Z^(p-2) mod p by Fermat's little theorem.
 *
 * Note: Ta and Tb are extracted but not consumed by compression — the
 * affine projection only needs X, Y, Z. The bedrock2 callers maintain
 * the invariant `X · Y = Z · Ta · Tb`, which we do not check here (this
 * is a Gallina reference, not a validator).
 *
 * Computability: a single 254-bit `pow_mod` via square-and-multiply
 * runs ~254 squarings + ~125 multiplies, each a 504-bit multiply +
 * mod 255-bit reduction. `vm_compute` finishes in a few seconds on
 * concrete inputs; `native_compute` is sub-second.
 *
 * Downstream proofs treat the spec abstractly (via [Global Opaque]
 * below and the [ed25519_compress_spec_len] length lemma), so they
 * remain unchanged.
 *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import PArith.PArith.
From Stdlib Require Import micromega.Lia.
Require Import coqutil.Byte.
Require Import coqutil.Word.LittleEndianList.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Ed25519 base-field prime [p = 2^255 - 19]. *)
Definition ed25519_p : Z := 2^255 - 19.

(** ** Modular exponentiation by a positive exponent.
    [pow_mod_pos base exp m] computes [base^(Zpos exp) mod m] via
    binary square-and-multiply on the bit pattern of [exp]. *)
Fixpoint pow_mod_pos (base : Z) (exp : positive) (m : Z) : Z :=
  match exp with
  | xH => base mod m
  | xO p =>
      let r := pow_mod_pos base p m in (r * r) mod m
  | xI p =>
      let r := pow_mod_pos base p m in (((r * r) mod m) * base) mod m
  end.

(** [pow_mod base exp m]: [exp = 0] yields [1 mod m]; otherwise delegates
    to [pow_mod_pos]. Negative exponents are not used by compression
    and return [0] as a safe placeholder. *)
Definition pow_mod (base exp m : Z) : Z :=
  match exp with
  | Z0 => 1 mod m
  | Zpos p => pow_mod_pos base p m
  | Zneg _ => 0
  end.

(** ** Parsing one felem (40 bytes) into a [Z].
    Splits 40 bytes into five 8-byte limbs, combines each LE into a Z,
    then evaluates as a polynomial in the unsaturated-solinas weight
    [w(i) = 2^(51·i)]. The result is reduced mod p once at the end. *)
Definition parse_limb (bs : list Byte.byte) (i : nat) : Z :=
  LittleEndianList.le_combine
    (firstn 8 (skipn (8 * i) bs)).

Definition parse_felem (bs : list Byte.byte) : Z :=
  let w0 := parse_limb bs 0 in
  let w1 := parse_limb bs 1 in
  let w2 := parse_limb bs 2 in
  let w3 := parse_limb bs 3 in
  let w4 := parse_limb bs 4 in
  (w0
   + w1 * 2^51
   + w2 * 2^102
   + w3 * 2^153
   + w4 * 2^204) mod ed25519_p.

(** ** Extracting (X, Y, Z) values from the 200-byte projective slot.
    Returns the three felem values modulo [ed25519_p]. *)
Definition parse_xyz (xyzt : list Byte.byte) : Z * Z * Z :=
  let x_bytes := firstn 40 xyzt in
  let y_bytes := firstn 40 (skipn 40 xyzt) in
  let z_bytes := firstn 40 (skipn 80 xyzt) in
  (parse_felem x_bytes, parse_felem y_bytes, parse_felem z_bytes).

(** ** Setting the sign bit in the encoded byte string.
    Replaces byte 31 with [(y_bytes[31] AND 0x7F) OR (sign << 7)]. *)
Definition set_sign_bit (y_bytes : list Byte.byte) (sign : Z) : list Byte.byte :=
  let low31 := firstn 31 y_bytes in
  let b31 := nth 31 y_bytes Byte.x00 in
  let b31' :=
      byte.of_Z (Z.lor (Z.land (byte.unsigned b31) 127)
                       (Z.shiftl (sign mod 2) 7)) in
  low31 ++ [b31'].

(** ** Edwards point compression. *)
Definition ed25519_compress_gallina (xyzt : list Byte.byte) : list Byte.byte :=
  if Nat.eqb (length xyzt) 200 then
    let '(x_val, y_val, z_val) := parse_xyz xyzt in
    let z_inv := pow_mod z_val (ed25519_p - 2) ed25519_p in
    let x_aff := (x_val * z_inv) mod ed25519_p in
    let y_aff := (y_val * z_inv) mod ed25519_p in
    let y_bytes := LittleEndianList.le_split 32 y_aff in
    set_sign_bit y_bytes (Z.land x_aff 1)
  else
    List.repeat Byte.x00 32.

(** ** Length lemma. *)
Lemma set_sign_bit_length (y_bytes : list Byte.byte) (sign : Z) :
  length y_bytes = 32%nat ->
  length (set_sign_bit y_bytes sign) = 32%nat.
Proof.
  intros Hlen. cbv [set_sign_bit].
  rewrite app_length, length_firstn, Hlen. simpl. lia.
Qed.

Lemma ed25519_compress_gallina_length :
  forall xyzt, length (ed25519_compress_gallina xyzt) = 32%nat.
Proof.
  intros xyzt. cbv [ed25519_compress_gallina].
  destruct (Nat.eqb (length xyzt) 200) eqn:Hlen.
  - destruct (parse_xyz xyzt) as [[x_val y_val] z_val].
    apply set_sign_bit_length.
    apply LittleEndianList.length_le_split.
  - apply List.repeat_length.
Qed.

(** ** Canonical export. *)
Definition ed25519_compress_spec : list Byte.byte -> list Byte.byte :=
  ed25519_compress_gallina.

Lemma ed25519_compress_output_32 :
  forall xyzt, length (ed25519_compress_spec xyzt) = 32%nat.
Proof. exact ed25519_compress_gallina_length. Qed.

Lemma ed25519_compress_spec_len :
  forall xyzt, length xyzt = 200%nat ->
    length (ed25519_compress_spec xyzt) = 32%nat.
Proof. intros xyzt _. apply ed25519_compress_output_32. Qed.

(** Seal the spec so downstream [cbn]/[simpl] cannot expose the
    body. Existing proofs treated [ed25519_compress_spec] as an
    opaque [Parameter]; this preserves that behaviour. *)
Global Opaque ed25519_compress_spec.
