(** * DecompressVerified — Gallina reference for [ed25519_decompress_*_spec].
 *
 * Drops both [Parameter ed25519_decompress_R_spec] and
 * [Parameter ed25519_decompress_A_spec] (declared in
 * [Verify_Strong_Correctness.v]).
 *
 * Status: **executable Gallina** computing Ed25519 point decompression
 * via the standard [p ≡ 5 mod 8] sqrt shortcut.
 *
 * Signature: [list byte] -> [list byte] (200 bytes xyzt encoding).
 * The decompression NEVER returns option/None: per the verify protocol
 * comment (Verify_Strong_Correctness.v §2, line 62), an invalid input
 * is modelled as a designated "bad" point in the xyzt encoding (the
 * protocol does not branch on validity); the strong-correctness theorem
 * threads this through symbolically.
 *
 * Algorithm (RFC 8032 §5.1.3):
 *   1. Strip and remember the sign bit (byte 31, bit 7).
 *   2. Parse y as the remaining 255-bit little-endian value mod p.
 *      If y >= p, the input is invalid → we still return some bytes.
 *   3. Compute u = y^2 - 1, v = d·y^2 + 1.
 *   4. Compute x = (u · v^7) · (u · v^3)^((p-5)/8) mod p.
 *   5. If v·x^2 ≡ −u mod p (and not u), multiply x by sqrt(-1).
 *   6. If x = 0 and sign = 1, invalid; otherwise conditionally negate
 *      x to match the requested sign bit.
 *   7. Pack as xyzt: X = x, Y = y, Z = 1, Ta = x, Tb = y.
 *
 * Inputs > 32 bytes: only the first 32 bytes are consulted (this lets
 * the verify protocol call decompress_R with the full 64-byte sig_in,
 * extracting the R = sig_in[0..32] component).
 *
 * Downstream proofs treat the spec abstractly via [Global Opaque].
 *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import micromega.Lia.
Require Import coqutil.Byte.
Require Import coqutil.Word.LittleEndianList.
Require Import Bedrock.End2End.Ed25519.CompressVerified.
Require Import Bedrock.End2End.Ed25519.XyztAddVerified.
Import ListNotations.
Local Open Scope Z_scope.

(** ** sqrt(-1) mod p = 2^((p-1)/4) mod p, used when the trial root
    needs a quadratic-non-residue correction.

    Concrete value:
      sqrtm1 = 19681161376707505956807079304988542015446066515923890162744021073123829784752.
    We hard-code it; this is a 254-bit constant directly computable
    by [pow_mod 2 ((ed25519_p - 1)/4) ed25519_p].
    Bug-fix 2026-05-12: the previous value (...0492881760...) had
    incorrect digits 34..; squaring it mod p yielded 27733169..., not
    p-1. Replaced with the IETF/canonical value (...0498854201...);
    sqrtm1² mod p = p-1 verified by vm_compute (see sanity lemma below). *)
Definition ed25519_sqrtm1 : Z :=
  19681161376707505956807079304988542015446066515923890162744021073123829784752.

Lemma ed25519_sqrtm1_sq : (ed25519_sqrtm1 * ed25519_sqrtm1) mod ed25519_p = ed25519_p - 1.
Proof. vm_compute. reflexivity. Qed.

(** ** Try to recover x from y given the sign-bit hint.
    Returns the value [x] (mod p); validity is not checked. *)
Definition recover_x (y sign : Z) : Z :=
  let y2 := (y * y) mod ed25519_p in
  let u  := (y2 - 1) mod ed25519_p in
  let v  := (ed25519_d * y2 + 1) mod ed25519_p in
  (* x_cand = (u · v^7) · (u · v^3)^((p-5)/8) mod p
     This is the standard sqrt-shortcut formula for p ≡ 5 mod 8. *)
  let uv3       := (u * pow_mod v 3 ed25519_p) mod ed25519_p in
  let uv7       := (u * pow_mod v 7 ed25519_p) mod ed25519_p in
  let exp_val   := pow_mod uv3 ((ed25519_p - 5) / 8) ed25519_p in
  let x_cand    := (uv7 * exp_val) mod ed25519_p in
  (* Check v · x_cand^2 mod p. *)
  let vxx       := (v * x_cand * x_cand) mod ed25519_p in
  let x_pre     :=
    if Z.eqb vxx (u mod ed25519_p)
    then x_cand
    else (x_cand * ed25519_sqrtm1) mod ed25519_p in
  (* Conditionally negate to match sign bit. *)
  if Z.eqb (Z.land x_pre 1) sign
  then x_pre
  else ((ed25519_p - x_pre) mod ed25519_p).

(** ** Top-level decompression: 32+ byte little-endian compressed
    encoding → 200-byte xyzt slot. *)
Definition ed25519_decompress_gallina (bs : list Byte.byte) : list Byte.byte :=
  let bs32     := firstn 32 bs in
  let b31      := nth 31 bs32 Byte.x00 in
  let sign     := Z.shiftr (byte.unsigned b31) 7 in
  let b31_low  := byte.of_Z (Z.land (byte.unsigned b31) 127) in
  let low31    := firstn 31 bs32 in
  let y_bytes  := (low31 ++ [b31_low])%list in
  let y        := le_combine y_bytes in
  let y_mod    := y mod ed25519_p in
  let x        := recover_x y_mod sign in
  pack_xyzt5 x y_mod 1 x y_mod.

Lemma ed25519_decompress_gallina_length :
  forall bs, length (ed25519_decompress_gallina bs) = 200%nat.
Proof.
  intros bs. cbv [ed25519_decompress_gallina].
  apply pack_xyzt5_length.
Qed.

(** ** Two named exports.  Both decompress the same way; the difference
    is just which 32-byte fragment of the caller's input is consumed
    (decompress_R on 64-byte sig: looks at first 32 bytes; decompress_A
    on 32-byte pub: looks at all 32 bytes — both are [firstn 32 bs]). *)
Definition ed25519_decompress_R_spec : list Byte.byte -> list Byte.byte
  := ed25519_decompress_gallina.
Definition ed25519_decompress_A_spec : list Byte.byte -> list Byte.byte
  := ed25519_decompress_gallina.

Lemma ed25519_decompress_R_spec_len :
  forall sig_in, length (ed25519_decompress_R_spec sig_in) = 200%nat.
Proof. intros. apply ed25519_decompress_gallina_length. Qed.

Lemma ed25519_decompress_A_spec_len :
  forall pub, length (ed25519_decompress_A_spec pub) = 200%nat.
Proof. intros. apply ed25519_decompress_gallina_length. Qed.

Global Opaque ed25519_decompress_R_spec.
Global Opaque ed25519_decompress_A_spec.
