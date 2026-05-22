(** * RistrettoHelpers — sqrt-ratio + is-negative helpers for Ristretto255.
 *
 * Implements the two primitive operations used by both encode and decode:
 *
 *  - [sqrt_ratio_m1 u v]  computes a canonical square root of [u/v]
 *                         (or of [SQRT_M1 * u/v] if [u/v] is not a QR),
 *                         per §3.1.3 of draft-irtf-cfrg-ristretto255-decaf448-03.
 *                         Returns [(was_square, r)] where [r * r * v]
 *                         equals [u] (case was_square = true) or
 *                         [SQRT_M1 * u] (case was_square = false), and
 *                         [r] is canonical (its low bit is 0).
 *
 *  - [is_negative x]      returns the low bit of [x] (where [x] is
 *                         assumed canonical, 0 ≤ x < p).
 *
 *  - [bytes_to_felem_canonical bs] parses a 32-byte little-endian
 *                         encoding into [Z], clearing bit 255 (the IETF
 *                         draft rejects encodings where bit 255 is set
 *                         — we model rejection by returning [None]).
 *
 *  - [felem_to_bytes32 z]  little-endian 32-byte encoding of [z mod p]
 *                         (with bit 255 zero by construction).
 *
 *  - [canonical_negate x] returns [-x mod p], which after canonicalisation
 *                         to [0..p) has its low bit possibly flipped.
 *
 * Reference: §3.1.3, §3.2.1, §3.2.2 of the IETF draft.
 *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import micromega.Lia.
Require Import coqutil.Byte.
Require Import coqutil.Word.LittleEndianList.
Require Import Bedrock.End2End.Ed25519.CompressVerified.
Require Import Bedrock.End2End.Lizard.RistrettoConsts.
Import ListNotations.
Local Open Scope Z_scope.

(** ** [is_negative x] = low bit of x.
    Ristretto convention: x is "negative" iff its canonical (smallest
    non-negative) representative has bit 0 set. *)
Definition ristretto_is_negative (x : Z) : bool :=
  Z.testbit x 0.

(** ** [canonical_negate x] = (p - x) mod p, the additive inverse mod p. *)
Definition ristretto_canonical_negate (x : Z) : Z :=
  (ed25519_p - x) mod ed25519_p.

(** ** [ristretto_abs x] = |x| in the Ristretto sense: if x is "negative"
    (low bit 1), return -x; else return x. *)
Definition ristretto_abs (x : Z) : Z :=
  if ristretto_is_negative (x mod ed25519_p)
  then ristretto_canonical_negate x
  else x mod ed25519_p.

(** ** [sqrt_ratio_m1 u v]
    Per §3.1.3 of the IETF draft: compute the canonical square root of
    [u/v] (or of [i * u / v] if [u/v] is a non-residue), where i = SQRT_M1.
    Returns [(was_square, r)]:
      - was_square = true  ⇔  v * r^2 ≡   u    (mod p)
      - was_square = false ⇔  v * r^2 ≡ i*u    (mod p)
    In all cases [r] is canonical: [is_negative r = false].
    Uses the [p ≡ 5 (mod 8)] sqrt shortcut. *)
Definition ristretto_sqrt_ratio_m1 (u v : Z) : bool * Z :=
  let v3   := (v * v * v) mod ed25519_p in
  let v7   := (v3 * v3 * v) mod ed25519_p in
  (* r0 = u * v3 * (u * v7)^((p-5)/8) mod p *)
  let pow_val := pow_mod ((u * v7) mod ed25519_p)
                         ((ed25519_p - 5) / 8) ed25519_p in
  let r0   := (u * v3 * pow_val) mod ed25519_p in
  let check := (v * r0 * r0) mod ed25519_p in
  let u_mod := u mod ed25519_p in
  let neg_u := ristretto_canonical_negate u in
  let neg_iu := ristretto_canonical_negate
                  ((ristretto_SQRT_M1 * u) mod ed25519_p) in
  let correct_sign_sqrt    := Z.eqb check u_mod in
  let flipped_sign_sqrt    := Z.eqb check neg_u in
  let flipped_sign_sqrt_i  := Z.eqb check neg_iu in
  let r1 :=
    if correct_sign_sqrt then r0
    else if flipped_sign_sqrt then
      (r0 * ristretto_SQRT_M1) mod ed25519_p
    else if flipped_sign_sqrt_i then
      (r0 * ristretto_SQRT_M1) mod ed25519_p
    else
      (* Shouldn't happen for valid (u,v); arbitrary value *)
      r0 in
  (* Canonicalize: choose non-negative representative. *)
  let r := if ristretto_is_negative r1
           then ristretto_canonical_negate r1
           else r1 in
  (* Per RFC 9496 §3.1.3: was_square := correct_sign_sqrt | flipped_sign_sqrt.
     Both branches give v * r^2 = u (case 1 directly, case 2 because
     multiplying r0 by SQRT_M1 yields r1 with v * r1^2 = -check = u).
     The flipped_sign_sqrt_i branch corresponds to u/v being NON-square
     (check = -i*u, r1 satisfies v*r1^2 = SQRT_M1*u — not a square root
     of u), so was_square must remain false there.
     Bug fix 2026-05-22 (B.5a agent finding): was previously
     [orb correct_sign_sqrt flipped_sign_sqrt_i], which incorrectly
     reported was_square=true for non-residues.  Matches the F-level
     specification in [Field/Synthesis/Examples/Ristretto255_Encode.v]
     line 111 and the comment there citing the RFC. *)
  let was_square := orb correct_sign_sqrt flipped_sign_sqrt in
  (was_square, r).

(** ** Parse 32-byte little-endian encoding.

    Per §3.2.1 of the IETF draft, decode rejects:
      - bit 255 set in the input (encoded value ≥ 2^255).
      - the resulting felem ≥ p (non-canonical).
      - is_negative(s) = true on the parsed value (sign-canonical).
    Returns [None] in the failure cases. *)
Definition ristretto_parse_canonical_felem (bs : list Byte.byte) : option Z :=
  if Nat.eqb (length bs) 32 then
    let z := le_combine bs in
    (* Check bit 255 zero. *)
    if Z.testbit z 255 then None
    else
      (* Check z < p; since bit 255 is zero, z < 2^255, but we still need z < p = 2^255 - 19. *)
      if Z.ltb z ed25519_p then
        if ristretto_is_negative z then None
        else Some z
      else None
  else None.

(** ** Pack 32-byte little-endian encoding of [z mod p].  Bit 255 is
    zero because the canonical value of [z mod p] lies in [0, p) ⊂ [0, 2^255). *)
Definition ristretto_pack_canonical_felem (z : Z) : list Byte.byte :=
  le_split 32 (z mod ed25519_p).

Lemma ristretto_pack_canonical_felem_length : forall z,
  length (ristretto_pack_canonical_felem z) = 32%nat.
Proof. intros z. unfold ristretto_pack_canonical_felem. apply length_le_split. Qed.
