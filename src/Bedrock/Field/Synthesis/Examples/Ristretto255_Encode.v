(** * Ristretto255_Encode — RFC 9496 §4.3.2 encoding pipeline (functional spec).
 *
 * Phase A.1 of RISTRETTO255_ENCODING_PLAN.md.  This file provides the
 * functional Gallina specification of the ristretto255 ENCODING half
 * (RFC 9496 §4.3.2), parameterised over the Curve25519 base field
 * [F p] with [p = 2^255 - 19].  No correctness proofs yet — those land
 * in subsequent phases (A.3, B.1, B.2).
 *
 *   ADR (§12 of plan):
 *   - byte form     := [list Byte.byte] of length 32 (NOT [Vector.t]),
 *                       to match existing AUCurves [LittleEndianList]
 *                       conventions in [Bedrock.End2End.Lizard.*].
 *   - point form    := extended Edwards [(X, Y, Z, T) : F * F * F * F]
 *                       matching the RFC pseudocode verbatim.  An
 *                       [affine_of_extended] boundary lemma is left for
 *                       Phase A.3.
 *   - constant-time := NOT verified at this layer (deferred).
 *
 * The Z-level mirror of these definitions lives in
 *   [Bedrock.End2End.Lizard.RistrettoEncode] / [RistrettoHelpers]
 *   / [RistrettoConsts].  This file is the [F p]-typed *abstraction* of
 * that mirror; the two are connected by a refinement lemma to be
 * established in Phase B.
 *
 *   Companion file: [Ristretto255_Decode.v] (sister-agent, parallel).
 *
 * References:
 *   - RFC 9496 §3.1.{1,2,3} (field primitives)
 *   - RFC 9496 §4.3.2       (encoding, lines 1-13)
 *   - RFC 9496 §A.1         (test vector for the basepoint)
 *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import NArith.NArith.
Require Import coqutil.Word.LittleEndianList.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.Curve25519.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Base field [F p] for Curve25519.
    We open [F_scope] for the field arithmetic operators ([+], [*], [-],
    [^]) so that overloaded notations bind to [F.add], [F.mul], etc.
    instead of the [Z] operations (the [F.to_Z] coercion would otherwise
    collapse everything to [Z]). *)
Local Notation Fp := (F.F (2^255 - 19)).
Local Notation Fzero := (F.of_Z _ 0).
Local Notation Fone  := (F.of_Z _ 1).
Local Open Scope F_scope.

(** ** Ristretto255 field constants (RFC 9496 §3.1).
 *
 *  - [SQRT_M1]          = sqrt(-1) mod p
 *  - [INVSQRT_A_MINUS_D] = 1 / sqrt(a - d) mod p (a = -1)
 *
 *  Decimal values copied from RFC 9496 §3.1 / IETF draft.  See
 *  [Bedrock.End2End.Lizard.RistrettoConsts] for [vm_compute] sanity
 *  checks of [SQRT_M1^2 ≡ -1 (mod p)] and the [INVSQRT_A_MINUS_D]
 *  defining equation.
 *)

Definition SQRT_M1 : Fp :=
  F.of_Z _ 19681161376707505956807079304988542015446066515923890162744021073123829784752.

Definition INVSQRT_A_MINUS_D : Fp :=
  F.of_Z _ 54469307008909316920995813868745141605393597292927456921205312896311721017578.

(** ** §3.1.1 [is_negative] — low bit of the canonical LE encoding. *)
Definition is_negative (s : Fp) : bool :=
  Z.testbit (F.to_Z s) 0.

(** ** §3.1.2 [abs] — canonical sign. *)
Definition abs (s : Fp) : Fp :=
  if is_negative s then F.opp s else s.

(** ** §3.1.3 [sqrt_ratio_m1 u v].
 *
 *  Compute the canonical square root of [u/v] (or of [SQRT_M1 * u / v]
 *  when [u/v] is a non-residue).  Returns [(was_square, r)].  The
 *  body follows the [p ≡ 5 mod 8] shortcut from RFC 9496 §3.1.3.
 *
 *  Algebraic invariant (proved in Phase B):
 *    - was_square = true  ⇔  v * r^2 = u
 *    - was_square = false ⇔  v * r^2 = SQRT_M1 * u
 *  In all cases, [is_negative r = false].
 *)
Definition sqrt_ratio_m1 (u v : Fp) : bool * Fp :=
  let v3 := v * v * v in
  let v7 := v3 * v3 * v in
  (* exponent (p - 5) / 8 *)
  let e  := ((2^255 - 19 - 5) / 8)%Z in
  let r0 := u * v3 * F.pow (u * v7) (Z.to_N e) in
  let check := v * r0 * r0 in
  (* Decidable equality on [F p] is reified via [F.to_Z]: two field
     elements are equal iff their canonical Z representatives match. *)
  let feqb (x y : Fp) : bool := Z.eqb (F.to_Z x) (F.to_Z y) in
  let correct_sign_sqrt   := feqb check u in
  let flipped_sign_sqrt   := feqb check (F.opp u) in
  let flipped_sign_sqrt_i := feqb check (F.opp (SQRT_M1 * u)) in
  let r1 :=
    if correct_sign_sqrt then r0
    else if flipped_sign_sqrt then r0 * SQRT_M1
    else if flipped_sign_sqrt_i then r0 * SQRT_M1
    else r0 in
  let r := abs r1 in
  (* Per RFC 9496 §3.1.3: was_square := correct_sign_sqrt | flipped_sign_sqrt.
     Both branches give v * r^2 = u (case 1 directly, case 2 because
     multiplying r0 by SQRT_M1 yields r1 with v * r1^2 = -check = u). *)
  let was_square := orb correct_sign_sqrt flipped_sign_sqrt in
  (was_square, r).

(** ** §4.3.2 lines 1-13: extended-Edwards → canonical field element [s].
 *
 *  Reads exactly as the RFC pseudocode:
 *
 *  {{
 *    u1            = (Z + Y) * (Z - Y)
 *    u2            = X * Y
 *    (_, invsqrt)  = SQRT_RATIO_M1(1, u1 * u2^2)
 *    den1          = invsqrt * u1
 *    den2          = invsqrt * u2
 *    z_inv         = den1 * den2 * T
 *    ix0           = X * SQRT_M1
 *    iy0           = Y * SQRT_M1
 *    enchanted_den = den1 * INVSQRT_A_MINUS_D
 *    rotate        = is_negative(T * z_inv)
 *    if rotate: X, Y = iy0, ix0;  den_inv = enchanted_den
 *    else:      den_inv = den2
 *    if is_negative(X * z_inv): Y = -Y
 *    s = abs(den_inv * (Z - Y))
 *  }}
 *)
Definition ristretto_encode_aux (X Y Z T : Fp) : Fp :=
  let u1 := (Z + Y) * (Z - Y) in
  let u2 := X * Y in
  let '(_, invsqrt) := sqrt_ratio_m1 Fone (u1 * (u2 * u2)) in
  let den1 := invsqrt * u1 in
  let den2 := invsqrt * u2 in
  let z_inv := den1 * den2 * T in
  let ix0 := X * SQRT_M1 in
  let iy0 := Y * SQRT_M1 in
  let enchanted_den := den1 * INVSQRT_A_MINUS_D in
  let rotate := is_negative (T * z_inv) in
  let X' := if rotate then iy0 else X in
  let Y0 := if rotate then ix0 else Y in
  let den_inv := if rotate then enchanted_den else den2 in
  let Y' := if is_negative (X' * z_inv) then F.opp Y0 else Y0 in
  abs (den_inv * (Z - Y')).

(** ** Step 14: serialise [s : Fp] to 32 little-endian bytes.  Bit 255
    is necessarily zero because [F.to_Z s ∈ [0, p) ⊂ [0, 2^255)]. *)
Definition ristretto_encode_bytes_of_F (s : Fp) : list Byte.byte :=
  le_split 32 (F.to_Z s).

(** ** Top-level encode: a 4-tuple of extended-Edwards coordinates in
    [Fp] is sent to a 32-byte little-endian canonical encoding.

    The product [Fp * Fp * Fp * Fp] is the on-curve representation; the
    RFC's "ristretto_point" is a coset (modulo [E[4]]).  The
    [well_defined] theorem of Phase A.3 will show that any two
    representatives in the same coset compress to the same byte string.
 *)
Definition ristretto_encode (P : Fp * Fp * Fp * Fp) : Fp :=
  let '(X, Y, Z, T) := P in ristretto_encode_aux X Y Z T.

Definition ristretto_encode_bytes (P : Fp * Fp * Fp * Fp) : list Byte.byte :=
  ristretto_encode_bytes_of_F (ristretto_encode P).

(** ** Length invariant — drop-out from [le_split]. *)
Lemma ristretto_encode_bytes_of_F_length :
  forall s, length (ristretto_encode_bytes_of_F s) = 32%nat.
Proof. intros s. apply length_le_split. Qed.

Lemma ristretto_encode_bytes_length :
  forall P, length (ristretto_encode_bytes P) = 32%nat.
Proof. intros [[[X Y] Z] T]. apply ristretto_encode_bytes_of_F_length. Qed.

(** ** RFC 9496 §A.1 — test vector for the basepoint.
 *
 *  The Ed25519 basepoint [B = (Bx, By, 1, Bx * By)] in extended-Edwards
 *  form has ristretto255 compressed encoding
 *  [E2 F2 AE 0A 6A BC 4E 71 ... 76].  We carry the 32-byte literal as
 *  [BASEPOINT_COMPRESSED_RFC] so that subsequent phases can prove
 *  [ristretto_encode_bytes B_extended = BASEPOINT_COMPRESSED_RFC].
 *
 *  We do NOT discharge the equality here — direct [vm_compute] on
 *  [ristretto_encode_bytes] of the basepoint chains [F.pow] of an
 *  exponent ≈ 2^252 in the abstract [F p] representation, which is
 *  intractable.  A Z-level mirror exists in
 *  [Bedrock.End2End.Lizard.RistrettoEncode]; the [F p] ↔ Z bridge is
 *  Phase B.
 *)

(** Basepoint extended-Edwards coordinates (Phase A.3 will use these). *)
Definition basepoint_Bx : Fp :=
  F.of_Z _ 15112221349535400772501151409588531511454012693041857206046113283949847762202.

Definition basepoint_By : Fp :=
  F.of_Z _ 46316835694926478169428394003475163141307993866256225615783033603165251855960.

Definition basepoint_extended : Fp * Fp * Fp * Fp :=
  (basepoint_Bx, basepoint_By, Fone, basepoint_Bx * basepoint_By)%F.

(** The expected 32-byte canonical compression of the basepoint
    (RFC 9496 §A.1, decimal form of [E2 F2 AE 0A ... 76] below).
    Hex bytes (LE):
      E2 F2 AE 0A 6A BC 4E 71 A8 84 A9 61 C5 00 51 5F
      58 E3 0B 6A A5 82 DD 8D B6 A6 59 45 E0 8D 2D 76 *)
Definition BASEPOINT_COMPRESSED_RFC : list Byte.byte :=
  [ Byte.xe2; Byte.xf2; Byte.xae; Byte.x0a;
    Byte.x6a; Byte.xbc; Byte.x4e; Byte.x71;
    Byte.xa8; Byte.x84; Byte.xa9; Byte.x61;
    Byte.xc5; Byte.x00; Byte.x51; Byte.x5f;
    Byte.x58; Byte.xe3; Byte.x0b; Byte.x6a;
    Byte.xa5; Byte.x82; Byte.xdd; Byte.x8d;
    Byte.xb6; Byte.xa6; Byte.x59; Byte.x45;
    Byte.xe0; Byte.x8d; Byte.x2d; Byte.x76 ].

Lemma BASEPOINT_COMPRESSED_RFC_length :
  length BASEPOINT_COMPRESSED_RFC = 32%nat.
Proof. reflexivity. Qed.
