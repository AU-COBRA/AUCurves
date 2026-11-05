(** * Ristretto255_Decode — Functional spec of RFC 9496 §4.3.1 decoding.

    Phase A.2 of the Ristretto255 encoding project (see
    [BLS/writeup/RISTRETTO255_ENCODING_PLAN.md]).

    This file is the typed counterpart to the byte-level
    [Bedrock.End2End.Lizard.RistrettoDecode] (which works in raw [Z mod p]
    and packs the result into a 200-byte slot for the bedrock2/Rust
    pipeline).  Here we lift the algorithm to fiat-crypto's
    [Spec.Curve25519.E] interface so that downstream phases B and C can
    state round-trip and canonicality theorems against the same
    [edwards25519_point] type used in [Crypto.Curves.Edwards].

    Status: NO PROOFS — Gallina well-typed only.  Round-trip,
    canonicality, and rejection theorems are deferred to Phase B.

    The §A.2 29 rejection test vectors of RFC 9496 are recorded at the
    bottom as [Definition] constants.  Their actual rejection by
    [ristretto_decode_coords] is left as a [vm_compute] assertion to be
    proved in Phase B.

    Companion file: [Ristretto255_Encode.v] (sister agent A.1, landed in
    commit 763458e).  We reuse A.1's [is_negative], [abs],
    [sqrt_ratio_m1], [SQRT_M1] and [BASEPOINT_COMPRESSED_RFC] verbatim
    so that the encode/decode pair agrees bit-for-bit on which root is
    canonical, the sign predicate, and the basepoint test vector.

    ADR alignment with A.1 (per RISTRETTO255_ENCODING_PLAN §12):

      - byte form  := [list Byte.byte] of length 32 (NOT [Vector.t]),
                       to match A.1's choice and existing AUCurves
                       [LittleEndianList] conventions.
      - point form := affine [(F.F p) * (F.F p)] (output of decode).
                       A.1's encode side takes extended Edwards
                       [(X, Y, Z, T)]; the encode/decode boundary thus
                       has a [from_affine] step on the encode side and
                       a [to_extended] step on the decode side (both
                       handled in downstream phases).
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import NArith.NArith.
Require Import coqutil.Byte.
Require Import coqutil.Word.LittleEndianList.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.Curve25519.
Require Import Bedrock.Field.Synthesis.Examples.Ristretto255_Encode.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Base field abbreviation (matches A.1's [Fp]).

    Re-exported here so callers don't have to thread the [F.F p] type
    through every spec.  The [F_scope] is opened for the algorithmic
    body. *)
Local Notation Fp := (F.F (2^255 - 19)).
Local Notation Fzero := (F.of_Z _ 0).
Local Notation Fone  := (F.of_Z _ 1).
Local Open Scope F_scope.

(** ** [bytes_to_canonical_F bs : option Fp]

    Reads 32 bytes little-endian into a [Fp].  Returns [None] if
      - the length is not 32, OR
      - bit 255 of the integer is set, OR
      - the integer is >= p (non-canonical).
    Otherwise returns [Some (F.of_Z _ z)].

    Per RFC 9496 §4.3.1 lines 1-2, the decoder rejects both
    non-canonical encodings AND inputs with the sign bit set.  The
    sign-bit check is done at line 3 ([is_negative s]) -- handled
    inside [ristretto_decode_coords]; here we only handle the
    length/canonicality check.
*)
Definition bytes_to_canonical_F (bs : list Byte.byte) : option Fp :=
  if Nat.eqb (length bs) 32 then
    let z := le_combine bs in
    if Z.testbit z 255 then None
    else if Z.ltb z (2^255 - 19) then Some (F.of_Z _ z)
    else None
  else None.

(** ** [ristretto_decode_coords bs] — RFC 9496 §4.3.1 lines 1-14.

    Returns [Some (x, y)] on success (affine Edwards25519 coordinates)
    or [None] on any rejection branch.  The branches mirror the RFC
    exactly:

      Line 1  : s = LE-decode(bs)             — bytes_to_canonical_F.
      Line 2  : reject if non-canonical.       — handled in (1).
      Line 3  : reject if is_negative(s).
      Line 4  : ss      = s^2
      Line 5  : u1      = 1 - ss
      Line 6  : u2      = 1 + ss
      Line 7  : u2_sqr  = u2^2
      Line 8  : v       = -d*u1^2 - u2_sqr
      Line 9  : (was_square, I) = SQRT_RATIO_M1(1, v * u2_sqr)
                                  where the convention is r^2*(v*u2^2) = 1
                                  (or = SQRT_M1 in the non-square branch).
      Line 10 : D_x    = I * u2
      Line 11 : D_y    = I * D_x * v
      Line 12 : x      = abs(2 * s * D_x)
      Line 13 : y      = u1 * D_y
      Line 14 : t      = x * y
      Line 15 : reject if (not was_square) OR is_negative(t) OR y = 0.
      Line 16 : return (x, y).  The full extended-Edwards form is
                  (x, y, 1, x*y); we expose only the affine pair so
                  callers don't need to deal with projective
                  representatives.

    Bug fix 2026-05-22 (B.5a agent finding): the original A.2 draft used
    a simplified [v = d*ss - 1, den = u^2*v] form taken from a different
    decoder variant; algebraic tracing showed it always produced [y = ±1]
    instead of the Edwards y-coordinate.  Replaced with the verbatim
    RFC 9496 §4.3.1 algorithm, matching the Z-mirror in
    [Bedrock.End2End.Lizard.RistrettoDecode.ristretto_decode_gallina].

    The [edwards25519_point] sigma type ([Curve25519.E.point]) requires
    proving the on-curve equation; we obtain that in Phase B via
    [ristretto_decode_bytes_well_typed].  Here we expose only the
    [option (Fp * Fp)] form.
*)
Definition ristretto_decode_coords (bs : list Byte.byte)
  : option (Fp * Fp) :=
  match bytes_to_canonical_F bs with
  | None => None
  | Some s =>
    if is_negative s then None
    else
      let ss     := s * s in
      let u1     := Fone - ss in
      let u2     := Fone + ss in
      let u2_sqr := u2 * u2 in
      let u1_sq  := u1 * u1 in
      let v      := F.opp (Curve25519.E.d * u1_sq) - u2_sqr in
      let den    := v * u2_sqr in
      let '(was_square, invsqrt) := sqrt_ratio_m1 Fone den in
      let Dx     := invsqrt * u2 in
      let Dy     := invsqrt * Dx * v in
      let x_raw  := F.of_Z _ 2 * s * Dx in
      let x      := abs x_raw in
      let y      := u1 * Dy in
      let t      := x * y in
      let y_is_zero : bool := Z.eqb (F.to_Z y) 0 in
      if orb (negb was_square) (orb (is_negative t) y_is_zero)
      then None
      else Some (x, y)
  end.

(** ** Top-level Edwards25519 point in affine coordinates (matches
    [Curve25519.E.point]).  The "real" decoder returns this typed form
    via a Phase-B-pending on-curve obligation. *)
Definition edwards25519_point : Type := Curve25519.E.point.

(** ** Typed decoder, parameterised on the Phase-B on-curve obligation.

    The Phase-A spec returns coordinates only.  Phase B will provide
    the function

      Theorem ristretto_decode_coords_on_curve :
        forall bs x y,
          ristretto_decode_coords bs = Some (x, y) ->
          (Curve25519.E.a * (x * x) + y * y =
           Fone + Curve25519.E.d * (x * x) * (y * y))%F.

    Applying it gives a total [list Byte.byte -> option
    edwards25519_point] without changing the algorithmic structure.
    To keep this file proof-free, we expose the typed form as a
    constructor parameterised on the obligation. *)
Definition ristretto_decode_bytes
  (on_curve_obligation :
    forall (bs : list Byte.byte) (x y : Fp),
      ristretto_decode_coords bs = Some (x, y) ->
      (Curve25519.E.a * (x * x) + y * y =
       Fone + Curve25519.E.d * (x * x) * (y * y))%F)
  (bs : list Byte.byte) : option edwards25519_point :=
  match ristretto_decode_coords bs as r return
        ristretto_decode_coords bs = r -> option edwards25519_point with
  | None        => fun _ => None
  | Some (x, y) =>
      fun H => Some (exist _ (x, y) (on_curve_obligation bs x y H))
  end eq_refl.

(** ============================================================
    RFC 9496 §A.2 — Rejection test vectors.

    The 29 invalid encodings of RFC 9496 Appendix A.2, which MUST decode to
    ERROR (= [None]), in the RFC's groups and order:

      [rfc_A2_noncanonical_*]  non-canonical field encodings (4)
      [rfc_A2_negative_*]      negative field elements (8)
      [rfc_A2_nonsquare_*]     non-square x^2 (8)
      [rfc_A2_negative_xy_*]   negative x * y value (8)
      [rfc_A2_s_minus_one_01]  s = -1, which causes y = 0 (1)

    The bytes are copied from the RFC text; [ristretto_decode_coords v = None]
    for each is proved in [Ristretto255_DecodeReject.v].
============================================================ *)

(** Helper: build a 32-byte list from a 32-list of [Z] values in [0..255]. *)
Local Open Scope Z_scope.
Definition mk_vec32 (l : list Z) : list Byte.byte :=
  List.map (fun z => match Byte.of_N (Z.to_N z) with
                     | Some b => b
                     | None => Byte.x00
                     end) l.

(** *** Non-canonical field encodings (4). *)
Definition rfc_A2_noncanonical_01 : list Byte.byte := mk_vec32
  [0x00;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;
   0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;
   0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff].

Definition rfc_A2_noncanonical_02 : list Byte.byte := mk_vec32
  [0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;
   0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;
   0xff;0xff;0xff;0xff;0xff;0xff;0xff;0x7f].

Definition rfc_A2_noncanonical_03 : list Byte.byte := mk_vec32
  [0xf3;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;
   0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;
   0xff;0xff;0xff;0xff;0xff;0xff;0xff;0x7f].

Definition rfc_A2_noncanonical_04 : list Byte.byte := mk_vec32
  [0xed;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;
   0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;
   0xff;0xff;0xff;0xff;0xff;0xff;0xff;0x7f].

(** *** Negative field elements (8). *)
Definition rfc_A2_negative_01 : list Byte.byte := mk_vec32
  [0x01;0x00;0x00;0x00;0x00;0x00;0x00;0x00;0x00;0x00;0x00;0x00;
   0x00;0x00;0x00;0x00;0x00;0x00;0x00;0x00;0x00;0x00;0x00;0x00;
   0x00;0x00;0x00;0x00;0x00;0x00;0x00;0x00].

Definition rfc_A2_negative_02 : list Byte.byte := mk_vec32
  [0x01;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;
   0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;
   0xff;0xff;0xff;0xff;0xff;0xff;0xff;0x7f].

Definition rfc_A2_negative_03 : list Byte.byte := mk_vec32
  [0xed;0x57;0xff;0xd8;0xc9;0x14;0xfb;0x20;0x14;0x71;0xd1;0xc3;
   0xd2;0x45;0xce;0x3c;0x74;0x6f;0xcb;0xe6;0x3a;0x36;0x79;0xd5;
   0x1b;0x6a;0x51;0x6e;0xbe;0xbe;0x0e;0x20].

Definition rfc_A2_negative_04 : list Byte.byte := mk_vec32
  [0xc3;0x4c;0x4e;0x18;0x26;0xe5;0xd4;0x03;0xb7;0x8e;0x24;0x6e;
   0x88;0xaa;0x05;0x1c;0x36;0xcc;0xf0;0xaa;0xfe;0xbf;0xfe;0x13;
   0x7d;0x14;0x8a;0x2b;0xf9;0x10;0x45;0x62].

Definition rfc_A2_negative_05 : list Byte.byte := mk_vec32
  [0xc9;0x40;0xe5;0xa4;0x40;0x41;0x57;0xcf;0xb1;0x62;0x8b;0x10;
   0x8d;0xb0;0x51;0xa8;0xd4;0x39;0xe1;0xa4;0x21;0x39;0x4e;0xc4;
   0xeb;0xcc;0xb9;0xec;0x92;0xa8;0xac;0x78].

Definition rfc_A2_negative_06 : list Byte.byte := mk_vec32
  [0x47;0xcf;0xc5;0x49;0x7c;0x53;0xdc;0x8e;0x61;0xc9;0x1d;0x17;
   0xfd;0x62;0x6f;0xfb;0x1c;0x49;0xe2;0xbc;0xa9;0x4e;0xed;0x05;
   0x22;0x81;0xb5;0x10;0xb1;0x11;0x7a;0x24].

Definition rfc_A2_negative_07 : list Byte.byte := mk_vec32
  [0xf1;0xc6;0x16;0x5d;0x33;0x36;0x73;0x51;0xb0;0xda;0x8f;0x6e;
   0x45;0x11;0x01;0x0c;0x68;0x17;0x4a;0x03;0xb6;0x58;0x12;0x12;
   0xc7;0x1c;0x0e;0x1d;0x02;0x6c;0x3c;0x72].

Definition rfc_A2_negative_08 : list Byte.byte := mk_vec32
  [0x87;0x26;0x0f;0x7a;0x2f;0x12;0x49;0x51;0x18;0x36;0x0f;0x02;
   0xc2;0x6a;0x47;0x0f;0x45;0x0d;0xad;0xf3;0x4a;0x41;0x3d;0x21;
   0x04;0x2b;0x43;0xb9;0xd9;0x3e;0x13;0x09].

(** *** Non-square x^2 (8). *)
Definition rfc_A2_nonsquare_01 : list Byte.byte := mk_vec32
  [0x26;0x94;0x8d;0x35;0xca;0x62;0xe6;0x43;0xe2;0x6a;0x83;0x17;
   0x73;0x32;0xe6;0xb6;0xaf;0xeb;0x9d;0x08;0xe4;0x26;0x8b;0x65;
   0x0f;0x1f;0x5b;0xbd;0x8d;0x81;0xd3;0x71].

Definition rfc_A2_nonsquare_02 : list Byte.byte := mk_vec32
  [0x4e;0xac;0x07;0x7a;0x71;0x3c;0x57;0xb4;0xf4;0x39;0x76;0x29;
   0xa4;0x14;0x59;0x82;0xc6;0x61;0xf4;0x80;0x44;0xdd;0x3f;0x96;
   0x42;0x7d;0x40;0xb1;0x47;0xd9;0x74;0x2f].

Definition rfc_A2_nonsquare_03 : list Byte.byte := mk_vec32
  [0xde;0x6a;0x7b;0x00;0xde;0xad;0xc7;0x88;0xeb;0x6b;0x6c;0x8d;
   0x20;0xc0;0xae;0x96;0xc2;0xf2;0x01;0x90;0x78;0xfa;0x60;0x4f;
   0xee;0x5b;0x87;0xd6;0xe9;0x89;0xad;0x7b].

Definition rfc_A2_nonsquare_04 : list Byte.byte := mk_vec32
  [0xbc;0xab;0x47;0x7b;0xe2;0x08;0x61;0xe0;0x1e;0x4a;0x0e;0x29;
   0x52;0x84;0x14;0x6a;0x51;0x01;0x50;0xd9;0x81;0x77;0x63;0xca;
   0xf1;0xa6;0xf4;0xb4;0x22;0xd6;0x70;0x42].

Definition rfc_A2_nonsquare_05 : list Byte.byte := mk_vec32
  [0x2a;0x29;0x2d;0xf7;0xe3;0x2c;0xab;0xab;0xbd;0x9d;0xe0;0x88;
   0xd1;0xd1;0xab;0xec;0x9f;0xc0;0x44;0x0f;0x63;0x7e;0xd2;0xfb;
   0xa1;0x45;0x09;0x4d;0xc1;0x4b;0xea;0x08].

Definition rfc_A2_nonsquare_06 : list Byte.byte := mk_vec32
  [0xf4;0xa9;0xe5;0x34;0xfc;0x0d;0x21;0x6c;0x44;0xb2;0x18;0xfa;
   0x0c;0x42;0xd9;0x96;0x35;0xa0;0x12;0x7e;0xe2;0xe5;0x3c;0x71;
   0x2f;0x70;0x60;0x96;0x49;0xfd;0xff;0x22].

Definition rfc_A2_nonsquare_07 : list Byte.byte := mk_vec32
  [0x82;0x68;0x43;0x6f;0x8c;0x41;0x26;0x19;0x6c;0xf6;0x4b;0x3c;
   0x7d;0xdb;0xda;0x90;0x74;0x6a;0x37;0x86;0x25;0xf9;0x81;0x3d;
   0xd9;0xb8;0x45;0x70;0x77;0x25;0x67;0x31].

Definition rfc_A2_nonsquare_08 : list Byte.byte := mk_vec32
  [0x28;0x10;0xe5;0xcb;0xc2;0xcc;0x4d;0x4e;0xec;0xe5;0x4f;0x61;
   0xc6;0xf6;0x97;0x58;0xe2;0x89;0xaa;0x7a;0xb4;0x40;0xb3;0xcb;
   0xea;0xa2;0x19;0x95;0xc2;0xf4;0x23;0x2b].

(** *** Negative x * y value (8). *)
Definition rfc_A2_negative_xy_01 : list Byte.byte := mk_vec32
  [0x3e;0xb8;0x58;0xe7;0x8f;0x5a;0x72;0x54;0xd8;0xc9;0x73;0x11;
   0x74;0xa9;0x4f;0x76;0x75;0x5f;0xd3;0x94;0x1c;0x0a;0xc9;0x37;
   0x35;0xc0;0x7b;0xa1;0x45;0x79;0x63;0x0e].

Definition rfc_A2_negative_xy_02 : list Byte.byte := mk_vec32
  [0xa4;0x5f;0xdc;0x55;0xc7;0x64;0x48;0xc0;0x49;0xa1;0xab;0x33;
   0xf1;0x70;0x23;0xed;0xfb;0x2b;0xe3;0x58;0x1e;0x9c;0x7a;0xad;
   0xe8;0xa6;0x12;0x52;0x15;0xe0;0x42;0x20].

Definition rfc_A2_negative_xy_03 : list Byte.byte := mk_vec32
  [0xd4;0x83;0xfe;0x81;0x3c;0x6b;0xa6;0x47;0xeb;0xbf;0xd3;0xec;
   0x41;0xad;0xca;0x1c;0x61;0x30;0xc2;0xbe;0xee;0xe9;0xd9;0xbf;
   0x06;0x5c;0x8d;0x15;0x1c;0x5f;0x39;0x6e].

Definition rfc_A2_negative_xy_04 : list Byte.byte := mk_vec32
  [0x8a;0x2e;0x1d;0x30;0x05;0x01;0x98;0xc6;0x5a;0x54;0x48;0x31;
   0x23;0x96;0x0c;0xcc;0x38;0xae;0xf6;0x84;0x8e;0x1e;0xc8;0xf5;
   0xf7;0x80;0xe8;0x52;0x37;0x69;0xba;0x32].

Definition rfc_A2_negative_xy_05 : list Byte.byte := mk_vec32
  [0x32;0x88;0x84;0x62;0xf8;0xb4;0x86;0xc6;0x8a;0xd7;0xdd;0x96;
   0x10;0xbe;0x51;0x92;0xbb;0xea;0xf3;0xb4;0x43;0x95;0x1a;0xc1;
   0xa8;0x11;0x84;0x19;0xd9;0xfa;0x09;0x7b].

Definition rfc_A2_negative_xy_06 : list Byte.byte := mk_vec32
  [0x22;0x71;0x42;0x50;0x1b;0x9d;0x43;0x55;0xcc;0xba;0x29;0x04;
   0x04;0xbd;0xe4;0x15;0x75;0xb0;0x37;0x69;0x3c;0xef;0x1f;0x43;
   0x8c;0x47;0xf8;0xfb;0xf3;0x5d;0x11;0x65].

Definition rfc_A2_negative_xy_07 : list Byte.byte := mk_vec32
  [0x5c;0x37;0xcc;0x49;0x1d;0xa8;0x47;0xcf;0xeb;0x92;0x81;0xd4;
   0x07;0xef;0xc4;0x1e;0x15;0x14;0x4c;0x87;0x6e;0x01;0x70;0xb4;
   0x99;0xa9;0x6a;0x22;0xed;0x31;0xe0;0x1e].

Definition rfc_A2_negative_xy_08 : list Byte.byte := mk_vec32
  [0x44;0x54;0x25;0x11;0x7c;0xb8;0xc9;0x0e;0xdc;0xbc;0x7c;0x1c;
   0xc0;0xe7;0x4f;0x74;0x7f;0x2c;0x1e;0xfa;0x56;0x30;0xa9;0x67;
   0xc6;0x4f;0x28;0x77;0x92;0xa4;0x8a;0x4b].

(** *** s = -1, which causes y = 0 (1). *)
Definition rfc_A2_s_minus_one_01 : list Byte.byte := mk_vec32
  [0xec;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;
   0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;
   0xff;0xff;0xff;0xff;0xff;0xff;0xff;0x7f].

Definition rfc_A2_rejection_vectors : list (list Byte.byte) :=
  [ rfc_A2_noncanonical_01; rfc_A2_noncanonical_02; rfc_A2_noncanonical_03; rfc_A2_noncanonical_04;
    rfc_A2_negative_01; rfc_A2_negative_02; rfc_A2_negative_03; rfc_A2_negative_04;
    rfc_A2_negative_05; rfc_A2_negative_06; rfc_A2_negative_07; rfc_A2_negative_08;
    rfc_A2_nonsquare_01; rfc_A2_nonsquare_02; rfc_A2_nonsquare_03; rfc_A2_nonsquare_04;
    rfc_A2_nonsquare_05; rfc_A2_nonsquare_06; rfc_A2_nonsquare_07; rfc_A2_nonsquare_08;
    rfc_A2_negative_xy_01; rfc_A2_negative_xy_02; rfc_A2_negative_xy_03; rfc_A2_negative_xy_04;
    rfc_A2_negative_xy_05; rfc_A2_negative_xy_06; rfc_A2_negative_xy_07; rfc_A2_negative_xy_08;
    rfc_A2_s_minus_one_01 ].

Lemma rfc_A2_rejection_vectors_length :
  List.length rfc_A2_rejection_vectors = 29%nat.
Proof. reflexivity. Qed.

Lemma rfc_A2_each_vector_length32 :
  List.Forall (fun v => List.length v = 32%nat) rfc_A2_rejection_vectors.
Proof.
  repeat constructor.
Qed.

Lemma rfc_A2_negative_01_unfold :
  rfc_A2_negative_01 =
    Byte.x01 :: List.repeat Byte.x00 31.
Proof. reflexivity. Qed.

(** ** RFC 9496 §A.1 basepoint round-trip sanity check.

    A.1 exports [BASEPOINT_COMPRESSED_RFC : list Byte.byte] (the
    canonical 32-byte ristretto255 compression of the Ed25519
    basepoint).  The matching round-trip property for the decoder is:

      ristretto_decode_coords BASEPOINT_COMPRESSED_RFC
        = Some (basepoint_Bx, basepoint_By)

    where [basepoint_Bx, basepoint_By : Fp] are A.1's basepoint affine
    coordinates.

    We do NOT discharge this here via [vm_compute]: the decoder calls
    [F.pow] with an exponent of order [2^252], which in the abstract
    [F.F p] representation reduces via a generic positional algorithm
    that is intentionally non-reducing in [Spec.ModularArithmetic].  A
    [native_compute]-friendly variant would require unfolding
    [pow_with_spec] or going through a Z-mirror reduction step.  Both
    options are routine and are scheduled for Phase B's basepoint
    round-trip Qed alongside the [Z]-mirror correspondence proof.

    The Z-level mirror in [Bedrock.End2End.Lizard.RistrettoDecode]
    DOES vm_compute on the same byte string and recovers the basepoint
    extended coordinates packed in a 200-byte slot; the bridge to this
    file's [Fp]-typed coordinates is part of Phase B's mirror lemma.
*)

(** Compatibility re-exports so callers can refer to encode-side
    constants by their decode-side names if they like. *)
Definition rfc_A1_basepoint_compressed : list Byte.byte :=
  BASEPOINT_COMPRESSED_RFC.

Lemma rfc_A1_basepoint_compressed_length :
  List.length rfc_A1_basepoint_compressed = 32%nat.
Proof. exact BASEPOINT_COMPRESSED_RFC_length. Qed.

(** Phase A.2 complete:
      - [ristretto_decode_coords : list Byte.byte -> option (Fp * Fp)]
        is well-typed Gallina, mirroring RFC 9496 §4.3.1 lines 1-14.
      - [ristretto_decode_bytes] is parameterised on the Phase B
        on-curve obligation and returns [option edwards25519_point].
      - 29 RFC §A.2 rejection vectors recorded as [Definition]
        constants with length lemmas.
      - Field primitives ([is_negative], [abs], [sqrt_ratio_m1],
        [SQRT_M1], [BASEPOINT_COMPRESSED_RFC]) shared verbatim with
        A.1 via [Bedrock.Field.Synthesis.Examples.Ristretto255_Encode]. *)
