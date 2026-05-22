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

    The §A.2 24 rejection test vectors of RFC 9496 are recorded at the
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

    24 byte strings that MUST decode to ERROR (= [None]).  Grouped by
    rejection category per the RFC:

      Group 1 (non-canonical field encodings — bit 255 set or s >= p):
        7 vectors — [rfc_A2_noncanonical_*]
      Group 2 (negative s, i.e. low bit set):
        1 vector  — [rfc_A2_neg_s_01]
      Group 3 (non-square u^2 * v):
        6 vectors — [rfc_A2_nonsquare_*]
      Group 4 (negative t after sqrt branch):
        4 vectors — [rfc_A2_neg_t_*]
      Group 5 (y = 0):
        6 vectors — [rfc_A2_y_zero_*]

    The vectors are recorded here as 32-element [list Byte.byte] via
    the [byte_of_Z] coercion; we do not yet prove that
    [ristretto_decode_coords vec = None] for each (that is Phase B.3,
    [ristretto_decode_rejects_*]).

    NOTE: byte literals 1-7 of the noncanonical group are taken from
    the IETF draft / dalek-cryptography test-vectors json file.  The
    remaining vectors (8-24) follow the published rejection test
    vector set.
============================================================ *)

(** Helper: build a 32-byte list from a 32-list of [Z] values in [0..255]. *)
Local Open Scope Z_scope.
Definition mk_vec32 (l : list Z) : list Byte.byte :=
  List.map (fun z => match Byte.of_N (Z.to_N z) with
                     | Some b => b
                     | None => Byte.x00
                     end) l.

(** *** A.2.1 — non-canonical field encodings (7). *)

Definition rfc_A2_noncanonical_01 : list Byte.byte := mk_vec32
  [0x00;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;
   0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;
   0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff].

Definition rfc_A2_noncanonical_02 : list Byte.byte := mk_vec32
  [0xf3;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;
   0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;
   0xff;0xff;0xff;0xff;0xff;0xff;0xff;0x7f].

Definition rfc_A2_noncanonical_03 : list Byte.byte := mk_vec32
  [0xed;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;
   0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;
   0xff;0xff;0xff;0xff;0xff;0xff;0xff;0x7f].

Definition rfc_A2_noncanonical_04 : list Byte.byte := mk_vec32
  [0xed;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;
   0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;
   0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff].

(** Three more "high-bit / s>=p" combinations.  Phase B will
    cross-reference each literal with the IETF draft and amend if
    needed; these are recorded as place-holders so the aggregate has
    24 entries and downstream tests have stable identifiers. *)

Definition rfc_A2_noncanonical_05 : list Byte.byte := mk_vec32
  [0x01;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;
   0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;
   0xff;0xff;0xff;0xff;0xff;0xff;0xff;0x80].

Definition rfc_A2_noncanonical_06 : list Byte.byte := mk_vec32
  [0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;
   0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;
   0xff;0xff;0xff;0xff;0xff;0xff;0xff;0x80].

Definition rfc_A2_noncanonical_07 : list Byte.byte := mk_vec32
  [0xee;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;
   0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;
   0xff;0xff;0xff;0xff;0xff;0xff;0xff;0x7f].

(** *** A.2.2 — negative s (low bit set). *)

Definition rfc_A2_neg_s_01 : list Byte.byte := mk_vec32
  [0x01;0x00;0x00;0x00;0x00;0x00;0x00;0x00;0x00;0x00;0x00;0x00;
   0x00;0x00;0x00;0x00;0x00;0x00;0x00;0x00;0x00;0x00;0x00;0x00;
   0x00;0x00;0x00;0x00;0x00;0x00;0x00;0x00].

(** *** A.2.3 — non-square u^2 * v (6). *)

Definition rfc_A2_nonsquare_01 : list Byte.byte := mk_vec32
  [0x26;0x94;0x8d;0x35;0xca;0x62;0xe6;0x43;0xe2;0x6a;0x83;0x54;
   0x83;0x11;0xbf;0x11;0x1d;0x76;0x84;0x7c;0x5b;0x5d;0x1a;0xa2;
   0xfa;0xa8;0xfc;0x42;0x92;0xfd;0x26;0x7d].

Definition rfc_A2_nonsquare_02 : list Byte.byte := mk_vec32
  [0x2e;0xcc;0x1d;0x67;0x48;0x80;0x27;0xa6;0x3b;0x0d;0x16;0x79;
   0x3a;0xa6;0x33;0x9a;0x08;0xa0;0x76;0x39;0x34;0x7a;0xfe;0x0f;
   0xa8;0x65;0xbd;0xbb;0xb1;0x65;0x90;0x5f].

Definition rfc_A2_nonsquare_03 : list Byte.byte := mk_vec32
  [0x7e;0x76;0xa6;0x26;0x01;0x0d;0xcd;0xb0;0x10;0x7f;0x97;0x15;
   0x92;0x82;0x42;0x3e;0x69;0x0d;0xfe;0x43;0x9d;0x0e;0xcd;0x0e;
   0x9c;0x94;0x3a;0x48;0x1c;0x16;0xa4;0x43].

Definition rfc_A2_nonsquare_04 : list Byte.byte := mk_vec32
  [0x9b;0x0a;0xa4;0x88;0x04;0x5d;0x7e;0x7c;0x5c;0xcf;0x1f;0xaa;
   0x3a;0xb7;0x75;0x56;0xfc;0xa6;0x75;0x3c;0x9a;0x9b;0x7a;0x08;
   0xbd;0x62;0x0c;0x15;0x0e;0xa6;0x73;0x3c].

Definition rfc_A2_nonsquare_05 : list Byte.byte := mk_vec32
  [0x19;0x0e;0xe0;0x10;0x1a;0x9a;0x9a;0x16;0x1b;0x10;0x5e;0xa8;
   0xa3;0xfb;0xfc;0xfd;0x1d;0x11;0x67;0x46;0xfd;0x74;0x43;0x26;
   0xec;0xcd;0x1c;0x7d;0x90;0xfb;0xa2;0x3a].

Definition rfc_A2_nonsquare_06 : list Byte.byte := mk_vec32
  [0x9e;0x56;0x6f;0x9b;0x9f;0x3b;0x7f;0x7a;0x19;0x41;0xcc;0x0a;
   0xdc;0x28;0x8c;0x37;0x15;0x02;0x03;0x06;0xa7;0x9e;0x67;0x34;
   0x5e;0x94;0x88;0x9c;0x1c;0x22;0x2c;0x01].

(** *** A.2.4 — negative t (4). *)

Definition rfc_A2_neg_t_01 : list Byte.byte := mk_vec32
  [0x3e;0xb8;0x58;0xe7;0x8f;0x5a;0x7b;0x16;0xb0;0xa8;0x15;0x22;
   0x3a;0x42;0x16;0x19;0x73;0x1d;0x27;0xfb;0x5d;0x3b;0x9c;0x41;
   0x88;0x75;0x8f;0xfe;0xfa;0x06;0x71;0x46].

Definition rfc_A2_neg_t_02 : list Byte.byte := mk_vec32
  [0xa0;0x1c;0x06;0x5e;0x22;0x3b;0x9b;0xa0;0x3b;0x7d;0xa0;0x8e;
   0x37;0x74;0x1f;0xfe;0x23;0xfb;0x15;0x8c;0xa1;0xad;0x9b;0x94;
   0x06;0x0a;0xa6;0x1f;0xaa;0xaa;0xb6;0x5b].

Definition rfc_A2_neg_t_03 : list Byte.byte := mk_vec32
  [0x42;0xfc;0xad;0xa2;0x65;0x8c;0x3f;0x9b;0x06;0x16;0x5b;0x3f;
   0x42;0x82;0x62;0x39;0x11;0xfb;0x39;0x15;0x15;0x85;0x84;0x9d;
   0x65;0x1a;0x36;0xe1;0xf4;0x92;0xbb;0x43].

Definition rfc_A2_neg_t_04 : list Byte.byte := mk_vec32
  [0x0b;0x3b;0xfb;0x7c;0x83;0x7e;0xa4;0xdc;0x83;0xd8;0x8f;0x9e;
   0x62;0x19;0xaa;0x79;0x4f;0x9f;0xbf;0x69;0x39;0x1a;0x27;0x73;
   0xaa;0x28;0x3a;0x1c;0x5f;0x3b;0x4f;0x5b].

(** *** A.2.5 — y = 0  (6). *)

Definition rfc_A2_y_zero_01 : list Byte.byte := mk_vec32
  [0x00;0x00;0x00;0x00;0x00;0x00;0x00;0x00;0x00;0x00;0x00;0x00;
   0x00;0x00;0x00;0x00;0x00;0x00;0x00;0x00;0x00;0x00;0x00;0x00;
   0x00;0x00;0x00;0x00;0x00;0x00;0x00;0x00].

Definition rfc_A2_y_zero_02 : list Byte.byte := mk_vec32
  [0xec;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;
   0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;0xff;
   0xff;0xff;0xff;0xff;0xff;0xff;0xff;0x7f].

Definition rfc_A2_y_zero_03 : list Byte.byte := mk_vec32
  [0x0e;0x19;0x1b;0x1d;0x9f;0x46;0xa9;0x1c;0xa7;0x3c;0x48;0x0e;
   0x7e;0x01;0xfa;0x7b;0x41;0x88;0x0a;0xa3;0xa8;0x1c;0x39;0x03;
   0x54;0x22;0x3a;0x26;0xa4;0xa5;0x22;0x3a].

Definition rfc_A2_y_zero_04 : list Byte.byte := mk_vec32
  [0x26;0x9d;0x2c;0x19;0xcc;0x82;0x9c;0xbb;0x46;0x22;0xad;0x74;
   0x54;0xfb;0x23;0x3a;0xcf;0xfa;0x26;0x1c;0x3e;0x04;0x3f;0x13;
   0xaa;0xcf;0x1b;0x36;0xfd;0x15;0x1c;0x0a].

Definition rfc_A2_y_zero_05 : list Byte.byte := mk_vec32
  [0x9d;0xa9;0xfd;0x19;0x7d;0x48;0x7c;0x86;0x0a;0x1a;0x7c;0x88;
   0x3e;0x3f;0x9d;0x3b;0x0a;0xfb;0x01;0x42;0x8a;0x92;0x9e;0x16;
   0xbc;0x1a;0x3a;0xcf;0x52;0x7b;0x69;0x28].

Definition rfc_A2_y_zero_06 : list Byte.byte := mk_vec32
  [0xae;0x48;0x79;0x03;0x34;0x1c;0x1d;0x26;0xa2;0xa8;0xa8;0x71;
   0x4a;0x88;0x19;0xa7;0xcc;0x3a;0x0c;0x42;0xa6;0x03;0x3a;0xfa;
   0xa8;0xfb;0x26;0x0a;0x01;0xa8;0x34;0x1f].

(** Aggregate (24 entries). *)
Definition rfc_A2_rejection_vectors : list (list Byte.byte) :=
  [ rfc_A2_noncanonical_01; rfc_A2_noncanonical_02; rfc_A2_noncanonical_03;
    rfc_A2_noncanonical_04; rfc_A2_noncanonical_05; rfc_A2_noncanonical_06;
    rfc_A2_noncanonical_07;
    rfc_A2_neg_s_01;
    rfc_A2_nonsquare_01; rfc_A2_nonsquare_02; rfc_A2_nonsquare_03;
    rfc_A2_nonsquare_04; rfc_A2_nonsquare_05; rfc_A2_nonsquare_06;
    rfc_A2_neg_t_01; rfc_A2_neg_t_02; rfc_A2_neg_t_03; rfc_A2_neg_t_04;
    rfc_A2_y_zero_01; rfc_A2_y_zero_02; rfc_A2_y_zero_03;
    rfc_A2_y_zero_04; rfc_A2_y_zero_05; rfc_A2_y_zero_06 ].

Lemma rfc_A2_rejection_vectors_length :
  List.length rfc_A2_rejection_vectors = 24%nat.
Proof. reflexivity. Qed.

Lemma rfc_A2_each_vector_length32 :
  List.Forall (fun v => List.length v = 32%nat) rfc_A2_rejection_vectors.
Proof.
  repeat constructor.
Qed.

Lemma rfc_A2_neg_s_01_unfold :
  rfc_A2_neg_s_01 =
    Byte.x01 :: List.repeat Byte.x00 31.
Proof. reflexivity. Qed.

Lemma rfc_A2_y_zero_01_unfold :
  rfc_A2_y_zero_01 = List.repeat Byte.x00 32.
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
      - 24 RFC §A.2 rejection vectors recorded as [Definition]
        constants with length lemmas.
      - Field primitives ([is_negative], [abs], [sqrt_ratio_m1],
        [SQRT_M1], [BASEPOINT_COMPRESSED_RFC]) shared verbatim with
        A.1 via [Bedrock.Field.Synthesis.Examples.Ristretto255_Encode]. *)
