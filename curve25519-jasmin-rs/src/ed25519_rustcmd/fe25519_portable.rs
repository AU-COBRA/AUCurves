//! Portable `fe25519_*` shim for the decomposed Ed25519 bodies.
//!
//! Backs each field-op leaf required by `decomposed_bodies.rs` with
//! fiat-crypto's verified radix-2^51 Curve25519 arithmetic
//! (`fiat-crypto::curve25519_64`).
//!
//! ## Representation
//!
//! Each 40-byte field-element slot used by the decomposed bodies is
//! the bedrock2-level `le_split 40 z` encoding of a 256-bit field
//! element — i.e., the integer `z` packed as 40 LE bytes, with the
//! top 8 bytes always zero for canonical values
//! (see `ScalarmultBaseVerified.v` `base_point_xyzt`).
//! We bridge to fiat's `fiat_25519_tight_field_element` (5 × u64
//! radix-2^51 limbs) via `fiat_25519_from_bytes` (consumes 32 LE
//! bytes — the canonical low-order portion) and `fiat_25519_to_bytes`
//! (emits 32 LE bytes — canonical representative in [0, p)).
//!
//! ## Tight vs loose
//!
//! fiat's API distinguishes two limb-bound regimes:
//!   * `tight`   — limbs are < 2^51 + ε (stable for ≥1 mul/sqr ahead)
//!   * `loose`   — limbs may grow to ~2^54 (result of `add`, `sub`,
//!                 multiple chained `add`s); must be reduced via
//!                 `fiat_25519_carry` before crossing into
//!                 `carry_mul`/`carry_square` as a *tight* input.
//!
//! `fiat_25519_carry_mul` / `fiat_25519_carry_square` ingest `loose`
//! and emit `tight`; `fiat_25519_add` / `fiat_25519_sub` ingest
//! `tight` and emit `loose`; `fiat_25519_relax` is a no-op view of
//! tight as loose.
//!
//! Our 40-byte byte slot always stores a `tight` value, so:
//!   - `fe25519_mul/sqr` : tight → relax → loose → carry_mul → tight
//!   - `fe25519_add/sub` : tight → add/sub → loose → carry → tight
//!
//! ## Compound ops
//!
//! * `fe25519_mul_2(out, a)`         := 2·a            (= add a a, carry)
//! * `fe25519_mul_d2(out, a)`        := 2d·a           (carry_mul with `2d` constant)
//! * `fe25519_sqr_scale2(out, a)`    := 2·a²           (sqr, then add to self, carry)
//! * `fe25519_sqr_sub2(out, x, a, b)`:= x² − a − b     (sqr, sub a, then sub b)
//! * `fe25519_neg_add(out, a, b)`    := −(a + b)       (per `XyztDoubleBodyDecomposed.v`:
//!                                                    `H = -(A + B)`)
//!
//! The 2d constant is the well-known Edwards `2d_25519`; its 5
//! radix-2^51 limbs are pre-computed below.  See
//! https://datatracker.ietf.org/doc/html/rfc8032#section-5.1 for d's
//! value (-121665/121666 mod p).

#![cfg(all(any(feature = "decomposed_leaves",
               feature = "inline_leaves",
               feature = "wnaf_comb_leaves"),
           not(feature = "dalek_leaves")))]
#![allow(non_snake_case)]

use fiat_crypto::curve25519_64::{
    fiat_25519_add, fiat_25519_carry, fiat_25519_carry_mul, fiat_25519_carry_square,
    fiat_25519_from_bytes, fiat_25519_loose_field_element, fiat_25519_relax, fiat_25519_sub,
    fiat_25519_tight_field_element, fiat_25519_to_bytes,
};

// ---------------------------------------------------------------------------
// Pre-computed Edwards `2d_25519` in radix-2^51 limb form.
//
// d   = -121665 / 121666 mod p          (Curve25519 prime p = 2^255 - 19)
// 2d  =  16295367250680780974490674513165176452449235426866156013048779062215315747161
//
// 5 × 51-bit limbs (little-endian, LSB-first):
//   limb[0] = 0x069B9426B2F159     = 1859910466990425
//   limb[1] = 0x035050762ADD7A     =  932731440258426
//   limb[2] = 0x03CF44C0038052     = 1072319116312658
//   limb[3] = 0x06738CC7407977     = 1815898335770999
//   limb[4] = 0x02406D9DC56DFF     =  633789495995903
//
// (Verified by python:  ((2 * (-121665 * pow(121666, -1, p))) % p
//   then >> 51*i & ((1<<51)-1) for i in 0..5.)
//
// Stored as a `tight` element — these limbs are well within the
// fiat tight bound (< 2^51 + ε), so carry_mul accepts the relaxed
// view directly.
const TWO_D_LIMBS: [u64; 5] = [
    1859910466990425u64,
    932731440258426u64,
    1072319116312658u64,
    1815898335770999u64,
    633789495995903u64,
];

// ---------------------------------------------------------------------------
// Byte ↔ limb codecs.
//
// The 40-byte slot holds `le_split 40 z` for some `z < p < 2^255`,
// so its first 32 bytes (top bit clear) are exactly the canonical
// 32-byte LE encoding consumed by `fiat_25519_from_bytes`; the
// trailing 8 bytes are always zero for canonical inputs.  We
// *re-zero* the trailing 8 bytes on write so the slot stays
// canonical (matching `le_split 40 z` exactly).

#[inline(always)]
fn read_tight(bytes: &[u8; 40]) -> fiat_25519_tight_field_element {
    let mut head = [0u8; 32];
    head.copy_from_slice(&bytes[0..32]);
    // Defensive: spec requires top bit clear.  `le_split 40` of any
    // value < p < 2^255 has bit 255 = 0; we mask just in case.
    head[31] &= 0x7f;
    let mut out = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_from_bytes(&mut out, &head);
    out
}

#[inline(always)]
fn write_tight(bytes: &mut [u8; 40], fe: &fiat_25519_tight_field_element) {
    let mut head = [0u8; 32];
    fiat_25519_to_bytes(&mut head, fe);
    bytes[0..32].copy_from_slice(&head);
    // Pad trailing 8 bytes to zero (canonical 40-byte slot).
    for byte in &mut bytes[32..40] {
        *byte = 0;
    }
}

#[inline(always)]
fn relax(fe: &fiat_25519_tight_field_element) -> fiat_25519_loose_field_element {
    let mut out = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_relax(&mut out, fe);
    out
}

#[inline(always)]
unsafe fn read_tight_ptr(p: *const u8) -> fiat_25519_tight_field_element {
    let r: &[u8; 40] = unsafe { &*(p as *const [u8; 40]) };
    read_tight(r)
}

#[inline(always)]
unsafe fn write_tight_ptr(p: *mut u8, fe: &fiat_25519_tight_field_element) {
    let w: &mut [u8; 40] = unsafe { &mut *(p as *mut [u8; 40]) };
    write_tight(w, fe);
}

// ---------------------------------------------------------------------------
// Field ops — primitive.

/// out := a + b   (mod p), stored tight.
#[cfg_attr(all(not(feature = "cryptopt_leaves"), not(feature = "tfp25519_limbs")), unsafe(no_mangle))]
pub unsafe extern "C" fn fe25519_add(out: *mut u8, a: *const u8, b: *const u8) {
    let at = unsafe { read_tight_ptr(a) };
    let bt = unsafe { read_tight_ptr(b) };
    let mut sum = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_add(&mut sum, &at, &bt);
    let mut r = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry(&mut r, &sum);
    unsafe { write_tight_ptr(out, &r) };
}

/// out := a − b   (mod p), stored tight.
#[cfg_attr(all(not(feature = "cryptopt_leaves"), not(feature = "tfp25519_limbs")), unsafe(no_mangle))]
pub unsafe extern "C" fn fe25519_sub(out: *mut u8, a: *const u8, b: *const u8) {
    let at = unsafe { read_tight_ptr(a) };
    let bt = unsafe { read_tight_ptr(b) };
    let mut diff = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_sub(&mut diff, &at, &bt);
    let mut r = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry(&mut r, &diff);
    unsafe { write_tight_ptr(out, &r) };
}

/// out := a · b   (mod p), stored tight.
#[cfg_attr(all(not(feature = "cryptopt_leaves"), not(feature = "tfp25519_limbs")), unsafe(no_mangle))]
pub unsafe extern "C" fn fe25519_mul(out: *mut u8, a: *const u8, b: *const u8) {
    let at = unsafe { read_tight_ptr(a) };
    let bt = unsafe { read_tight_ptr(b) };
    let al = relax(&at);
    let bl = relax(&bt);
    let mut r = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry_mul(&mut r, &al, &bl);
    unsafe { write_tight_ptr(out, &r) };
}

/// out := a²   (mod p), stored tight.
#[cfg_attr(all(not(feature = "cryptopt_leaves"), not(feature = "tfp25519_limbs")), unsafe(no_mangle))]
pub unsafe extern "C" fn fe25519_sqr(out: *mut u8, a: *const u8) {
    let at = unsafe { read_tight_ptr(a) };
    let al = relax(&at);
    let mut r = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry_square(&mut r, &al);
    unsafe { write_tight_ptr(out, &r) };
}

// ---------------------------------------------------------------------------
// Field ops — compound.

/// out := 2 · a   (used in xyzt_add: D = 2·Z1·Z2-precursor).
#[cfg_attr(all(not(feature = "cryptopt_leaves"), not(feature = "tfp25519_limbs")), unsafe(no_mangle))]
pub unsafe extern "C" fn fe25519_mul_2(out: *mut u8, a: *const u8) {
    let at = unsafe { read_tight_ptr(a) };
    let mut sum = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_add(&mut sum, &at, &at);
    let mut r = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry(&mut r, &sum);
    unsafe { write_tight_ptr(out, &r) };
}

/// out := 2d · a   (Edwards d2 constant; xyzt_add: C = 2d·T1·T2 step).
#[cfg_attr(all(not(feature = "cryptopt_leaves"), not(feature = "tfp25519_limbs")), unsafe(no_mangle))]
pub unsafe extern "C" fn fe25519_mul_d2(out: *mut u8, a: *const u8) {
    let at = unsafe { read_tight_ptr(a) };
    let al = relax(&at);
    // 2d as a loose element: limbs already fit in tight bound, so the
    // loose view is a no-op copy via the same limbs.
    let two_d_tight = fiat_25519_tight_field_element(TWO_D_LIMBS);
    let two_d_loose = relax(&two_d_tight);
    let mut r = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry_mul(&mut r, &al, &two_d_loose);
    unsafe { write_tight_ptr(out, &r) };
}

/// out := 2 · a²   (Edwards C in double formula: C = 2·Z²).
#[cfg_attr(all(not(feature = "cryptopt_leaves"), not(feature = "tfp25519_limbs")), unsafe(no_mangle))]
pub unsafe extern "C" fn fe25519_sqr_scale2(out: *mut u8, a: *const u8) {
    let at = unsafe { read_tight_ptr(a) };
    let al = relax(&at);
    let mut sq = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry_square(&mut sq, &al);
    let mut twice = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_add(&mut twice, &sq, &sq);
    let mut r = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry(&mut r, &twice);
    unsafe { write_tight_ptr(out, &r) };
}

/// out := a² − b − c   (used in xyzt_double_decomposed:
/// `E = (X+Y)² − A − B`, where the caller passes the squared input).
#[cfg_attr(all(not(feature = "cryptopt_leaves"), not(feature = "tfp25519_limbs")), unsafe(no_mangle))]
pub unsafe extern "C" fn fe25519_sqr_sub2(
    out: *mut u8,
    a: *const u8,
    b: *const u8,
    c: *const u8,
) {
    // 1. Compute a² (tight).
    let at = unsafe { read_tight_ptr(a) };
    let al = relax(&at);
    let mut sq = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry_square(&mut sq, &al);

    // 2. Subtract b: sq - b → loose → carry → tight.
    let bt = unsafe { read_tight_ptr(b) };
    let mut diff1_loose = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_sub(&mut diff1_loose, &sq, &bt);
    let mut diff1 = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry(&mut diff1, &diff1_loose);

    // 3. Subtract c: diff1 - c → loose → carry → tight.
    let ct = unsafe { read_tight_ptr(c) };
    let mut diff2_loose = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_sub(&mut diff2_loose, &diff1, &ct);
    let mut r = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry(&mut r, &diff2_loose);
    unsafe { write_tight_ptr(out, &r) };
}

/// out := −(a + b)   (used in xyzt_double_decomposed: `H = -(A + B)`).
#[cfg_attr(all(not(feature = "cryptopt_leaves"), not(feature = "tfp25519_limbs")), unsafe(no_mangle))]
pub unsafe extern "C" fn fe25519_neg_add(out: *mut u8, a: *const u8, b: *const u8) {
    // Use sub: 0 - (a + b) is harder than computing -(a + b) directly
    // via `(0 - a) - b` (one extra carry).  Fiat exposes `fiat_25519_opp`
    // but we already have add+sub; simplest: compute s = a + b (loose →
    // carry → tight), then `0 - s`.  Implement `0 - s` by exploiting
    // sub's tight-tight signature with a zero tight element.
    let at = unsafe { read_tight_ptr(a) };
    let bt = unsafe { read_tight_ptr(b) };
    let mut sum_loose = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_add(&mut sum_loose, &at, &bt);
    let mut sum = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry(&mut sum, &sum_loose);

    let zero = fiat_25519_tight_field_element([0; 5]);
    let mut neg_loose = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_sub(&mut neg_loose, &zero, &sum);
    let mut r = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry(&mut r, &neg_loose);
    unsafe { write_tight_ptr(out, &r) };
}

// ---------------------------------------------------------------------------
// xyzt point pack / unpack / copy — pure byte moves.

/// Unpack a 200-byte xyzt point into 5 × 40-byte field elements
/// (X, Y, Z, Ta, Tb).  The body's packed layout is X || Y || Z || Ta || Tb.
///
/// Format-neutral: under canonical or limb 200-byte slot format,
/// the unpack is a 40-byte memcpy per coord — the slot layout's
/// 40-byte chunks just get distributed across 5 outputs.
#[cfg_attr(not(feature = "cryptopt_leaves"), unsafe(no_mangle))]
pub unsafe extern "C" fn fe25519_unpack_xyzt5(
    x: *mut u8,
    y: *mut u8,
    z: *mut u8,
    ta: *mut u8,
    tb: *mut u8,
    p: *const u8,
) {
    unsafe {
        core::ptr::copy_nonoverlapping(p, x, 40);
        core::ptr::copy_nonoverlapping(p.add(40), y, 40);
        core::ptr::copy_nonoverlapping(p.add(80), z, 40);
        core::ptr::copy_nonoverlapping(p.add(120), ta, 40);
        core::ptr::copy_nonoverlapping(p.add(160), tb, 40);
    }
}

/// Pack 5 × 40-byte field elements into a 200-byte xyzt point.
/// Format-neutral, like unpack.
#[cfg_attr(not(feature = "cryptopt_leaves"), unsafe(no_mangle))]
pub unsafe extern "C" fn fe25519_pack_xyzt5(
    out: *mut u8,
    x: *const u8,
    y: *const u8,
    z: *const u8,
    ta: *const u8,
    tb: *const u8,
) {
    unsafe {
        core::ptr::copy_nonoverlapping(x, out, 40);
        core::ptr::copy_nonoverlapping(y, out.add(40), 40);
        core::ptr::copy_nonoverlapping(z, out.add(80), 40);
        core::ptr::copy_nonoverlapping(ta, out.add(120), 40);
        core::ptr::copy_nonoverlapping(tb, out.add(160), 40);
    }
}

/// Copy a 200-byte xyzt slot.
///
/// Suppressed when `jasminc_leaves` is active: the linker picks up the
/// jasminc-emitted `fe25519_xyzt_copy` symbol from `ed25519_xyzt_copy.s`
/// instead.  This is the smallest representative slice of Option C
/// step (d) — the verified rust_cmd_ed -> Jasmin.expr.cmd ->
/// jasminc -> x86-64 pipeline.
#[cfg(not(feature = "jasminc_leaves"))]
#[cfg_attr(not(feature = "cryptopt_leaves"), unsafe(no_mangle))]
pub unsafe extern "C" fn fe25519_xyzt_copy(out: *mut u8, src: *const u8) {
    unsafe { core::ptr::copy_nonoverlapping(src, out, 200) };
}

// ---------------------------------------------------------------------------
// Field power chain — pow2k, pow22501, invert (used by compress).
// Translated directly from dalek's
// `curve25519-dalek/src/field.rs::FieldElement::{pow22501, invert}`
// (Apache-2.0 / MIT licensed), staying on fiat-rust's tight limb form.

fn fe_square(a: &fiat_25519_tight_field_element) -> fiat_25519_tight_field_element {
    let al = relax(a);
    let mut out = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry_square(&mut out, &al);
    out
}

fn fe_pow2k(a: &fiat_25519_tight_field_element, k: u32) -> fiat_25519_tight_field_element {
    let mut t = *a;
    for _ in 0..k {
        t = fe_square(&t);
    }
    t
}

fn fe_mul(
    a: &fiat_25519_tight_field_element,
    b: &fiat_25519_tight_field_element,
) -> fiat_25519_tight_field_element {
    let al = relax(a);
    let bl = relax(b);
    let mut out = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry_mul(&mut out, &al, &bl);
    out
}

/// (t19, t3) where t19 = self^(2^250 - 1), t3 = self^11.
/// See dalek's `FieldElement::pow22501`.
fn fe_pow22501(
    a: &fiat_25519_tight_field_element,
) -> (fiat_25519_tight_field_element, fiat_25519_tight_field_element) {
    let t0 = fe_square(a);
    let t1 = fe_pow2k(&t0, 2);
    let t2 = fe_mul(a, &t1);
    let t3 = fe_mul(&t0, &t2);
    let t4 = fe_square(&t3);
    let t5 = fe_mul(&t2, &t4);
    let t6 = fe_pow2k(&t5, 5);
    let t7 = fe_mul(&t6, &t5);
    let t8 = fe_pow2k(&t7, 10);
    let t9 = fe_mul(&t8, &t7);
    let t10 = fe_pow2k(&t9, 20);
    let t11 = fe_mul(&t10, &t9);
    let t12 = fe_pow2k(&t11, 10);
    let t13 = fe_mul(&t12, &t7);
    let t14 = fe_pow2k(&t13, 50);
    let t15 = fe_mul(&t14, &t13);
    let t16 = fe_pow2k(&t15, 100);
    let t17 = fe_mul(&t16, &t15);
    let t18 = fe_pow2k(&t17, 50);
    let t19 = fe_mul(&t18, &t13);
    (t19, t3)
}

/// `tight_from_int(z)` — set tight limbs from u64 (`z < 2^51`).
fn tight_from_u51(z: u64) -> fiat_25519_tight_field_element {
    fiat_25519_tight_field_element([z, 0, 0, 0, 0])
}

/// Compute Y_aff = Y * Z^-1 and X_aff = X * Z^-1, returning canonical
/// 32-byte compressed encoding (Y_aff with sign(X_aff) in bit 255).
///
/// Inputs are byte slots in the same 40-byte `le_split 40 z`
/// representation as the rest of this module.
pub(crate) fn compress_xyz(x_bytes: &[u8; 40], y_bytes: &[u8; 40], z_bytes: &[u8; 40]) -> [u8; 32] {
    let x = read_tight(x_bytes);
    let y = read_tight(y_bytes);
    let z = read_tight(z_bytes);

    // z_inv = z^(-1)
    let (t19, t3) = fe_pow22501(&z);
    let t20 = fe_pow2k(&t19, 5);
    let z_inv = fe_mul(&t20, &t3);

    let y_aff = fe_mul(&y, &z_inv);
    let x_aff = fe_mul(&x, &z_inv);

    let mut y_bytes_out = [0u8; 32];
    fiat_25519_to_bytes(&mut y_bytes_out, &y_aff);

    let mut x_bytes_out = [0u8; 32];
    fiat_25519_to_bytes(&mut x_bytes_out, &x_aff);

    // Set bit 255 of y_bytes_out = LSB of x_aff (the sign bit).
    let sign = x_bytes_out[0] & 1;
    y_bytes_out[31] |= sign << 7;

    y_bytes_out
}

// Edwards d_25519 = -121665 / 121666 mod p as tight limbs.
//
// d = 37095705934669439343138083508754565189542113879843219016388785533085940283555
// 51-bit limbs (verified by python: d >> (51*i) & ((1<<51)-1)).
const D_LIMBS: [u64; 5] = [
    929955233495203u64,  // 0x34dca135978a3
    466365720129213u64,  // 0x1a8283b156ebd
    1662059464998953u64, // 0x5e7a26001c029
    2033849074728123u64, // 0x739c663a03cbb
    1442794654840575u64, // 0x52036cee2b6ff
];

// sqrt(-1) mod p = 2^((p-1)/4) mod p.
//
// SQRT_M1 = 19681161376707505956807079304988542015446066515923890162744021073123829784752
// (verified: SQRT_M1^2 ≡ -1 mod p)
const SQRT_M1_LIMBS: [u64; 5] = [
    1718705420411056u64, // 0x61b274a0ea0b0
    234908883556509u64,  // 0x0d5a5fc8f189d
    2233514472574048u64, // 0x7ef5e9cbd0c60
    2117202627021982u64, // 0x78595a6804c9e
    765476049583133u64,  // 0x2b8324804fc1d
];

/// Decompress: parse 32-byte compressed encoding, recover (x_aff, y_aff).
/// Returns the 40-byte LE encodings (x_aff, y_aff) or `None` for invalid.
pub(crate) fn decompress(sig32: &[u8; 32]) -> Option<([u8; 40], [u8; 40])> {
    // y_bytes = bottom 255 bits of sig32 (clear bit 255).
    let mut y_bytes_in = [0u8; 32];
    y_bytes_in.copy_from_slice(sig32);
    let sign_bit = (y_bytes_in[31] >> 7) & 1;
    y_bytes_in[31] &= 0x7f;
    let y = {
        let mut t = fiat_25519_tight_field_element([0; 5]);
        fiat_25519_from_bytes(&mut t, &y_bytes_in);
        t
    };

    // u = y^2 - 1
    let y2 = fe_square(&y);
    let one = tight_from_u51(1);
    let u = {
        let mut diff = fiat_25519_loose_field_element([0; 5]);
        fiat_25519_sub(&mut diff, &y2, &one);
        let mut out = fiat_25519_tight_field_element([0; 5]);
        fiat_25519_carry(&mut out, &diff);
        out
    };

    // v = d * y^2 + 1
    let d = fiat_25519_tight_field_element(D_LIMBS);
    let dy2 = fe_mul(&d, &y2);
    let v = {
        let mut sum = fiat_25519_loose_field_element([0; 5]);
        fiat_25519_add(&mut sum, &dy2, &one);
        let mut out = fiat_25519_tight_field_element([0; 5]);
        fiat_25519_carry(&mut out, &sum);
        out
    };

    // Compute sqrt(u/v) using the ed25519 trick.
    //   β = (u·v) · (u·v^3) · ((u·v^7)^((p-5)/8))²   ... follows dalek's sqrt_ratio_i
    //
    // We just use: x = (u/v)^((p+3)/8) if u/v is a QR; else
    //              x = sqrt(-1) · (u/v)^((p+3)/8).
    //
    // Compute (u/v) = u * v^(-1).
    let v_inv = {
        let (t19, t3) = fe_pow22501(&v);
        let t20 = fe_pow2k(&t19, 5);
        fe_mul(&t20, &t3)
    };
    let u_div_v = fe_mul(&u, &v_inv);

    // Compute candidate x = (u/v)^((p+3)/8).
    //  (p+3)/8 = 2^252 - 2  i.e. nonzero bits 251..1.
    //  This is `pow22501.t19` (249..0) >> 2 ... easier to compute via
    //    chain: t19 = self^(2^250-1) gives bits 249..0.
    //    Then square twice -> bits 251..2.
    //    That equals self^(2^252 - 4) = self^((p-5)/8 - 1)... hmm.
    //
    // Cleaner: compute self^((p+3)/8) directly via:
    //   (p+3)/8 = (2^252 + 1) / ... wait let me think.
    //
    //   p = 2^255 - 19
    //   p + 3 = 2^255 - 16
    //   (p+3)/8 = 2^252 - 2
    //
    // Bits of 2^252 - 2: bits 1..251 are set, bit 0 is clear.  i.e.
    // bit positions 251, 250, ..., 1.
    //
    // From pow22501: t19 = self^(2^250 - 1)  (bits 249..0).
    //   self^(2^252 - 4) = (t19)^4 = self^(bits 251..2).
    //   Note: 2^252 - 4 = 2^252 - 4 ; bits 251..2.
    //   But we want 2^252 - 2 = bits 251..1.
    //   2^252 - 2 = (2^252 - 4) + 2 = bits 251..2 plus bit 1.
    //
    // Easier: from t19, we have bits 249..0.
    //   Goal: bits 251..1.
    //   Square t19 once: get bits 250..1.   = (t19)^2
    //   That's NOT 251..1; that's 250..1.
    //   Square again: bits 251..2.   = (t19)^4
    //   Multiply by self^2  (square of self once)  to add bit 1.
    //
    // (t19)^4 * self^2 = bits 251..2 + bit 1 = bits 251..1.  Done.
    let (t19, _) = fe_pow22501(&u_div_v);
    let t_squared_twice = fe_pow2k(&t19, 2); // bits 251..2
    let self_squared = fe_square(&u_div_v); // bit 1
    let beta = fe_mul(&t_squared_twice, &self_squared); // bits 251..1

    // Check whether beta^2 == u/v.  If yes, x = beta.
    // Else, x = beta · sqrt(-1).
    let beta_sq = fe_square(&beta);
    // Compare canonical encodings.
    let mut beta_sq_bytes = [0u8; 32];
    fiat_25519_to_bytes(&mut beta_sq_bytes, &beta_sq);
    let mut u_div_v_bytes = [0u8; 32];
    fiat_25519_to_bytes(&mut u_div_v_bytes, &u_div_v);
    let is_qr = beta_sq_bytes == u_div_v_bytes;

    let x_candidate = if is_qr {
        beta
    } else {
        // Check whether -beta^2 == u/v  (i.e. beta * sqrt(-1) is a sqrt).
        let sqrt_m1 = fiat_25519_tight_field_element(SQRT_M1_LIMBS);
        let x = fe_mul(&beta, &sqrt_m1);
        let x_sq = fe_square(&x);
        let mut x_sq_bytes = [0u8; 32];
        fiat_25519_to_bytes(&mut x_sq_bytes, &x_sq);
        if x_sq_bytes != u_div_v_bytes {
            return None; // not on curve
        }
        x
    };

    // Pick the sign of x matching `sign_bit`.
    let mut x_bytes_canon = [0u8; 32];
    fiat_25519_to_bytes(&mut x_bytes_canon, &x_candidate);
    let x_is_zero = x_bytes_canon == [0u8; 32];
    if x_is_zero && sign_bit == 1 {
        return None; // x=0 with sign_bit=1 is invalid
    }
    let x_lsb = x_bytes_canon[0] & 1;
    let x_final = if x_lsb == sign_bit {
        x_candidate
    } else {
        // negate
        let zero = tight_from_u51(0);
        let mut neg = fiat_25519_loose_field_element([0; 5]);
        fiat_25519_sub(&mut neg, &zero, &x_candidate);
        let mut out = fiat_25519_tight_field_element([0; 5]);
        fiat_25519_carry(&mut out, &neg);
        out
    };

    // Encode (x_final, y) as two 40-byte slots.
    let mut x_out = [0u8; 40];
    write_tight(&mut x_out, &x_final);
    let mut y_out = [0u8; 40];
    write_tight(&mut y_out, &y);
    Some((x_out, y_out))
}
