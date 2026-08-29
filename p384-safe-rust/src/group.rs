//! P-384 group operations — hand-written projective arithmetic over the
//! fiat-crypto field leaves in `lib.rs`.
//!
//! Point addition is a line-by-line transcription of the 40-field-op
//! Renes–Costello–Batina 2015 complete addition sequence (Algorithm 1,
//! general `a`) from the Qed-proved bedrock2 function body in
//! `src/Bedrock/Curve/P256_G1_Add_Spec.v` (`P256_G1_add`, steps 1–40).
//! The op sequence is curve-generic in `a` and `3b`; only the two curve
//! constants differ between P-256 and P-384.
//!
//! Coordinates are homogeneous projective (X : Y : Z), identity
//! (0 : 1 : 0).  All field elements are in Montgomery form (`Fp`).
//!
//! Curve constants (canonical, non-Montgomery limbs, little-endian u64):
//!   - `p` and the group order `N` from the fiat-crypto generation headers
//!     (`fiat-rust/src/p384_64.rs`, `fiat-rust/src/p384_scalar_64.rs`);
//!   - `a = -3 mod p`, `b`, `Gx`, `Gy` are the FIPS 186-4 / SEC2 v2
//!     secp384r1 values.  `b`, `Gx`, `Gy`, `N` are validated jointly by
//!     the tests (`g_on_curve`, `order_times_g_is_identity`).

use crate::{fp_add, fp_inv, fp_mul, fp_opp, fp_square, fp_sub, Fp};
#[cfg(test)]
use crate::{fp_to_montgomery, FpRaw};

// ---------------------------------------------------------------------------
// Curve constants (canonical limbs, little-endian u64)
// ---------------------------------------------------------------------------

/// a = -3 mod p  (p = 2^384 - 2^128 - 2^96 + 2^32 - 1).
pub const A_CANON: [u64; 6] = [
    0x0000_0000_ffff_fffc,
    0xffff_ffff_0000_0000,
    0xffff_ffff_ffff_fffe,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
];

/// b (FIPS 186-4 / SEC2 secp384r1).
pub const B_CANON: [u64; 6] = [
    0x2a85_c8ed_d3ec_2aef,
    0xc656_398d_8a2e_d19d,
    0x0314_088f_5013_875a,
    0x181d_9c6e_fe81_4112,
    0x988e_056b_e3f8_2d19,
    0xb331_2fa7_e23e_e7e4,
];

/// Base point x-coordinate Gx (FIPS 186-4 / SEC2 secp384r1).
pub const GX_CANON: [u64; 6] = [
    0x3a54_5e38_7276_0ab7,
    0x5502_f25d_bf55_296c,
    0x59f7_41e0_8254_2a38,
    0x6e1d_3b62_8ba7_9b98,
    0x8eb1_c71e_f320_ad74,
    0xaa87_ca22_be8b_0537,
];

/// Base point y-coordinate Gy (FIPS 186-4 / SEC2 secp384r1).
pub const GY_CANON: [u64; 6] = [
    0x7a43_1d7c_90ea_0e5f,
    0x0a60_b1ce_1d7e_819d,
    0xe9da_3113_b5f0_b8c0,
    0xf8f4_1dbd_289a_147c,
    0x5d9e_98bf_9292_dc29,
    0x3617_de4a_9626_2c6f,
];

/// Group order n (from `fiat-rust/src/p384_scalar_64.rs` header:
/// n = 2^384 - 1388124618062372383947042015309946732620727252194336364173).
pub const N_CANON: [u64; 6] = [
    0xecec_196a_ccc5_2973,
    0x581a_0db2_48b0_a77a,
    0xc763_4d81_f437_2ddf,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
];

// ---------------------------------------------------------------------------
// Field helpers
// ---------------------------------------------------------------------------

#[inline]
fn fp_zero() -> Fp {
    Fp([0u64; 6])
}

/// Montgomery encoding of 1 (i.e. R mod p).
#[inline]
fn fp_one() -> Fp {
    ONE_MONT
}

/// Runtime recomputation of [`ONE_MONT`], for the drift test.
#[cfg(test)]
fn fp_one_computed() -> Fp {
    let mut out = fp_zero();
    let mut raw = FpRaw([0u64; 6]);
    raw.0[0] = 1;
    fp_to_montgomery(&mut out, &raw);
    out
}

/// Montgomery encoding of a canonical limb value.  Only the drift tests
/// need it now that the curve constants are stored pre-encoded.
#[cfg(test)]
#[inline]
fn fp_from_canon(limbs: &[u64; 6]) -> Fp {
    let mut out = fp_zero();
    fp_to_montgomery(&mut out, &FpRaw(*limbs));
    out
}

// ---------------------------------------------------------------------------
// Precomputed Montgomery encodings
//
// `g1_add` used to recompute `a` and `3b` on every call (two
// `to_montgomery` conversions plus two adds per addition).  The
// Rocq-emitted body in `g1_extracted.rs` loads them from byte literals
// instead.  The constants below are those same values;
// `mont_constants_match_runtime` recomputes them at test time and
// `mont_constants_match_extracted_literals` compares them against the
// `cA` / `cB3` literals, so they cannot silently drift.
// ---------------------------------------------------------------------------

/// Montgomery encoding of 1 (R mod p).
pub const ONE_MONT: Fp = Fp([
    0xffffffff00000001,
    0x00000000ffffffff,
    0x0000000000000001,
    0x0000000000000000,
    0x0000000000000000,
    0x0000000000000000,
]);

/// Montgomery encoding of a = -3 mod p.
/// Equals the `cA` literal of `g1_extracted.rs` read as little-endian u64s.
pub const A_MONT: Fp = Fp([
    0x00000003fffffffc,
    0xfffffffc00000000,
    0xfffffffffffffffb,
    0xffffffffffffffff,
    0xffffffffffffffff,
    0xffffffffffffffff,
]);

/// Montgomery encoding of b.
pub const B_MONT: Fp = Fp([
    0x081188719d412dcc,
    0xf729add87a4c32ec,
    0x77f2209b1920022e,
    0xe3374bee94938ae2,
    0xb62b21f41f022094,
    0xcd08114b604fbff9,
]);

/// Montgomery encoding of 3b.
/// Equals the `cB3` literal of `g1_extracted.rs` read as little-endian u64s.
pub const THREE_B_MONT: Fp = Fp([
    0x18349952d7c38966,
    0xe57d098b6ee498c4,
    0x67d661d14b60068e,
    0xa9a5e3cbbdbaa0a7,
    0x228165dc5d0661be,
    0x671833e220ef3fed,
]);

/// Montgomery encoding of the base-point x-coordinate.
pub const GX_MONT: Fp = Fp([
    0x3dd0756649c0b528,
    0x20e378e2a0d6ce38,
    0x879c3afc541b4d6e,
    0x6454868459a30eff,
    0x812ff723614ede2b,
    0x4d3aadc2299e1513,
]);

/// Montgomery encoding of the base-point y-coordinate.
pub const GY_MONT: Fp = Fp([
    0x23043dad4b03a4fe,
    0xa1bfa8bf7bb4a9ac,
    0x8bade7562e83b050,
    0xc6c3521968f4ffd9,
    0xdd8002263969a840,
    0x2b78abc25a15c5e9,
]);

/// a in Montgomery form.
#[inline]
pub fn a_mont() -> Fp {
    A_MONT
}

/// b in Montgomery form.
#[inline]
pub fn b_mont() -> Fp {
    B_MONT
}

/// 3*b mod p in Montgomery form.
#[inline]
pub fn three_b_mont() -> Fp {
    THREE_B_MONT
}

/// Runtime recomputation of [`THREE_B_MONT`] as b + b + b, for the drift test.
#[cfg(test)]
fn three_b_mont_computed() -> Fp {
    let b = fp_from_canon(&B_CANON);
    let mut t = fp_zero();
    fp_add(&mut t, &b, &b);
    let mut out = fp_zero();
    fp_add(&mut out, &t, &b);
    out
}

/// Field-element equality.  fiat-crypto's Montgomery-domain values are kept
/// in the unique saturated representation < p, so limb equality is field
/// equality.  (Used in tests and non-secret checks only — not constant-time.)
#[inline]
fn fp_eq(x: &Fp, y: &Fp) -> bool {
    x.0 == y.0
}

#[inline]
fn fp_is_zero(x: &Fp) -> bool {
    x.0 == [0u64; 6]
}

// ---------------------------------------------------------------------------
// Point type
// ---------------------------------------------------------------------------

/// A P-384 point in homogeneous projective coordinates (X : Y : Z).
/// The identity is (0 : 1 : 0).
#[derive(Clone, Copy)]
pub struct G1 {
    pub x: Fp,
    pub y: Fp,
    pub z: Fp,
}

/// The identity element (0 : 1 : 0).
pub fn g1_identity() -> G1 {
    G1 {
        x: fp_zero(),
        y: fp_one(),
        z: fp_zero(),
    }
}

/// The standard base point G, in projective coordinates (Gx : Gy : 1).
pub fn g1_generator() -> G1 {
    G1 {
        x: GX_MONT,
        y: GY_MONT,
        z: ONE_MONT,
    }
}

/// Whether P is the identity (Z = 0).  Not constant-time.
pub fn g1_is_identity(p: &G1) -> bool {
    fp_is_zero(&p.z)
}

/// Point negation: (X : -Y : Z).
pub fn g1_neg(p: &G1) -> G1 {
    let mut ny = fp_zero();
    fp_opp(&mut ny, &p.y);
    G1 { x: p.x, y: ny, z: p.z }
}

/// Affine (x, y) → projective (x : y : 1).
pub fn g1_from_affine(x: &Fp, y: &Fp) -> G1 {
    G1 { x: *x, y: *y, z: fp_one() }
}

/// Projective → affine via Z inversion.  Returns None for the identity.
/// Not constant-time (branches on Z = 0; fp_inv itself is constant-time).
pub fn g1_to_affine(p: &G1) -> Option<(Fp, Fp)> {
    if fp_is_zero(&p.z) {
        return None;
    }
    let mut zinv = fp_zero();
    fp_inv(&mut zinv, &p.z);
    let mut ax = fp_zero();
    let mut ay = fp_zero();
    fp_mul(&mut ax, &p.x, &zinv);
    fp_mul(&mut ay, &p.y, &zinv);
    Some((ax, ay))
}

/// Affine on-curve check: y^2 = x^3 + a*x + b (all in Montgomery form).
pub fn g1_is_on_curve_affine(x: &Fp, y: &Fp) -> bool {
    let mut lhs = fp_zero();
    fp_square(&mut lhs, y);
    let mut x2 = fp_zero();
    fp_square(&mut x2, x);
    let mut x3 = fp_zero();
    fp_mul(&mut x3, &x2, x);
    let mut ax = fp_zero();
    fp_mul(&mut ax, &a_mont(), x);
    let mut rhs = fp_zero();
    fp_add(&mut rhs, &x3, &ax);
    let mut rhs2 = fp_zero();
    fp_add(&mut rhs2, &rhs, &b_mont());
    fp_eq(&lhs, &rhs2)
}

// ---------------------------------------------------------------------------
// Complete addition (Renes–Costello–Batina 2015, Algorithm 1, general a)
// ---------------------------------------------------------------------------

/// Complete projective point addition.
///
/// Transcribed op-for-op from the Qed-proved bedrock2 body of
/// `P256_G1_add` in `src/Bedrock/Curve/P256_G1_Add_Spec.v` (steps 1–40 of
/// the RCB 2015 Algorithm 1 for general `a`); the sequence is
/// curve-generic, with the P-384 constants `a = -3 mod p` and `3b`
/// substituted.  Because the formula is complete, `g1_add(p, p)` computes
/// the doubling and addition with the identity is correct.
///
/// Straight-line code over constant-time fiat field ops: no
/// secret-dependent branches or memory accesses.
pub fn g1_add(p: &G1, q: &G1) -> G1 {

    let (x1, y1, z1) = (&p.x, &p.y, &p.z);
    let (x2, y2, z2) = (&q.x, &q.y, &q.z);

    let mut t0 = fp_zero();
    let mut t1 = fp_zero();
    let mut t2 = fp_zero();
    let mut t3 = fp_zero();
    let mut t4 = fp_zero();
    let mut t5 = fp_zero();
    let mut x3 = fp_zero();
    let mut y3 = fp_zero();
    let mut z3 = fp_zero();
    let mut tmp = fp_zero();

    // Steps 1-18 (same as the a=0 case)
    fp_mul(&mut t0, x1, x2);            //  1: t0 := X1 * X2
    fp_mul(&mut t1, y1, y2);            //  2: t1 := Y1 * Y2
    fp_mul(&mut t2, z1, z2);            //  3: t2 := Z1 * Z2
    fp_add(&mut t3, x1, y1);            //  4: t3 := X1 + Y1
    fp_add(&mut t4, x2, y2);            //  5: t4 := X2 + Y2
    fp_mul(&mut tmp, &t3, &t4);         //  6: t3 := t3 * t4
    t3 = tmp;
    fp_add(&mut t4, &t0, &t1);          //  7: t4 := t0 + t1
    fp_sub(&mut tmp, &t3, &t4);         //  8: t3 := t3 - t4
    t3 = tmp;
    fp_add(&mut t4, x1, z1);            //  9: t4 := X1 + Z1
    fp_add(&mut t5, x2, z2);            // 10: t5 := X2 + Z2
    fp_mul(&mut tmp, &t4, &t5);         // 11: t4 := t4 * t5
    t4 = tmp;
    fp_add(&mut t5, &t0, &t2);          // 12: t5 := t0 + t2
    fp_sub(&mut tmp, &t4, &t5);         // 13: t4 := t4 - t5
    t4 = tmp;
    fp_add(&mut t5, y1, z1);            // 14: t5 := Y1 + Z1
    fp_add(&mut x3, y2, z2);            // 15: X3 := Y2 + Z2
    fp_mul(&mut tmp, &t5, &x3);         // 16: t5 := t5 * X3
    t5 = tmp;
    fp_add(&mut x3, &t1, &t2);          // 17: X3 := t1 + t2
    fp_sub(&mut tmp, &t5, &x3);         // 18: t5 := t5 - X3
    t5 = tmp;
    // Step 19: Z3 := a * t4
    fp_mul(&mut z3, &A_MONT, &t4);
    // Step 20: X3 := 3b * t2
    fp_mul(&mut x3, &THREE_B_MONT, &t2);
    // Step 21: Z3 := X3 + Z3
    fp_add(&mut tmp, &x3, &z3);
    z3 = tmp;
    // Step 22: X3 := t1 - Z3
    fp_sub(&mut x3, &t1, &z3);
    // Step 23: Z3 := Z3 + t1  (var order as in the spec: outz := outz + t1)
    fp_add(&mut tmp, &z3, &t1);
    z3 = tmp;
    // Step 24: Y3 := X3 * Z3
    fp_mul(&mut y3, &x3, &z3);
    // Steps 25-26: t1 := 3 * t0
    fp_add(&mut t1, &t0, &t0);
    fp_add(&mut tmp, &t1, &t0);
    t1 = tmp;
    // Step 27: t2 := a * t2
    fp_mul(&mut tmp, &A_MONT, &t2);
    t2 = tmp;
    // Step 28: t4 := 3b * t4
    fp_mul(&mut tmp, &THREE_B_MONT, &t4);
    t4 = tmp;
    // Step 29: t1 := t1 + t2
    fp_add(&mut tmp, &t1, &t2);
    t1 = tmp;
    // Step 30: t2 := t0 - t2
    fp_sub(&mut tmp, &t0, &t2);
    t2 = tmp;
    // Step 31: t2 := a * t2
    fp_mul(&mut tmp, &A_MONT, &t2);
    t2 = tmp;
    // Step 32: t4 := t4 + t2
    fp_add(&mut tmp, &t4, &t2);
    t4 = tmp;
    // Steps 33-40: final accumulation
    fp_mul(&mut t0, &t1, &t4);          // 33: t0 := t1 * t4
    fp_add(&mut tmp, &y3, &t0);         // 34: Y3 := Y3 + t0
    y3 = tmp;
    fp_mul(&mut t0, &t5, &t4);          // 35: t0 := t5 * t4
    fp_mul(&mut tmp, &t3, &x3);         // 36: X3 := t3 * X3
    x3 = tmp;
    fp_sub(&mut tmp, &x3, &t0);         // 37: X3 := X3 - t0
    x3 = tmp;
    fp_mul(&mut t0, &t3, &t1);          // 38: t0 := t3 * t1
    fp_mul(&mut tmp, &t5, &z3);         // 39: Z3 := t5 * Z3
    z3 = tmp;
    fp_add(&mut tmp, &z3, &t0);         // 40: Z3 := Z3 + t0
    z3 = tmp;

    G1 { x: x3, y: y3, z: z3 }
}

/// Point doubling via the complete addition formula.
pub fn g1_double(p: &G1) -> G1 {
    g1_add(p, p)
}

// ---------------------------------------------------------------------------
// Constant-time scalar multiplication
// ---------------------------------------------------------------------------

/// Constant-time conditional select on limb arrays:
/// returns `a` if bit = 0, `b` if bit = 1.  `bit` must be 0 or 1.
#[inline]
fn ct_select_limbs(a: &[u64; 6], b: &[u64; 6], bit: u64) -> [u64; 6] {
    ct_select_limbs_mask(a, b, 0u64.wrapping_sub(bit)) // 0x00..0 or 0xff..f
}

/// Constant-time conditional select on a full mask: returns `a` if
/// `mask == 0`, `b` if `mask == u64::MAX`.
#[inline]
fn ct_select_limbs_mask(a: &[u64; 6], b: &[u64; 6], mask: u64) -> [u64; 6] {
    let mut out = [0u64; 6];
    let mut i = 0;
    while i < 6 {
        out[i] = a[i] ^ (mask & (a[i] ^ b[i]));
        i += 1;
    }
    out
}

#[inline]
fn ct_select_point(a: &G1, b: &G1, bit: u64) -> G1 {
    G1 {
        x: Fp(ct_select_limbs(&a.x.0, &b.x.0, bit)),
        y: Fp(ct_select_limbs(&a.y.0, &b.y.0, bit)),
        z: Fp(ct_select_limbs(&a.z.0, &b.z.0, bit)),
    }
}

/// Constant-time scalar multiplication: `k * p`.
///
/// Scalar input: `k` as 6 little-endian u64 limbs (k = sum k[i] * 2^(64 i)),
/// interpreted as an integer in [0, 2^384).  No reduction mod n is
/// performed; callers pass scalars already below the group order.
///
/// Fixed-length MSB-first double-and-add over all 384 bits: every
/// iteration performs one complete doubling, one complete addition, and a
/// limb-masked conditional select — no secret-dependent branches or
/// memory access patterns.
pub fn g1_scalar_mul(k: &[u64; 6], p: &G1) -> G1 {
    let mut acc = g1_identity();
    let mut i: i32 = 383;
    while i >= 0 {
        acc = g1_add(&acc, &acc);
        let with_p = g1_add(&acc, p);
        let bit = (k[(i as usize) / 64] >> ((i as usize) % 64)) & 1;
        acc = ct_select_point(&acc, &with_p, bit);
        i -= 1;
    }
    acc
}

// ---------------------------------------------------------------------------
// Fixed-base scalar multiplication (precomputed table for G)
// ---------------------------------------------------------------------------

mod g_table;

/// Window width of the fixed-base table, in bits.
///
/// Chosen by measurement: the per-window table scan is cheap next to the
/// one complete addition per window, so the cost is dominated by
/// `ceil(384/W)` additions; W=5 is the knee of the speed/size curve
/// (see the P-256 crate's `BASE_W` note for the W=4/5/6 numbers).
pub const BASE_W: usize = 5;

/// Number of windows, `ceil(384 / BASE_W)`.
pub const BASE_WINDOWS: usize = (384 + BASE_W - 1) / BASE_W;

/// Non-zero digits per window, `2^BASE_W - 1`.
pub const BASE_TSIZE: usize = (1 << BASE_W) - 1;

/// Size of the precomputed table in bytes
/// (`BASE_WINDOWS * BASE_TSIZE` affine points, 2 x 48 bytes each).
pub const BASE_TABLE_BYTES: usize = BASE_WINDOWS * BASE_TSIZE * 2 * 48;

/// Constant-time equality mask: `u64::MAX` when `a == b`, else 0.
#[inline]
fn ct_eq_mask(a: u64, b: u64) -> u64 {
    let d = a ^ b;
    let nonzero = (d | d.wrapping_neg()) >> 63;
    nonzero.wrapping_sub(1)
}

/// The `i`-th `BASE_W`-bit digit of the scalar, LSB-first window order.
/// `i` is a loop counter, never secret.
#[inline]
fn base_digit(k: &[u64; 6], i: usize) -> u64 {
    let mut d = 0u64;
    let mut b = 0;
    while b < BASE_W {
        let idx = i * BASE_W + b;
        if idx < 384 {
            d |= ((k[idx / 64] >> (idx % 64)) & 1) << b;
        }
        b += 1;
    }
    d
}

/// Constant-time fixed-base scalar multiplication: `k * G`.
///
/// `k` is 6 little-endian u64 limbs, an integer in `[0, 2^384)` with no
/// reduction mod n — the same convention as [`g1_scalar_mul`].
///
/// The scalar is split into [`BASE_WINDOWS`] digits of [`BASE_W`] bits.
/// Digit `d` of window `i` selects `d * 2^(BASE_W*i) * G` from the
/// precomputed table `g_table::G_TABLE`, so there are no doublings — one
/// complete addition per window instead of the ladder's 768.
///
/// Constant-time: the lookup is a full linear scan of all [`BASE_TSIZE`]
/// entries of the window with a limb-mask select ([`ct_eq_mask`] /
/// [`ct_select_limbs_mask`]), so the addresses touched and the instruction
/// trace depend only on the public `BASE_W` / `BASE_WINDOWS`.  `d = 0`
/// leaves the identity in `sel`, which the complete formula handles with
/// no special case.
pub fn g1_scalar_mul_base(k: &[u64; 6]) -> G1 {
    let mut acc = g1_identity();
    let mut i = 0;
    while i < BASE_WINDOWS {
        let digit = base_digit(k, i);
        let mut sx = [0u64; 6];
        let mut sy = ONE_MONT.0;
        let mut sz = [0u64; 6];
        let mut j = 1usize;
        while j <= BASE_TSIZE {
            let e = &g_table::G_TABLE[i * BASE_TSIZE + (j - 1)];
            let m = ct_eq_mask(digit, j as u64);
            sx = ct_select_limbs_mask(&sx, &e[0], m);
            sy = ct_select_limbs_mask(&sy, &e[1], m);
            sz = ct_select_limbs_mask(&sz, &ONE_MONT.0, m);
            j += 1;
        }
        let sel = G1 { x: Fp(sx), y: Fp(sy), z: Fp(sz) };
        // `i` is public, so this branch leaks nothing; it saves one add.
        acc = if i == 0 { sel } else { g1_add(&acc, &sel) };
        i += 1;
    }
    acc
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Projective equality: (X1:Y1:Z1) == (X2:Y2:Z2) iff both identity, or
    /// neither identity and X1*Z2 = X2*Z1 and Y1*Z2 = Y2*Z1.
    fn pt_eq(p: &G1, q: &G1) -> bool {
        let pi = g1_is_identity(p);
        let qi = g1_is_identity(q);
        if pi || qi {
            return pi == qi;
        }
        let mut l = fp_zero();
        let mut r = fp_zero();
        fp_mul(&mut l, &p.x, &q.z);
        fp_mul(&mut r, &q.x, &p.z);
        if !fp_eq(&l, &r) {
            return false;
        }
        fp_mul(&mut l, &p.y, &q.z);
        fp_mul(&mut r, &q.y, &p.z);
        fp_eq(&l, &r)
    }

    fn small_scalar(v: u64) -> [u64; 6] {
        let mut k = [0u64; 6];
        k[0] = v;
        k
    }

    /// Checked 384-bit big-int addition (little-endian limbs).
    /// Panics on overflow past 2^384.
    fn add_384(a: &[u64; 6], b: &[u64; 6]) -> [u64; 6] {
        let mut out = [0u64; 6];
        let mut carry = 0u64;
        for i in 0..6 {
            let (s1, c1) = a[i].overflowing_add(b[i]);
            let (s2, c2) = s1.overflowing_add(carry);
            out[i] = s2;
            carry = (c1 as u64) + (c2 as u64);
        }
        assert_eq!(carry, 0, "384-bit addition overflowed");
        out
    }

    /// Little-endian limb comparison: a < b.
    fn lt_384(a: &[u64; 6], b: &[u64; 6]) -> bool {
        for i in (0..6).rev() {
            if a[i] != b[i] {
                return a[i] < b[i];
            }
        }
        false
    }

    /// The hoisted Montgomery constants must equal the runtime computation
    /// they replaced, so they cannot silently drift.
    #[test]
    fn mont_constants_match_runtime() {
        assert!(fp_eq(&ONE_MONT, &fp_one_computed()), "ONE_MONT");
        assert!(fp_eq(&A_MONT, &fp_from_canon(&A_CANON)), "A_MONT");
        assert!(fp_eq(&B_MONT, &fp_from_canon(&B_CANON)), "B_MONT");
        assert!(fp_eq(&THREE_B_MONT, &three_b_mont_computed()), "THREE_B_MONT");
        assert!(fp_eq(&GX_MONT, &fp_from_canon(&GX_CANON)), "GX_MONT");
        assert!(fp_eq(&GY_MONT, &fp_from_canon(&GY_CANON)), "GY_MONT");
    }

    /// `A_MONT` / `THREE_B_MONT` must equal the `cA` / `cB3` byte literals of
    /// the Rocq-emitted `g1_extracted.rs`, read little-endian.
    #[test]
    fn mont_constants_match_extracted_literals() {
        let ca: [u8; 48] = [
            252, 255, 255, 255, 3, 0, 0, 0, 0, 0, 0, 0, 252, 255, 255, 255, 251, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        ];
        let cb3: [u8; 48] = [
            102, 137, 195, 215, 82, 153, 52, 24, 196, 152, 228, 110, 139, 9, 125, 229, 142, 6, 96,
            75, 209, 97, 214, 103, 167, 160, 186, 189, 203, 227, 165, 169, 190, 97, 6, 93, 220,
            101, 129, 34, 237, 63, 239, 32, 226, 51, 24, 103,
        ];
        let le = |bs: &[u8; 48]| {
            let mut o = [0u64; 6];
            for (i, w) in o.iter_mut().enumerate() {
                *w = u64::from_le_bytes(bs[8 * i..8 * i + 8].try_into().unwrap());
            }
            o
        };
        assert_eq!(A_MONT.0, le(&ca), "A_MONT vs g1_extracted cA");
        assert_eq!(THREE_B_MONT.0, le(&cb3), "THREE_B_MONT vs g1_extracted cB3");
    }

    /// Every entry of the fixed-base table must equal the corresponding
    /// multiple of G obtained by repeated `g1_add` from the generator.
    #[test]
    fn base_table_entries_match_repeated_addition() {
        assert_eq!(g_table::G_TABLE.len(), BASE_WINDOWS * BASE_TSIZE);
        let mut base = g1_generator(); // 2^(BASE_W*i) * G
        for i in 0..BASE_WINDOWS {
            let mut acc = base; // j * 2^(BASE_W*i) * G
            for j in 1..=BASE_TSIZE {
                let e = &g_table::G_TABLE[i * BASE_TSIZE + (j - 1)];
                let want = G1 { x: Fp(e[0]), y: Fp(e[1]), z: ONE_MONT };
                assert!(
                    pt_eq(&want, &acc),
                    "G_TABLE[{i}][{j}] != {j} * 2^({BASE_W}*{i}) * G"
                );
                assert!(
                    g1_is_on_curve_affine(&Fp(e[0]), &Fp(e[1])),
                    "G_TABLE[{i}][{j}] is not on the curve"
                );
                acc = g1_add(&acc, &base);
            }
            for _ in 0..BASE_W {
                base = g1_double(&base);
            }
        }
    }

    #[test]
    fn base_mul_matches_ladder() {
        let g = g1_generator();
        for v in [0u64, 1, 2, 3, 31, 32, 33, 1023, 1024, u64::MAX] {
            let k = small_scalar(v);
            assert!(
                pt_eq(&g1_scalar_mul_base(&k), &g1_scalar_mul(&k, &g)),
                "g1_scalar_mul_base disagrees with the ladder at k = {v}"
            );
        }
        assert!(g1_is_identity(&g1_scalar_mul_base(&N_CANON)), "n * G != O");
    }

    #[test]
    fn base_mul_matches_ladder_on_large_scalars() {
        let mut state: u64 = 0x9e37_79b9_7f4a_7c15;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let g = g1_generator();
        for _ in 0..4 {
            let mut k = [0u64; 6];
            for w in k.iter_mut() {
                *w = next();
            }
            assert!(
                pt_eq(&g1_scalar_mul_base(&k), &g1_scalar_mul(&k, &g)),
                "g1_scalar_mul_base disagrees with the ladder"
            );
        }
    }

    #[test]
    fn g_on_curve() {
        // Validates b, Gx, Gy jointly.
        let gx = fp_from_canon(&GX_CANON);
        let gy = fp_from_canon(&GY_CANON);
        assert!(g1_is_on_curve_affine(&gx, &gy));
    }

    #[test]
    fn generator_affine_roundtrip() {
        let g = g1_generator();
        let (ax, ay) = g1_to_affine(&g).expect("G is not the identity");
        assert!(fp_eq(&ax, &fp_from_canon(&GX_CANON)));
        assert!(fp_eq(&ay, &fp_from_canon(&GY_CANON)));
        assert!(g1_is_on_curve_affine(&ax, &ay));
    }

    #[test]
    fn order_times_g_is_identity() {
        // Validates n and the group arithmetic jointly.
        let g = g1_generator();
        let ng = g1_scalar_mul(&N_CANON, &g);
        assert!(g1_is_identity(&ng), "n * G is not the identity");
    }

    #[test]
    fn double_matches_scalar_two() {
        let g = g1_generator();
        let d = g1_add(&g, &g);
        let two_g = g1_scalar_mul(&small_scalar(2), &g);
        assert!(pt_eq(&d, &two_g));
        // The result of doubling stays on the curve.
        let (ax, ay) = g1_to_affine(&d).unwrap();
        assert!(g1_is_on_curve_affine(&ax, &ay));
    }

    #[test]
    fn scalar_distributivity_small() {
        // (3 + 5) * G = 3*G + 5*G
        let g = g1_generator();
        let three_g = g1_scalar_mul(&small_scalar(3), &g);
        let five_g = g1_scalar_mul(&small_scalar(5), &g);
        let eight_g = g1_scalar_mul(&small_scalar(8), &g);
        assert!(pt_eq(&g1_add(&three_g, &five_g), &eight_g));

        // (1 + 1) * G = G + G
        let two_g = g1_scalar_mul(&small_scalar(2), &g);
        assert!(pt_eq(&g1_add(&g, &g), &two_g));

        // (7 + 11) * G = 7*G + 11*G
        let seven_g = g1_scalar_mul(&small_scalar(7), &g);
        let eleven_g = g1_scalar_mul(&small_scalar(11), &g);
        let eighteen_g = g1_scalar_mul(&small_scalar(18), &g);
        assert!(pt_eq(&g1_add(&seven_g, &eleven_g), &eighteen_g));
    }

    #[test]
    fn scalar_distributivity_large() {
        // Two fixed 384-bit scalars with k1, k2 < 2^382, so k1 + k2 < 2^383 < n:
        // no reduction mod n occurs, and the sum is a checked big-int addition.
        let k1: [u64; 6] = [
            0xace1_3579_bdf0_2468,
            0xace1_3579_bdf0_2468,
            0xace1_3579_bdf0_2468,
            0xace1_3579_bdf0_2468,
            0xace1_3579_bdf0_2468,
            0x1f3a_5c7e_9bd0_2468,
        ];
        let k2: [u64; 6] = [
            0x2468_ace1_3579_bdf0,
            0x2468_ace1_3579_bdf0,
            0x2468_ace1_3579_bdf0,
            0x2468_ace1_3579_bdf0,
            0x2468_ace1_3579_bdf0,
            0x2468_ace1_3579_bdf0,
        ];
        let sum = add_384(&k1, &k2);
        assert!(lt_384(&sum, &N_CANON), "k1 + k2 must stay below n");
        let g = g1_generator();
        let lhs = g1_add(&g1_scalar_mul(&k1, &g), &g1_scalar_mul(&k2, &g));
        let rhs = g1_scalar_mul(&sum, &g);
        assert!(pt_eq(&lhs, &rhs));
    }

    #[test]
    fn add_commutative_and_associative() {
        let g = g1_generator();
        let p2 = g1_scalar_mul(&small_scalar(2), &g);
        let p3 = g1_scalar_mul(&small_scalar(3), &g);
        let p5 = g1_scalar_mul(&small_scalar(5), &g);
        // Commutativity
        assert!(pt_eq(&g1_add(&p2, &p3), &g1_add(&p3, &p2)));
        assert!(pt_eq(&g1_add(&p2, &p5), &g1_add(&p5, &p2)));
        // Associativity: (P2 + P3) + P5 = P2 + (P3 + P5)
        let lhs = g1_add(&g1_add(&p2, &p3), &p5);
        let rhs = g1_add(&p2, &g1_add(&p3, &p5));
        assert!(pt_eq(&lhs, &rhs));
    }

    #[test]
    fn identity_laws() {
        let g = g1_generator();
        let o = g1_identity();
        // P + O = P
        assert!(pt_eq(&g1_add(&g, &o), &g));
        // O + P = P
        assert!(pt_eq(&g1_add(&o, &g), &g));
        // P + (-P) = O
        let neg_g = g1_neg(&g);
        assert!(g1_is_identity(&g1_add(&g, &neg_g)));
        // O + O = O
        assert!(g1_is_identity(&g1_add(&o, &o)));
        // -O = O (negation fixes the identity)
        assert!(g1_is_identity(&g1_neg(&o)));
        // 0 * G = O
        assert!(g1_is_identity(&g1_scalar_mul(&small_scalar(0), &g)));
        // 1 * G = G
        assert!(pt_eq(&g1_scalar_mul(&small_scalar(1), &g), &g));
    }

    #[test]
    fn neg_is_on_curve() {
        let g = g1_generator();
        let neg_g = g1_neg(&g);
        let (ax, ay) = g1_to_affine(&neg_g).unwrap();
        assert!(g1_is_on_curve_affine(&ax, &ay));
    }
}
