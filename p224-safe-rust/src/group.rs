//! P-224 elliptic-curve group operations — hand-written over the fiat
//! field leaves in `lib.rs`.
//!
//! Curve: short Weierstrass y^2 = x^3 + a*x + b over GF(p),
//! p = 2^224 - 2^96 + 1, a = -3 mod p (FIPS 186-4 / SEC2 P-224).
//!
//! Points use homogeneous projective coordinates (X : Y : Z) with the
//! identity at (0 : 1 : 0).  Addition is the Renes–Costello–Batina 2015
//! complete addition formula for general a (Algorithm 1, 40 field
//! operations).  The operation sequence is transcribed verbatim from the
//! bedrock2 function body in
//! `src/Bedrock/Curve/P256_G1_Add_Spec.v` (`P256_G1_add`), whose WP
//! correctness proof (`P256_G1_add_func_ok`) is Qed for P-256; the
//! sequence itself is curve-generic in `a` and `3b`.
//!
//! Because the formula is complete, `g1_add(P, P)` computes 2P and
//! addition with the identity is correct, so doubling is implemented as
//! self-addition and scalar multiplication needs no special cases.

use crate::{
    fp_add, fp_inv, fp_from_montgomery, fp_mul, fp_opp, fp_square, fp_sub,
    fp_to_montgomery, Fp, FpRaw,
};

// ---------------------------------------------------------------------------
// Curve constants (canonical, non-Montgomery, 4 x u64 little-endian limbs).
//
// Sources: p = 2^224 - 2^96 + 1 is documented in
// `fiat-crypto/fiat-rust/src/p224_64.rs`; a = p - 3, b, G = (Gx, Gy) and the
// group order n are the FIPS 186-4 / SEC2 P-224 values (there is no
// fiat-crypto p224 scalar-field file).  The tests below validate them
// jointly: `generator_is_on_curve` ties (b, Gx, Gy) together and
// `order_times_generator_is_identity` ties n to the curve.
// ---------------------------------------------------------------------------

/// a = -3 mod p.
pub const P224_A: [u64; 4] = [
    0xfffffffffffffffe,
    0xfffffffeffffffff,
    0xffffffffffffffff,
    0x00000000ffffffff,
];

/// b = 0xb4050a850c04b3abf54132565044b0b7d7bfd8ba270b39432355ffb4.
pub const P224_B: [u64; 4] = [
    0x270b39432355ffb4,
    0x5044b0b7d7bfd8ba,
    0x0c04b3abf5413256,
    0x00000000b4050a85,
];

/// Base-point x-coordinate Gx (FIPS 186-4).
pub const P224_GX: [u64; 4] = [
    0x343280d6115c1d21,
    0x4a03c1d356c21122,
    0x6bb4bf7f321390b9,
    0x00000000b70e0cbd,
];

/// Base-point y-coordinate Gy (FIPS 186-4).
pub const P224_GY: [u64; 4] = [
    0x44d5819985007e34,
    0xcd4375a05a074764,
    0xb5f723fb4c22dfe6,
    0x00000000bd376388,
];

/// Group order n = 0xffffffffffffffffffffffffffff16a2e0b8f03e13dd29455c5c2a3d.
/// The cofactor is 1.
pub const P224_N: [u64; 4] = [
    0x13dd29455c5c2a3d,
    0xffff16a2e0b8f03e,
    0xffffffffffffffff,
    0x00000000ffffffff,
];

// ---------------------------------------------------------------------------
// Field helpers (by-value wrappers over the in/out leaf API).
// ---------------------------------------------------------------------------

#[inline]
fn fp_zero() -> Fp {
    Fp([0u64; 4])
}

#[inline]
fn mont(limbs: [u64; 4]) -> Fp {
    let mut out = fp_zero();
    fp_to_montgomery(&mut out, &FpRaw(limbs));
    out
}

#[inline]
fn mul(x: &Fp, y: &Fp) -> Fp {
    let mut out = fp_zero();
    fp_mul(&mut out, x, y);
    out
}

#[inline]
fn add(x: &Fp, y: &Fp) -> Fp {
    let mut out = fp_zero();
    fp_add(&mut out, x, y);
    out
}

#[inline]
fn sub(x: &Fp, y: &Fp) -> Fp {
    let mut out = fp_zero();
    fp_sub(&mut out, x, y);
    out
}

#[inline]
fn square(x: &Fp) -> Fp {
    let mut out = fp_zero();
    fp_square(&mut out, x);
    out
}

/// Limb equality.  fiat word-by-word Montgomery outputs are fully reduced,
/// so canonical limb comparison decides field equality.  Not constant-time;
/// used only on public data (tests, conversions).
#[inline]
fn fp_eq(x: &Fp, y: &Fp) -> bool {
    x.0 == y.0
}

#[inline]
fn fp_is_zero(x: &Fp) -> bool {
    x.0 == [0u64; 4]
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
    0xffffffff00000000,
    0xffffffffffffffff,
    0x0000000000000000,
    0x0000000000000000,
]);

/// Montgomery encoding of a = -3 mod p.
/// Equals the `cA` literal of `g1_extracted.rs` read as little-endian u64s.
pub const A_MONT: Fp = Fp([
    0x0000000300000001,
    0xffffffff00000000,
    0xfffffffffffffffc,
    0x00000000ffffffff,
]);

/// Montgomery encoding of b.
pub const B_MONT: Fp = Fp([
    0xe768cdf663c059cd,
    0x107ac2f3ccf01310,
    0x3dceba98c8528151,
    0x000000007fc02f93,
]);

/// Montgomery encoding of 3b.
/// Equals the `cB3` literal of `g1_extracted.rs` read as little-endian u64s.
pub const THREE_B_MONT: Fp = Fp([
    0xb63a69e32b410d66,
    0x317048dc66d03932,
    0xb96c2fca58f783f3,
    0x000000007f408eb9,
]);

/// Montgomery encoding of the base-point x-coordinate.
pub const GX_MONT: Fp = Fp([
    0xbc9052266d0a4aea,
    0x852597366018bfaa,
    0x6dd3af9bf96bec05,
    0x00000000a21b5e60,
]);

/// Montgomery encoding of the base-point y-coordinate.
pub const GY_MONT: Fp = Fp([
    0x2edca1e5eff3ede8,
    0xf8cd672b05335a6b,
    0xaea9c5ae03dfe878,
    0x00000000614786f1,
]);

/// Runtime recomputation of [`THREE_B_MONT`] as b + b + b, for the drift test.
#[cfg(test)]
fn three_b_mont_computed() -> Fp {
    let b = mont(P224_B);
    let b2 = add(&b, &b);
    add(&b2, &b)
}

// ---------------------------------------------------------------------------
// Point type
// ---------------------------------------------------------------------------

/// Projective P-224 point (X : Y : Z), coordinates in Montgomery form.
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
        y: ONE_MONT,
        z: fp_zero(),
    }
}

/// True iff the point is the identity (Z = 0).  Not constant-time.
pub fn g1_is_identity(p: &G1) -> bool {
    fp_is_zero(&p.z)
}

/// Point negation: (X : -Y : Z).
pub fn g1_neg(p: &G1) -> G1 {
    let mut ny = fp_zero();
    fp_opp(&mut ny, &p.y);
    G1 { x: p.x, y: ny, z: p.z }
}

/// Complete projective addition (Renes–Costello–Batina 2015, Algorithm 1,
/// general a).  Transcribed from the 40-op bedrock2 body of `P256_G1_add`
/// in `src/Bedrock/Curve/P256_G1_Add_Spec.v` (proved correct for P-256;
/// the sequence is generic in `a_mont` / `three_b_mont`).
///
/// Superseded as the default path by [`g1_add_a3`] (Algorithm 4).  Kept
/// as the reference for `tests/a3_diff.rs` and because it is the body
/// that `g1_extracted.rs` and `scalar_mul_extracted.rs` implement.
pub fn g1_add_general_a(p: &G1, q: &G1) -> G1 {
    let (x1, y1, z1) = (&p.x, &p.y, &p.z);
    let (x2, y2, z2) = (&q.x, &q.y, &q.z);

    // Steps 1-18 (a-independent part)
    let t0 = mul(x1, x2); //  1: t0 := X1 * X2
    let t1 = mul(y1, y2); //  2: t1 := Y1 * Y2
    let t2 = mul(z1, z2); //  3: t2 := Z1 * Z2
    let t3 = add(x1, y1); //  4: t3 := X1 + Y1
    let t4 = add(x2, y2); //  5: t4 := X2 + Y2
    let t3 = mul(&t3, &t4); //  6: t3 := t3 * t4
    let t4 = add(&t0, &t1); //  7: t4 := t0 + t1
    let t3 = sub(&t3, &t4); //  8: t3 := t3 - t4
    let t4 = add(x1, z1); //  9: t4 := X1 + Z1
    let t5 = add(x2, z2); // 10: t5 := X2 + Z2
    let t4 = mul(&t4, &t5); // 11: t4 := t4 * t5
    let t5 = add(&t0, &t2); // 12: t5 := t0 + t2
    let t4 = sub(&t4, &t5); // 13: t4 := t4 - t5
    let t5 = add(y1, z1); // 14: t5 := Y1 + Z1
    let x3 = add(y2, z2); // 15: X3 := Y2 + Z2
    let t5 = mul(&t5, &x3); // 16: t5 := t5 * X3
    let x3 = add(&t1, &t2); // 17: X3 := t1 + t2
    let t5 = sub(&t5, &x3); // 18: t5 := t5 - X3
    // Steps 19-24
    let z3 = mul(&A_MONT, &t4); // 19: Z3 := a * t4
    let x3 = mul(&THREE_B_MONT, &t2); // 20: X3 := 3b * t2
    let z3 = add(&x3, &z3); // 21: Z3 := X3 + Z3
    let x3 = sub(&t1, &z3); // 22: X3 := t1 - Z3
    let z3 = add(&z3, &t1); // 23: Z3 := Z3 + t1
    let y3 = mul(&x3, &z3); // 24: Y3 := X3 * Z3
    // Steps 25-32
    let t1 = add(&t0, &t0); // 25: t1 := t0 + t0
    let t1 = add(&t1, &t0); // 26: t1 := t1 + t0
    let t2 = mul(&A_MONT, &t2); // 27: t2 := a * t2
    let t4 = mul(&THREE_B_MONT, &t4); // 28: t4 := 3b * t4
    let t1 = add(&t1, &t2); // 29: t1 := t1 + t2
    let t2 = sub(&t0, &t2); // 30: t2 := t0 - t2
    let t2 = mul(&A_MONT, &t2); // 31: t2 := a * t2
    let t4 = add(&t4, &t2); // 32: t4 := t4 + t2
    // Steps 33-40
    let t0 = mul(&t1, &t4); // 33: t0 := t1 * t4
    let y3 = add(&y3, &t0); // 34: Y3 := Y3 + t0
    let t0 = mul(&t5, &t4); // 35: t0 := t5 * t4
    let x3 = mul(&t3, &x3); // 36: X3 := t3 * X3
    let x3 = sub(&x3, &t0); // 37: X3 := X3 - t0
    let t0 = mul(&t3, &t1); // 38: t0 := t3 * t1
    let z3 = mul(&t5, &z3); // 39: Z3 := t5 * Z3
    let z3 = add(&z3, &t0); // 40: Z3 := Z3 + t0

    G1 { x: x3, y: y3, z: z3 }
}

/// Doubling via the general-a complete addition formula.
pub fn g1_double_general_a(p: &G1) -> G1 {
    g1_add_general_a(p, p)
}

// ---------------------------------------------------------------------------
// Complete addition and doubling specialised to a = -3
// (Renes–Costello–Batina 2015, Algorithms 4 and 6)
// ---------------------------------------------------------------------------
//
// Op-for-op transcriptions of the Rupicola derivations
// `rcb_add_a3_gallina` (`src/Bedrock/Group/CurveAdd/CurveAddA3.v`,
// steps A1-A43) and `rcb_double_a3_gallina`
// (`.../CurveDoubleA3.v`, steps E1-E34).  P-224 has a = -3, so they
// apply.  Against Algorithm 1 the addition trades three multiplications
// for six additions (43 ops, 14 M) and the doubling replaces a 40-op
// self-addition with 34 ops; only `b` is needed as a constant, not `a`
// and `3b`.  `src/Bedrock/Group/CurveAdd/CurveA3Equiv.v` proves the
// chains equal at a = -3 as polynomial identities, so the agreement is
// exact equality of the projective triple, on the exceptional inputs
// too; `tests/a3_diff.rs` checks that numerically.

/// Complete projective point addition for `a = -3` (RCB Algorithm 4).
///
/// Returns exactly the same projective triple as [`g1_add_general_a`].
pub fn g1_add_a3(p: &G1, q: &G1) -> G1 {
    let (x1, y1, z1) = (&p.x, &p.y, &p.z);
    let (x2, y2, z2) = (&q.x, &q.y, &q.z);

    let t0 = mul(x1, x2); // A1  t0 := X1 * X2
    let t1 = mul(y1, y2); // A2  t1 := Y1 * Y2
    let t2 = mul(z1, z2); // A3  t2 := Z1 * Z2
    let t3 = add(x1, y1); // A4  t3 := X1 + Y1
    let t4 = add(x2, y2); // A5  t4 := X2 + Y2
    let t3 = mul(&t3, &t4); // A6  t3 := t3 * t4
    let t4 = add(&t0, &t1); // A7  t4 := t0 + t1
    let t3 = sub(&t3, &t4); // A8  t3 := t3 - t4
    let t4 = add(y1, z1); // A9  t4 := Y1 + Z1
    let x3 = add(y2, z2); // A10 X3 := Y2 + Z2
    let t4 = mul(&t4, &x3); // A11 t4 := t4 * X3
    let x3 = add(&t1, &t2); // A12 X3 := t1 + t2
    let t4 = sub(&t4, &x3); // A13 t4 := t4 - X3
    let x3 = add(x1, z1); // A14 X3 := X1 + Z1
    let y3 = add(x2, z2); // A15 Y3 := X2 + Z2
    let x3 = mul(&x3, &y3); // A16 X3 := X3 * Y3
    let y3 = add(&t0, &t2); // A17 Y3 := t0 + t2
    let y3 = sub(&x3, &y3); // A18 Y3 := X3 - Y3
    let z3 = mul(&B_MONT, &t2); // A19 Z3 := b * t2
    let x3 = sub(&y3, &z3); // A20 X3 := Y3 - Z3
    let z3 = add(&x3, &x3); // A21 Z3 := X3 + X3
    let x3 = add(&x3, &z3); // A22 X3 := X3 + Z3
    let z3 = sub(&t1, &x3); // A23 Z3 := t1 - X3
    let x3 = add(&t1, &x3); // A24 X3 := t1 + X3
    let y3 = mul(&B_MONT, &y3); // A25 Y3 := b * Y3
    let t1 = add(&t2, &t2); // A26 t1 := t2 + t2
    let t2 = add(&t1, &t2); // A27 t2 := t1 + t2
    let y3 = sub(&y3, &t2); // A28 Y3 := Y3 - t2
    let y3 = sub(&y3, &t0); // A29 Y3 := Y3 - t0
    let t1 = add(&y3, &y3); // A30 t1 := Y3 + Y3
    let y3 = add(&t1, &y3); // A31 Y3 := t1 + Y3
    let t1 = add(&t0, &t0); // A32 t1 := t0 + t0
    let t0 = add(&t1, &t0); // A33 t0 := t1 + t0
    let t0 = sub(&t0, &t2); // A34 t0 := t0 - t2
    let t1 = mul(&t4, &y3); // A35 t1 := t4 * Y3
    let t2 = mul(&t0, &y3); // A36 t2 := t0 * Y3
    let y3 = mul(&x3, &z3); // A37 Y3 := X3 * Z3
    let y3 = add(&y3, &t2); // A38 Y3 := Y3 + t2
    let x3 = mul(&t3, &x3); // A39 X3 := t3 * X3
    let x3 = sub(&x3, &t1); // A40 X3 := X3 - t1
    let z3 = mul(&t4, &z3); // A41 Z3 := t4 * Z3
    let t1 = mul(&t3, &t0); // A42 t1 := t3 * t0
    let z3 = add(&z3, &t1); // A43 Z3 := Z3 + t1

    G1 { x: x3, y: y3, z: z3 }
}

/// Complete projective point doubling for `a = -3` (RCB Algorithm 6).
///
/// Returns exactly the same projective triple as
/// `g1_add_general_a(p, p)`.
pub fn g1_double_a3(p: &G1) -> G1 {
    let (x, y, z) = (&p.x, &p.y, &p.z);

    let t0 = mul(x, x); // E1  t0 := X * X
    let t1 = mul(y, y); // E2  t1 := Y * Y
    let t2 = mul(z, z); // E3  t2 := Z * Z
    let t3 = mul(x, y); // E4  t3 := X * Y
    let t3 = add(&t3, &t3); // E5  t3 := t3 + t3
    let z3 = mul(x, z); // E6  Z3 := X * Z
    let z3 = add(&z3, &z3); // E7  Z3 := Z3 + Z3
    let y3 = mul(&B_MONT, &t2); // E8  Y3 := b * t2
    let y3 = sub(&y3, &z3); // E9  Y3 := Y3 - Z3
    let x3 = add(&y3, &y3); // E10 X3 := Y3 + Y3
    let y3 = add(&x3, &y3); // E11 Y3 := X3 + Y3
    let x3 = sub(&t1, &y3); // E12 X3 := t1 - Y3
    let y3 = add(&t1, &y3); // E13 Y3 := t1 + Y3
    let y3 = mul(&x3, &y3); // E14 Y3 := X3 * Y3
    let x3 = mul(&x3, &t3); // E15 X3 := X3 * t3
    let t3 = add(&t2, &t2); // E16 t3 := t2 + t2
    let t2 = add(&t2, &t3); // E17 t2 := t2 + t3
    let z3 = mul(&B_MONT, &z3); // E18 Z3 := b * Z3
    let z3 = sub(&z3, &t2); // E19 Z3 := Z3 - t2
    let z3 = sub(&z3, &t0); // E20 Z3 := Z3 - t0
    let t3 = add(&z3, &z3); // E21 t3 := Z3 + Z3
    let z3 = add(&z3, &t3); // E22 Z3 := Z3 + t3
    let t3 = add(&t0, &t0); // E23 t3 := t0 + t0
    let t0 = add(&t3, &t0); // E24 t0 := t3 + t0
    let t0 = sub(&t0, &t2); // E25 t0 := t0 - t2
    let t0 = mul(&t0, &z3); // E26 t0 := t0 * Z3
    let y3 = add(&y3, &t0); // E27 Y3 := Y3 + t0
    let t0 = mul(y, z); // E28 t0 := Y * Z
    let t0 = add(&t0, &t0); // E29 t0 := t0 + t0
    let z3 = mul(&t0, &z3); // E30 Z3 := t0 * Z3
    let x3 = sub(&x3, &z3); // E31 X3 := X3 - Z3
    let z3 = mul(&t0, &t1); // E32 Z3 := t0 * t1
    let z3 = add(&z3, &z3); // E33 Z3 := Z3 + Z3
    let z3 = add(&z3, &z3); // E34 Z3 := Z3 + Z3

    G1 { x: x3, y: y3, z: z3 }
}

/// Complete projective point addition — the default path.
///
/// Dispatches to the a = -3 specialisation [`g1_add_a3`].
#[inline]
pub fn g1_add(p: &G1, q: &G1) -> G1 {
    g1_add_a3(p, q)
}

/// Point doubling — the default path.
///
/// Dispatches to the a = -3 specialisation [`g1_double_a3`].
#[inline]
pub fn g1_double(p: &G1) -> G1 {
    g1_double_a3(p)
}

// ---------------------------------------------------------------------------
// Affine conversions and curve membership
// ---------------------------------------------------------------------------

/// Build a projective point from canonical (non-Montgomery) affine limbs.
/// Does not check curve membership; see [`is_on_curve_affine`].
pub fn g1_from_affine(x: &[u64; 4], y: &[u64; 4]) -> G1 {
    G1 {
        x: mont(*x),
        y: mont(*y),
        z: ONE_MONT,
    }
}

/// Convert to canonical (non-Montgomery) affine coordinates.
/// Returns `None` for the identity.  Uses the constant-time divstep
/// inverse `fp_inv`; the surrounding identity branch is not constant-time.
pub fn g1_to_affine(p: &G1) -> Option<([u64; 4], [u64; 4])> {
    if g1_is_identity(p) {
        return None;
    }
    let mut zinv = fp_zero();
    fp_inv(&mut zinv, &p.z);
    let xa = mul(&p.x, &zinv);
    let ya = mul(&p.y, &zinv);
    let mut xr = FpRaw([0u64; 4]);
    let mut yr = FpRaw([0u64; 4]);
    fp_from_montgomery(&mut xr, &xa);
    fp_from_montgomery(&mut yr, &ya);
    Some((xr.0, yr.0))
}

/// Check y^2 = x^3 + a*x + b for canonical affine limbs.
pub fn is_on_curve_affine(x: &[u64; 4], y: &[u64; 4]) -> bool {
    let xm = mont(*x);
    let ym = mont(*y);
    let lhs = square(&ym);
    let x2 = square(&xm);
    let x3 = mul(&x2, &xm);
    let ax = mul(&A_MONT, &xm);
    let rhs = add(&add(&x3, &ax), &B_MONT);
    fp_eq(&lhs, &rhs)
}

/// Projective equality (same point on the curve, any Z scaling).
/// Not constant-time; intended for tests and public data.
pub fn g1_eq(p: &G1, q: &G1) -> bool {
    match (g1_is_identity(p), g1_is_identity(q)) {
        (true, true) => true,
        (true, false) | (false, true) => false,
        (false, false) => {
            fp_eq(&mul(&p.x, &q.z), &mul(&q.x, &p.z))
                && fp_eq(&mul(&p.y, &q.z), &mul(&q.y, &p.z))
        }
    }
}

/// The base point G.
pub fn g1_generator() -> G1 {
    G1 { x: GX_MONT, y: GY_MONT, z: ONE_MONT }
}

// ---------------------------------------------------------------------------
// Constant-time scalar multiplication
// ---------------------------------------------------------------------------

/// Constant-time conditional select: returns `a` if `mask == u64::MAX`,
/// `b` if `mask == 0`.
#[inline]
fn fp_cmov(mask: u64, a: &Fp, b: &Fp) -> Fp {
    let mut out = [0u64; 4];
    let mut i = 0;
    while i < 4 {
        out[i] = (a.0[i] & mask) | (b.0[i] & !mask);
        i += 1;
    }
    Fp(out)
}

#[inline]
fn g1_cmov(mask: u64, a: &G1, b: &G1) -> G1 {
    G1 {
        x: fp_cmov(mask, &a.x, &b.x),
        y: fp_cmov(mask, &a.y, &b.y),
        z: fp_cmov(mask, &a.z, &b.z),
    }
}

/// Constant-time width-1 scalar multiplication k * P.
///
/// The scalar `k` is given as 4 little-endian u64 limbs and must be
/// less than 2^224 (bits 224..255 are ignored — the loop covers exactly
/// the 224 scalar bits, MSB first).  Fixed-length double-and-add: every
/// iteration performs one complete addition-as-doubling, one complete
/// addition, and a limb-masked conditional select; there are no
/// secret-dependent branches or memory indices.
///
/// Retained as the differential-test reference for the windowed
/// [`g1_scalar_mul`], which is the default path.
/// Kept as the differential-test reference (`windowed_matches_width1_*`
/// below): it is the simplest correct constant-time ladder in the crate,
/// so it is what the faster one is checked against.
pub fn g1_scalar_mul_width1(k: &[u64; 4], p: &G1) -> G1 {
    let mut acc = g1_identity();
    let mut i: i32 = 223;
    while i >= 0 {
        acc = g1_double(&acc);
        let sum = g1_add(&acc, p);
        let bit = (k[(i as usize) / 64] >> ((i as usize) % 64)) & 1;
        let mask = 0u64.wrapping_sub(bit);
        acc = g1_cmov(mask, &sum, &acc);
        i -= 1;
    }
    acc
}

// ---------------------------------------------------------------------------
// Constant-time windowed variable-base scalar multiplication
// ---------------------------------------------------------------------------
//
// Same windowing technique as `g1_scalar_mul_base` below, with the table
// built at run time from the input point instead of read from `g_table`.
//
// Operation counts at 224 bits (D = doubling, A = addition):
//
//   width 1     224 D + 224 A                       = 6048 field mul
//   W = 4        (7 + 220) D + (7 + 55) A           = 3819 field mul
//   W = 5       (15 + 220) D + (15 + 44) A          = 3881 field mul
//
// counting `g1_double` at 13 multiplications and `g1_add` at 14, and
// charging the table build 2^(W-1)-1 doublings and 2^(W-1)-1 additions.
// W = 4 also scans fewer table entries (56 x 15 = 840 against
// 45 x 31 = 1395), so it wins on both counts; the sibling P-256 crate's
// `examples/bench_width.rs` measured the same ordering directly.

/// Window width of the variable-base ladder, in bits.
pub const VAR_W: usize = 4;

/// Number of windows, `ceil(224 / VAR_W)`.
pub const VAR_WINDOWS: usize = (224 + VAR_W - 1) / VAR_W;

/// Non-zero digits per window, `2^VAR_W - 1`; also the number of
/// precomputed multiples of the input point.
pub const VAR_TSIZE: usize = (1 << VAR_W) - 1;

/// The `i`-th `VAR_W`-bit digit of the scalar, LSB-first window order
/// (window `i` carries weight `2^(VAR_W*i)`).  `i` is a loop counter,
/// never secret.
#[inline]
fn var_digit(k: &[u64; 4], i: usize) -> u64 {
    let mut d = 0u64;
    let mut b = 0;
    while b < VAR_W {
        let idx = i * VAR_W + b;
        if idx < 224 {
            d |= ((k[idx / 64] >> (idx % 64)) & 1) << b;
        }
        b += 1;
    }
    d
}

/// Constant-time scalar multiplication: `k * P`, variable base.
///
/// `k` is 4 little-endian u64 limbs and must be less than `2^224`, the
/// same convention as [`g1_scalar_mul_width1`]; bits 224..255 are
/// ignored.
///
/// Fixed `VAR_W`-bit window, MSB first.  `T[j] = j * P` for
/// `j = 1 ..= VAR_TSIZE` is built once with the complete `g1_add` /
/// `g1_double`; then, from the most significant window down, the
/// accumulator is doubled `VAR_W` times and one table entry is added.
///
/// Constant-time, on the same argument as [`g1_scalar_mul_base`]:
///
/// * the table entry is chosen by a **full linear scan** of all
///   `VAR_TSIZE` entries with [`ct_eq_mask`] / [`fp_cmov`], so the table
///   is never indexed by a digit and the addresses touched are the same
///   for every scalar;
/// * digit `0` matches no entry and leaves the identity in `sel`, which
///   the complete addition formula absorbs with no special case;
/// * every branch is on `i`, `j` or `b`, loop counters derived from the
///   public constants `VAR_W` and `VAR_WINDOWS`;
/// * there is no early exit and no data-dependent iteration count.
pub fn g1_scalar_mul(k: &[u64; 4], p: &G1) -> G1 {
    // T[j - 1] = j * P, j = 1 ..= VAR_TSIZE.  Even j is one doubling of
    // T[j/2], odd j is one addition of P to T[j-1]; `j` is public.
    let mut t = [*p; VAR_TSIZE];
    let mut j = 2usize;
    while j <= VAR_TSIZE {
        t[j - 1] = if j % 2 == 0 {
            g1_double(&t[j / 2 - 1])
        } else {
            g1_add(&t[j - 2], p)
        };
        j += 1;
    }

    let mut acc = g1_identity();
    let mut i = VAR_WINDOWS;
    while i > 0 {
        i -= 1;
        let top = i + 1 == VAR_WINDOWS;
        // `top` is a function of the loop counter, hence public.  The
        // accumulator is the identity before the first window, so the
        // VAR_W doublings and the addition are both skipped there.
        if !top {
            let mut d = 0;
            while d < VAR_W {
                acc = g1_double(&acc);
                d += 1;
            }
        }
        let digit = var_digit(k, i);
        // Full scan of the table: identity when digit == 0.
        let mut sx = fp_zero();
        let mut sy = ONE_MONT;
        let mut sz = fp_zero();
        let mut j = 1usize;
        while j <= VAR_TSIZE {
            let e = &t[j - 1];
            let m = ct_eq_mask(digit, j as u64);
            sx = fp_cmov(m, &e.x, &sx);
            sy = fp_cmov(m, &e.y, &sy);
            sz = fp_cmov(m, &e.z, &sz);
            j += 1;
        }
        let sel = G1 { x: sx, y: sy, z: sz };
        acc = if top { sel } else { g1_add(&acc, &sel) };
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
/// `ceil(224/W)` additions; W=5 is the knee of the speed/size curve
/// (see the P-256 crate's `BASE_W` note for the W=4/5/6 numbers).
pub const BASE_W: usize = 5;

/// Number of windows, `ceil(224 / BASE_W)`.
pub const BASE_WINDOWS: usize = (224 + BASE_W - 1) / BASE_W;

/// Non-zero digits per window, `2^BASE_W - 1`.
pub const BASE_TSIZE: usize = (1 << BASE_W) - 1;

/// Size of the precomputed table in bytes
/// (`BASE_WINDOWS * BASE_TSIZE` affine points, 2 x 32 bytes each).
pub const BASE_TABLE_BYTES: usize = BASE_WINDOWS * BASE_TSIZE * 2 * 32;

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
fn base_digit(k: &[u64; 4], i: usize) -> u64 {
    let mut d = 0u64;
    let mut b = 0;
    while b < BASE_W {
        let idx = i * BASE_W + b;
        if idx < 224 {
            d |= ((k[idx / 64] >> (idx % 64)) & 1) << b;
        }
        b += 1;
    }
    d
}

/// Constant-time fixed-base scalar multiplication: `k * G`.
///
/// `k` is 4 little-endian u64 limbs and must be less than `2^224`, the
/// same convention as [`g1_scalar_mul`]; bits 224..255 are ignored.
///
/// The scalar is split into [`BASE_WINDOWS`] digits of [`BASE_W`] bits.
/// Digit `d` of window `i` selects `d * 2^(BASE_W*i) * G` from the
/// precomputed table `g_table::G_TABLE`, so there are no doublings — one
/// complete addition per window instead of the ladder's 448.
///
/// Constant-time: the lookup is a full linear scan of all [`BASE_TSIZE`]
/// entries of the window with a limb-mask select ([`ct_eq_mask`] /
/// [`fp_cmov`]), so the addresses touched and the instruction trace depend
/// only on the public `BASE_W` / `BASE_WINDOWS`.  `d = 0` leaves the
/// identity in `sel`, which the complete formula handles with no special
/// case.
pub fn g1_scalar_mul_base(k: &[u64; 4]) -> G1 {
    let mut acc = g1_identity();
    let mut i = 0;
    while i < BASE_WINDOWS {
        let digit = base_digit(k, i);
        let mut sx = fp_zero();
        let mut sy = ONE_MONT;
        let mut sz = fp_zero();
        let mut j = 1usize;
        while j <= BASE_TSIZE {
            let e = &g_table::G_TABLE[i * BASE_TSIZE + (j - 1)];
            let m = ct_eq_mask(digit, j as u64);
            sx = fp_cmov(m, &Fp(e[0]), &sx);
            sy = fp_cmov(m, &Fp(e[1]), &sy);
            sz = fp_cmov(m, &ONE_MONT, &sz);
            j += 1;
        }
        let sel = G1 { x: sx, y: sy, z: sz };
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

    fn scalar(v: u64) -> [u64; 4] {
        [v, 0, 0, 0]
    }

    /// Checked 256-bit little-endian addition; panics on overflow past
    /// 2^224 so distributivity tests never need reduction mod n.
    fn scalar_add_checked(a: &[u64; 4], b: &[u64; 4]) -> [u64; 4] {
        let mut out = [0u64; 4];
        let mut carry = 0u64;
        for i in 0..4 {
            let (s1, c1) = a[i].overflowing_add(b[i]);
            let (s2, c2) = s1.overflowing_add(carry);
            out[i] = s2;
            carry = (c1 as u64) + (c2 as u64);
        }
        assert_eq!(carry, 0, "scalar sum overflows 256 bits");
        assert!(out[3] < 1u64 << 32, "scalar sum >= 2^224");
        out
    }

    /// The hoisted Montgomery constants must equal the runtime computation
    /// they replaced, so they cannot silently drift.
    #[test]
    fn mont_constants_match_runtime() {
        assert_eq!(ONE_MONT.0, mont([1, 0, 0, 0]).0, "ONE_MONT");
        assert_eq!(A_MONT.0, mont(P224_A).0, "A_MONT");
        assert_eq!(B_MONT.0, mont(P224_B).0, "B_MONT");
        assert_eq!(THREE_B_MONT.0, three_b_mont_computed().0, "THREE_B_MONT");
        assert_eq!(GX_MONT.0, mont(P224_GX).0, "GX_MONT");
        assert_eq!(GY_MONT.0, mont(P224_GY).0, "GY_MONT");
    }

    /// `A_MONT` / `THREE_B_MONT` must equal the `cA` / `cB3` byte literals of
    /// the Rocq-emitted `g1_extracted.rs`, read little-endian.
    #[test]
    fn mont_constants_match_extracted_literals() {
        let ca: [u8; 32] = [
            1, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 255, 255, 255, 255, 252, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 0, 0, 0, 0,
        ];
        let cb3: [u8; 32] = [
            102, 13, 65, 43, 227, 105, 58, 182, 50, 57, 208, 102, 220, 72, 112, 49, 243, 131, 247,
            88, 202, 47, 108, 185, 185, 142, 64, 127, 0, 0, 0, 0,
        ];
        let le = |bs: &[u8; 32]| {
            let mut o = [0u64; 4];
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
                    g1_eq(&want, &acc),
                    "G_TABLE[{i}][{j}] != {j} * 2^({BASE_W}*{i}) * G"
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
            let k = scalar(v);
            assert!(
                g1_eq(&g1_scalar_mul_base(&k), &g1_scalar_mul(&k, &g)),
                "g1_scalar_mul_base disagrees with the ladder at k = {v}"
            );
        }
        assert!(g1_is_identity(&g1_scalar_mul_base(&P224_N)), "n * G != O");
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
        for _ in 0..8 {
            let mut k = [0u64; 4];
            for w in k.iter_mut() {
                *w = next();
            }
            k[3] &= 0x0000_0000_ffff_ffff; // keep k < 2^224
            assert!(
                g1_eq(&g1_scalar_mul_base(&k), &g1_scalar_mul(&k, &g)),
                "g1_scalar_mul_base disagrees with the ladder"
            );
        }
    }

    #[test]
    fn generator_is_on_curve() {
        // Validates b, Gx, Gy jointly.
        assert!(is_on_curve_affine(&P224_GX, &P224_GY));
    }

    // -----------------------------------------------------------------
    // Windowed variable-base ladder vs the width-1 ladder it replaced
    // -----------------------------------------------------------------

    /// Checked little-endian subtraction; panics on borrow-out.
    fn scalar_sub_checked(a: &[u64; 4], b: &[u64; 4]) -> [u64; 4] {
        let mut out = [0u64; 4];
        let mut borrow = 0u64;
        for i in 0..4 {
            let (d1, b1) = a[i].overflowing_sub(b[i]);
            let (d2, b2) = d1.overflowing_sub(borrow);
            out[i] = d2;
            borrow = (b1 as u64) + (b2 as u64);
        }
        assert_eq!(borrow, 0, "scalar subtraction borrowed out");
        out
    }

    /// The structured scalars both ladders must agree on.  Everything
    /// here stays below `2^224`, the input convention of both ladders.
    fn structured_scalars() -> Vec<[u64; 4]> {
        let one = scalar(1);
        let mut v = vec![
            [0u64; 4],                              // k = 0
            scalar(1),                              // k = 1
            scalar(2),                              // k = 2
            scalar_sub_checked(&P224_N, &one),      // k = n - 1
            P224_N,                                 // k = n
            scalar_add_checked(&P224_N, &one),      // k = n + 1
            [u64::MAX, u64::MAX, u64::MAX, 0xffff_ffff], // 2^224 - 1
        ];
        // A single bit set at each of the 224 positions.
        for bit in 0..224usize {
            let mut k = [0u64; 4];
            k[bit / 64] = 1u64 << (bit % 64);
            v.push(k);
        }
        v
    }

    #[test]
    fn windowed_matches_width1_structured() {
        let g = g1_generator();
        let pts = [g1_identity(), g, g1_double(&g), g1_neg(&g)];
        for (pi, p) in pts.iter().enumerate() {
            for (si, k) in structured_scalars().iter().enumerate() {
                assert!(
                    g1_eq(&g1_scalar_mul(k, p), &g1_scalar_mul_width1(k, p)),
                    "windowed != width-1 at point {pi}, scalar #{si}"
                );
            }
        }
    }

    #[test]
    fn windowed_matches_width1_random() {
        // Deterministic xorshift, so a failure is reproducible.
        let mut state: u64 = 0xdead_beef_1234_5678;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let g = g1_generator();
        let pts = [
            g,
            g1_double(&g),
            g1_scalar_mul_width1(&scalar(0x5eed_1234_5678_9abc), &g),
        ];
        for p in pts.iter() {
            for i in 0..128 {
                let mut k = [next(), next(), next(), next()];
                k[3] &= 0xffff_ffff; // keep k < 2^224
                assert!(
                    g1_eq(&g1_scalar_mul(&k, p), &g1_scalar_mul_width1(&k, p)),
                    "windowed != width-1 on random scalar #{i}"
                );
            }
        }
    }

    /// The exact input of `examples/bench.rs`: the reported speedup must
    /// be on the same answer the width-1 ladder gave.
    #[test]
    fn windowed_matches_width1_on_bench_input() {
        let k: [u64; 4] = [
            0x0f1e_2d3c_4b5a_6978,
            0x8796_a5b4_c3d2_e1f0,
            0x1a2b_3c4d_5e6f_7081,
            0x0000_0000_02a3_b4c5,
        ];
        let g = g1_generator();
        let g2 = g1_double(&g);
        assert!(g1_eq(&g1_scalar_mul(&k, &g), &g1_scalar_mul_width1(&k, &g)));
        assert!(g1_eq(&g1_scalar_mul(&k, &g2), &g1_scalar_mul_width1(&k, &g2)));
    }

    /// Every digit value `1 ..= VAR_TSIZE` must select `j * P`: run the
    /// windowed ladder on the one-digit scalars and compare against
    /// repeated addition.  This is the table-scan invariant, isolated.
    #[test]
    fn windowed_selects_every_digit() {
        let g = g1_generator();
        for p in [g, g1_double(&g)] {
            let mut want = p;
            for j in 1..=VAR_TSIZE {
                assert!(
                    g1_eq(&g1_scalar_mul(&scalar(j as u64), &p), &want),
                    "digit {j} does not select {j} * P"
                );
                want = g1_add(&want, &p);
            }
        }
        // Digit 0 in every window: the scan must leave the identity.
        assert!(g1_is_identity(&g1_scalar_mul(&[0u64; 4], &g)));
    }

    #[test]
    fn order_times_generator_is_identity() {
        // Validates n against the curve arithmetic; a wrong n (or wrong
        // curve constants) makes this fail with overwhelming probability.
        let ng = g1_scalar_mul(&P224_N, &g1_generator());
        assert!(g1_is_identity(&ng));
    }

    #[test]
    fn double_matches_scalar_mul_two() {
        let g = g1_generator();
        let d = g1_add(&g, &g);
        let two_g = g1_scalar_mul(&scalar(2), &g);
        assert!(g1_eq(&d, &two_g));
        assert!(g1_eq(&g1_double(&g), &two_g));
    }

    #[test]
    fn scalar_mul_distributes_over_scalar_addition() {
        let g = g1_generator();
        // Small pairs plus large fixed scalars (sums stay below 2^224).
        let big1: [u64; 4] = [
            0x0123456789abcdef,
            0xfedcba9876543210,
            0x0f1e2d3c4b5a6978,
            0x000000007fffffff,
        ];
        let big2: [u64; 4] = [
            0xdeadbeefcafebabe,
            0x0102030405060708,
            0x1122334455667788,
            0x000000006fffffff,
        ];
        let pairs: [([u64; 4], [u64; 4]); 5] = [
            (scalar(1), scalar(1)),
            (scalar(2), scalar(3)),
            (scalar(7), scalar(11)),
            (scalar(123456789), big1),
            (big1, big2),
        ];
        for (k1, k2) in pairs.iter() {
            let k12 = scalar_add_checked(k1, k2);
            let lhs = g1_scalar_mul(&k12, &g);
            let rhs = g1_add(&g1_scalar_mul(k1, &g), &g1_scalar_mul(k2, &g));
            assert!(g1_eq(&lhs, &rhs));
        }
    }

    #[test]
    fn addition_is_commutative_and_associative() {
        let g = g1_generator();
        let p2 = g1_scalar_mul(&scalar(2), &g);
        let p3 = g1_scalar_mul(&scalar(3), &g);
        let p5 = g1_scalar_mul(&scalar(5), &g);
        // Commutativity
        assert!(g1_eq(&g1_add(&p2, &p3), &g1_add(&p3, &p2)));
        assert!(g1_eq(&g1_add(&g, &p5), &g1_add(&p5, &g)));
        // Associativity
        let lhs = g1_add(&g1_add(&p2, &p3), &p5);
        let rhs = g1_add(&p2, &g1_add(&p3, &p5));
        assert!(g1_eq(&lhs, &rhs));
        // Cross-check against 10*G
        assert!(g1_eq(&lhs, &g1_scalar_mul(&scalar(10), &g)));
    }

    #[test]
    fn identity_laws() {
        let g = g1_generator();
        let o = g1_identity();
        // P + O = P (complete formula handles Z = 0 inputs)
        assert!(g1_eq(&g1_add(&g, &o), &g));
        assert!(g1_eq(&g1_add(&o, &g), &g));
        // P + (-P) = O
        assert!(g1_is_identity(&g1_add(&g, &g1_neg(&g))));
        // O + O = O
        assert!(g1_is_identity(&g1_add(&o, &o)));
        // 0 * G = O
        assert!(g1_is_identity(&g1_scalar_mul(&scalar(0), &g)));
    }

    #[test]
    fn affine_round_trip() {
        let g = g1_generator();
        let p7 = g1_scalar_mul(&scalar(7), &g);
        let (xa, ya) = g1_to_affine(&p7).expect("7*G is not the identity");
        assert!(is_on_curve_affine(&xa, &ya));
        assert!(g1_eq(&g1_from_affine(&xa, &ya), &p7));
        // Generator round-trips to the FIPS coordinates.
        let (gx, gy) = g1_to_affine(&g).unwrap();
        assert_eq!(gx, P224_GX);
        assert_eq!(gy, P224_GY);
        assert!(g1_to_affine(&g1_identity()).is_none());
    }
}
