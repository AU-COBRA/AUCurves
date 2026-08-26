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

/// Montgomery-domain curve constant a = -3.
#[inline]
fn a_mont() -> Fp {
    mont(P224_A)
}

/// Montgomery-domain curve constant 3*b.
#[inline]
fn three_b_mont() -> Fp {
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
        y: mont([1, 0, 0, 0]),
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
pub fn g1_add(p: &G1, q: &G1) -> G1 {
    let a_c = a_mont();
    let b3 = three_b_mont();
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
    let z3 = mul(&a_c, &t4); // 19: Z3 := a * t4
    let x3 = mul(&b3, &t2); // 20: X3 := 3b * t2
    let z3 = add(&x3, &z3); // 21: Z3 := X3 + Z3
    let x3 = sub(&t1, &z3); // 22: X3 := t1 - Z3
    let z3 = add(&z3, &t1); // 23: Z3 := Z3 + t1
    let y3 = mul(&x3, &z3); // 24: Y3 := X3 * Z3
    // Steps 25-32
    let t1 = add(&t0, &t0); // 25: t1 := t0 + t0
    let t1 = add(&t1, &t0); // 26: t1 := t1 + t0
    let t2 = mul(&a_c, &t2); // 27: t2 := a * t2
    let t4 = mul(&b3, &t4); // 28: t4 := 3b * t4
    let t1 = add(&t1, &t2); // 29: t1 := t1 + t2
    let t2 = sub(&t0, &t2); // 30: t2 := t0 - t2
    let t2 = mul(&a_c, &t2); // 31: t2 := a * t2
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

/// Doubling via the complete addition formula.
pub fn g1_double(p: &G1) -> G1 {
    g1_add(p, p)
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
        z: mont([1, 0, 0, 0]),
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
    let ax = mul(&a_mont(), &xm);
    let rhs = add(&add(&x3, &ax), &mont(P224_B));
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
    g1_from_affine(&P224_GX, &P224_GY)
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

/// Constant-time scalar multiplication k * P.
///
/// The scalar `k` is given as 4 little-endian u64 limbs and must be
/// less than 2^224 (bits 224..255 are ignored — the loop covers exactly
/// the 224 scalar bits, MSB first).  Fixed-length double-and-add: every
/// iteration performs one complete addition-as-doubling, one complete
/// addition, and a limb-masked conditional select; there are no
/// secret-dependent branches or memory indices.
pub fn g1_scalar_mul(k: &[u64; 4], p: &G1) -> G1 {
    let mut acc = g1_identity();
    let mut i: i32 = 223;
    while i >= 0 {
        acc = g1_add(&acc, &acc);
        let sum = g1_add(&acc, p);
        let bit = (k[(i as usize) / 64] >> ((i as usize) % 64)) & 1;
        let mask = 0u64.wrapping_sub(bit);
        acc = g1_cmov(mask, &sum, &acc);
        i -= 1;
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

    #[test]
    fn generator_is_on_curve() {
        // Validates b, Gx, Gy jointly.
        assert!(is_on_curve_affine(&P224_GX, &P224_GY));
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
