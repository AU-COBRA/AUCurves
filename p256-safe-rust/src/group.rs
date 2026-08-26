//! P-256 (secp256r1) projective group operations, hand-written over the
//! fiat-crypto field leaves in `lib.rs`.
//!
//! The point addition is a line-by-line transcription of the bedrock2
//! function body [`P256_G1_add`] in
//! `src/Bedrock/Curve/P256_G1_Add_Spec.v` (proved correct there,
//! theorem `P256_G1_add_func_ok`, Qed).  That body implements the
//! Renes–Costello–Batina 2015 complete addition formula (Algorithm 1,
//! general `a != 0` case, 40 field operations) for homogeneous
//! projective coordinates with identity `(0 : 1 : 0)`.
//!
//! Because the formula is complete, `g1_add(P, P)` computes `2P` and
//! addition with the identity is correct, so doubling is implemented as
//! self-addition.
//!
//! Curve constants (canonical, non-Montgomery limbs, little-endian u64):
//! - `b`, and the group order `n`, from
//!   `fiat-crypto/src/Curves/Weierstrass/P256.v` (`b`,
//!   `p256_group_order`); `n` also appears in the header of
//!   `fiat-crypto/fiat-rust/src/p256_scalar_64.rs`.  `b` also appears
//!   in `src/Bedrock/Curve/P256_G1_Add_Spec.v` (`b_val`).
//! - Base point `Gx`, `Gy` from FIPS 186-4 / SEC 2 v2.0 §2.4.2 (they do
//!   not appear in this repository); they are validated jointly with
//!   `b` and `n` by the tests below (G on curve, n·G = identity).
//! - `a = -3 mod p` is computed at runtime as `fp_opp` of the
//!   Montgomery encoding of 3; `3b` as `b + b + b`.
//!
//! Scalar-multiplication input format: 32 bytes, **big-endian**.
//! The ladder is a fixed-length MSB-first double-and-add over all 256
//! bits with a limb-mask conditional select
//! (`mask = 0u64.wrapping_sub(bit)`); there are no secret-dependent
//! branches or memory addresses.

use crate::{fp_add, fp_inv, fp_mul, fp_opp, fp_square, fp_sub, fp_to_montgomery, Fp, FpRaw};

/// Homogeneous projective point (X : Y : Z), coordinates in Montgomery form.
/// Identity is (0 : 1 : 0).
#[derive(Clone, Copy)]
pub struct G1 {
    pub x: Fp,
    pub y: Fp,
    pub z: Fp,
}

// ---------------------------------------------------------------------------
// Curve constants (canonical, non-Montgomery limbs, little-endian u64)
// ---------------------------------------------------------------------------

/// b = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
/// (fiat-crypto/src/Curves/Weierstrass/P256.v, `b`).
pub const B_CANON: [u64; 4] = [
    0x3bce3c3e27d2604b,
    0x651d06b0cc53b0f6,
    0xb3ebbd55769886bc,
    0x5ac635d8aa3a93e7,
];

/// Gx = 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296
/// (FIPS 186-4 D.1.2.3 / SEC 2 v2.0 §2.4.2).
pub const GX_CANON: [u64; 4] = [
    0xf4a13945d898c296,
    0x77037d812deb33a0,
    0xf8bce6e563a440f2,
    0x6b17d1f2e12c4247,
];

/// Gy = 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5
/// (FIPS 186-4 D.1.2.3 / SEC 2 v2.0 §2.4.2).
pub const GY_CANON: [u64; 4] = [
    0xcbb6406837bf51f5,
    0x2bce33576b315ece,
    0x8ee7eb4a7c0f9e16,
    0x4fe342e2fe1a7f9b,
];

/// Group order n =
/// 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
/// (fiat-crypto/src/Curves/Weierstrass/P256.v `p256_group_order`;
/// fiat-crypto/fiat-rust/src/p256_scalar_64.rs header).
pub const N_CANON: [u64; 4] = [
    0xf3b9cac2fc632551,
    0xbce6faada7179e84,
    0xffffffffffffffff,
    0xffffffff00000000,
];

#[inline]
fn to_mont(canon: [u64; 4]) -> Fp {
    let mut out = Fp([0u64; 4]);
    fp_to_montgomery(&mut out, &FpRaw(canon));
    out
}

/// Montgomery encoding of 1.
#[inline]
fn fp_one() -> Fp {
    to_mont([1, 0, 0, 0])
}

/// Montgomery encoding of a = -3 mod p, computed as opp(3).
#[inline]
fn a_mont() -> Fp {
    let three = to_mont([3, 0, 0, 0]);
    let mut a = Fp([0u64; 4]);
    fp_opp(&mut a, &three);
    a
}

/// Montgomery encoding of 3b, computed as b + b + b.
#[inline]
fn three_b_mont() -> Fp {
    let b = to_mont(B_CANON);
    let mut bb = Fp([0u64; 4]);
    fp_add(&mut bb, &b, &b);
    let mut tb = Fp([0u64; 4]);
    fp_add(&mut tb, &bb, &b);
    tb
}

// ---------------------------------------------------------------------------
// Basic point operations
// ---------------------------------------------------------------------------

/// The identity (0 : 1 : 0).
pub fn g1_identity() -> G1 {
    G1 {
        x: Fp([0u64; 4]),
        y: fp_one(),
        z: Fp([0u64; 4]),
    }
}

/// Identity test: Z = 0.  fiat-crypto outputs are fully reduced, so the
/// Montgomery representation of 0 is exactly the all-zero limb vector.
/// Not constant-time; do not call on secret data.
pub fn g1_is_identity(p: &G1) -> bool {
    p.z.0 == [0u64; 4]
}

/// Negation: (X : -Y : Z).
pub fn g1_neg(p: &G1) -> G1 {
    let mut ny = Fp([0u64; 4]);
    fp_opp(&mut ny, &p.y);
    G1 { x: p.x, y: ny, z: p.z }
}

/// Affine (x, y) in Montgomery form -> projective (x : y : 1).
pub fn g1_from_affine(x: &Fp, y: &Fp) -> G1 {
    G1 { x: *x, y: *y, z: fp_one() }
}

/// Projective -> affine (x/z, y/z), both in Montgomery form.
/// Returns `None` for the identity.  Not constant-time in the identity
/// test; the inversion itself is the constant-time divstep `fp_inv`.
pub fn g1_to_affine(p: &G1) -> Option<(Fp, Fp)> {
    if g1_is_identity(p) {
        return None;
    }
    let mut zinv = Fp([0u64; 4]);
    fp_inv(&mut zinv, &p.z);
    let mut ax = Fp([0u64; 4]);
    let mut ay = Fp([0u64; 4]);
    fp_mul(&mut ax, &p.x, &zinv);
    fp_mul(&mut ay, &p.y, &zinv);
    Some((ax, ay))
}

/// On-curve check for an affine point (Montgomery form):
/// y^2 == x^3 + a*x + b with a = -3.
pub fn g1_affine_on_curve(x: &Fp, y: &Fp) -> bool {
    let mut lhs = Fp([0u64; 4]);
    fp_square(&mut lhs, y);
    let mut x2 = Fp([0u64; 4]);
    fp_square(&mut x2, x);
    let mut x3 = Fp([0u64; 4]);
    fp_mul(&mut x3, &x2, x);
    let mut ax = Fp([0u64; 4]);
    fp_mul(&mut ax, &a_mont(), x);
    let mut rhs = Fp([0u64; 4]);
    fp_add(&mut rhs, &x3, &ax);
    let mut rhs2 = Fp([0u64; 4]);
    fp_add(&mut rhs2, &rhs, &to_mont(B_CANON));
    lhs.0 == rhs2.0
}

/// The standard base point G, projective, Montgomery form.
pub fn g1_generator() -> G1 {
    g1_from_affine(&to_mont(GX_CANON), &to_mont(GY_CANON))
}

// ---------------------------------------------------------------------------
// Complete addition (Renes–Costello–Batina 2015, general a)
// ---------------------------------------------------------------------------

/// Complete projective point addition.
///
/// Faithful transcription of the 40-field-op call sequence in the
/// bedrock2 body `P256_G1_add` of
/// `src/Bedrock/Curve/P256_G1_Add_Spec.v` (lines with `$mul`/`$add`/
/// `$sub`), which is proved correct there (`P256_G1_add_func_ok`, Qed).
/// Variable names t0..t5, x3 (= outx), y3 (= outy), z3 (= outz) match
/// the bedrock2 temporaries.
pub fn g1_add(p: &G1, q: &G1) -> G1 {
    let (x1, y1, z1) = (&p.x, &p.y, &p.z);
    let (x2, y2, z2) = (&q.x, &q.y, &q.z);
    let a = a_mont();
    let three_b = three_b_mont();

    let mut t0 = Fp([0u64; 4]);
    let mut t1 = Fp([0u64; 4]);
    let mut t2 = Fp([0u64; 4]);
    let mut t3 = Fp([0u64; 4]);
    let mut t4 = Fp([0u64; 4]);
    let mut t5 = Fp([0u64; 4]);
    let mut x3 = Fp([0u64; 4]);
    let mut y3 = Fp([0u64; 4]);
    let mut z3 = Fp([0u64; 4]);

    // Steps 1-18 (same as the a=0 case)
    fp_mul(&mut t0, x1, x2); //  1: t0 := X1 * X2
    fp_mul(&mut t1, y1, y2); //  2: t1 := Y1 * Y2
    fp_mul(&mut t2, z1, z2); //  3: t2 := Z1 * Z2
    fp_add(&mut t3, x1, y1); //  4: t3 := X1 + Y1
    fp_add(&mut t4, x2, y2); //  5: t4 := X2 + Y2
    let s = t3;
    fp_mul(&mut t3, &s, &t4); //  6: t3 := t3 * t4
    fp_add(&mut t4, &t0, &t1); //  7: t4 := t0 + t1
    let s = t3;
    fp_sub(&mut t3, &s, &t4); //  8: t3 := t3 - t4
    fp_add(&mut t4, x1, z1); //  9: t4 := X1 + Z1
    fp_add(&mut t5, x2, z2); // 10: t5 := X2 + Z2
    let s = t4;
    fp_mul(&mut t4, &s, &t5); // 11: t4 := t4 * t5
    fp_add(&mut t5, &t0, &t2); // 12: t5 := t0 + t2
    let s = t4;
    fp_sub(&mut t4, &s, &t5); // 13: t4 := t4 - t5
    fp_add(&mut t5, y1, z1); // 14: t5 := Y1 + Z1
    fp_add(&mut x3, y2, z2); // 15: x3 := Y2 + Z2
    let s = t5;
    fp_mul(&mut t5, &s, &x3); // 16: t5 := t5 * x3
    fp_add(&mut x3, &t1, &t2); // 17: x3 := t1 + t2
    let s = t5;
    fp_sub(&mut t5, &s, &x3); // 18: t5 := t5 - x3
    // Steps 19-24
    fp_mul(&mut z3, &a, &t4); // 19: z3 := a * t4
    fp_mul(&mut x3, &three_b, &t2); // 20: x3 := 3b * t2
    let s = z3;
    fp_add(&mut z3, &x3, &s); // 21: z3 := x3 + z3
    fp_sub(&mut x3, &t1, &z3); // 22: x3 := t1 - z3
    let s = z3;
    fp_add(&mut z3, &s, &t1); // 23: z3 := z3 + t1
    fp_mul(&mut y3, &x3, &z3); // 24: y3 := x3 * z3
    // Steps 25-32
    fp_add(&mut t1, &t0, &t0); // 25: t1 := t0 + t0
    let s = t1;
    fp_add(&mut t1, &s, &t0); // 26: t1 := t1 + t0
    let s = t2;
    fp_mul(&mut t2, &a, &s); // 27: t2 := a * t2
    let s = t4;
    fp_mul(&mut t4, &three_b, &s); // 28: t4 := 3b * t4
    let s = t1;
    fp_add(&mut t1, &s, &t2); // 29: t1 := t1 + t2
    let s = t2;
    fp_sub(&mut t2, &t0, &s); // 30: t2 := t0 - t2
    let s = t2;
    fp_mul(&mut t2, &a, &s); // 31: t2 := a * t2
    let s = t4;
    fp_add(&mut t4, &s, &t2); // 32: t4 := t4 + t2
    // Steps 33-40: final accumulation
    fp_mul(&mut t0, &t1, &t4); // 33: t0 := t1 * t4
    let s = y3;
    fp_add(&mut y3, &s, &t0); // 34: y3 := y3 + t0
    fp_mul(&mut t0, &t5, &t4); // 35: t0 := t5 * t4
    let s = x3;
    fp_mul(&mut x3, &t3, &s); // 36: x3 := t3 * x3
    let s = x3;
    fp_sub(&mut x3, &s, &t0); // 37: x3 := x3 - t0
    fp_mul(&mut t0, &t3, &t1); // 38: t0 := t3 * t1
    let s = z3;
    fp_mul(&mut z3, &t5, &s); // 39: z3 := t5 * z3
    let s = z3;
    fp_add(&mut z3, &s, &t0); // 40: z3 := z3 + t0

    G1 { x: x3, y: y3, z: z3 }
}

/// Doubling via the complete addition formula.
pub fn g1_double(p: &G1) -> G1 {
    g1_add(p, p)
}

// ---------------------------------------------------------------------------
// Constant-time scalar multiplication
// ---------------------------------------------------------------------------

/// Constant-time conditional select: out = if bit == 1 { b } else { a }.
/// `bit` must be 0 or 1.
#[inline]
fn fp_cmov(a: &Fp, b: &Fp, bit: u64) -> Fp {
    let mask = 0u64.wrapping_sub(bit);
    let mut out = [0u64; 4];
    let mut i = 0;
    while i < 4 {
        out[i] = (a.0[i] & !mask) | (b.0[i] & mask);
        i += 1;
    }
    Fp(out)
}

#[inline]
fn g1_cmov(a: &G1, b: &G1, bit: u64) -> G1 {
    G1 {
        x: fp_cmov(&a.x, &b.x, bit),
        y: fp_cmov(&a.y, &b.y, bit),
        z: fp_cmov(&a.z, &b.z, bit),
    }
}

/// Constant-time scalar multiplication: k * P.
///
/// `scalar` is 32 bytes, big-endian.  Fixed-length MSB-first
/// double-and-add over all 256 bits: every iteration performs one
/// complete doubling, one complete addition, and a limb-mask
/// conditional select; there are no secret-dependent branches or
/// memory accesses.
pub fn g1_scalar_mul(scalar: &[u8; 32], p: &G1) -> G1 {
    let mut acc = g1_identity();
    for i in 0..256 {
        acc = g1_add(&acc, &acc);
        let byte = scalar[i / 8];
        let bit = ((byte >> (7 - (i % 8))) & 1) as u64;
        let sum = g1_add(&acc, p);
        acc = g1_cmov(&acc, &sum, bit);
    }
    acc
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Projective equality via cross-multiplication:
    /// X1*Z2 == X2*Z1 and Y1*Z2 == Y2*Z1, identities handled separately.
    fn g1_eq(p: &G1, q: &G1) -> bool {
        let pi = g1_is_identity(p);
        let qi = g1_is_identity(q);
        if pi || qi {
            return pi == qi;
        }
        let mut l = Fp([0u64; 4]);
        let mut r = Fp([0u64; 4]);
        fp_mul(&mut l, &p.x, &q.z);
        fp_mul(&mut r, &q.x, &p.z);
        if l.0 != r.0 {
            return false;
        }
        fp_mul(&mut l, &p.y, &q.z);
        fp_mul(&mut r, &q.y, &p.z);
        l.0 == r.0
    }

    /// 32-byte big-endian scalar from a small u64.
    fn scalar_from_u64(k: u64) -> [u8; 32] {
        let mut s = [0u8; 32];
        s[24..32].copy_from_slice(&k.to_be_bytes());
        s
    }

    /// Checked 256-bit big-endian addition; panics on overflow.
    fn scalar_add_be(a: &[u8; 32], b: &[u8; 32]) -> [u8; 32] {
        let mut out = [0u8; 32];
        let mut carry = 0u16;
        for i in (0..32).rev() {
            let s = a[i] as u16 + b[i] as u16 + carry;
            out[i] = s as u8;
            carry = s >> 8;
        }
        assert_eq!(carry, 0, "256-bit scalar addition overflowed");
        out
    }

    /// n as 32 big-endian bytes, from N_CANON.
    fn order_be_bytes() -> [u8; 32] {
        let mut s = [0u8; 32];
        for (limb_i, limb) in N_CANON.iter().enumerate() {
            let be = limb.to_be_bytes();
            let start = 32 - 8 * (limb_i + 1);
            s[start..start + 8].copy_from_slice(&be);
        }
        s
    }

    #[test]
    fn generator_on_curve() {
        let gx = to_mont(GX_CANON);
        let gy = to_mont(GY_CANON);
        assert!(
            g1_affine_on_curve(&gx, &gy),
            "G = (Gx, Gy) does not satisfy y^2 = x^3 - 3x + b"
        );
    }

    #[test]
    fn order_times_generator_is_identity() {
        let g = g1_generator();
        let ng = g1_scalar_mul(&order_be_bytes(), &g);
        assert!(g1_is_identity(&ng), "n * G is not the identity");
    }

    #[test]
    fn double_matches_scalar_two() {
        let g = g1_generator();
        let dbl = g1_add(&g, &g);
        let two_g = g1_scalar_mul(&scalar_from_u64(2), &g);
        assert!(g1_eq(&dbl, &two_g));
        // and the g1_double wrapper
        assert!(g1_eq(&g1_double(&g), &two_g));
    }

    #[test]
    fn scalar_distributes_small() {
        // 3G + 5G = 8G
        let g = g1_generator();
        let g3 = g1_scalar_mul(&scalar_from_u64(3), &g);
        let g5 = g1_scalar_mul(&scalar_from_u64(5), &g);
        let g8 = g1_scalar_mul(&scalar_from_u64(8), &g);
        assert!(g1_eq(&g1_add(&g3, &g5), &g8));
    }

    #[test]
    fn scalar_distributes_large() {
        // Two fixed pseudo-random 256-bit scalars with small top bytes so
        // k1 + k2 < n (n starts 0xffffffff...); the sum is computed by a
        // checked big-int addition, so no reduction mod n is involved.
        let k1: [u8; 32] = [
            0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc, 0xde, 0xf0, 0x0f, 0x1e, 0x2d, 0x3c, 0x4b, 0x5a,
            0x69, 0x78, 0x87, 0x96, 0xa5, 0xb4, 0xc3, 0xd2, 0xe1, 0xf0, 0x01, 0x23, 0x45, 0x67,
            0x89, 0xab, 0xcd, 0xef,
        ];
        let k2: [u8; 32] = [
            0x0f, 0xed, 0xcb, 0xa9, 0x87, 0x65, 0x43, 0x21, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66,
            0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff, 0x00, 0xfe, 0xdc, 0xba, 0x98,
            0x76, 0x54, 0x32, 0x10,
        ];
        let ksum = scalar_add_be(&k1, &k2);
        // sanity: top byte 0x12 + 0x0f < 0xff, so ksum < n
        let g = g1_generator();
        let p1 = g1_scalar_mul(&k1, &g);
        let p2 = g1_scalar_mul(&k2, &g);
        let psum = g1_scalar_mul(&ksum, &g);
        assert!(g1_eq(&g1_add(&p1, &p2), &psum));
    }

    #[test]
    fn add_commutative_and_associative() {
        let g = g1_generator();
        let p = g1_scalar_mul(&scalar_from_u64(2), &g);
        let q = g1_scalar_mul(&scalar_from_u64(3), &g);
        let r = g1_scalar_mul(&scalar_from_u64(5), &g);
        // commutativity
        assert!(g1_eq(&g1_add(&p, &q), &g1_add(&q, &p)));
        assert!(g1_eq(&g1_add(&q, &r), &g1_add(&r, &q)));
        // associativity
        let lhs = g1_add(&g1_add(&p, &q), &r);
        let rhs = g1_add(&p, &g1_add(&q, &r));
        assert!(g1_eq(&lhs, &rhs));
    }

    #[test]
    fn identity_laws() {
        let g = g1_generator();
        let p = g1_scalar_mul(&scalar_from_u64(7), &g);
        let o = g1_identity();
        // P + O = P (both orders; the formula is complete)
        assert!(g1_eq(&g1_add(&p, &o), &p));
        assert!(g1_eq(&g1_add(&o, &p), &p));
        // P + (-P) = O
        assert!(g1_is_identity(&g1_add(&p, &g1_neg(&p))));
        // to_affine round-trips through from_affine
        let (ax, ay) = g1_to_affine(&p).expect("7G is not the identity");
        assert!(g1_affine_on_curve(&ax, &ay));
        assert!(g1_eq(&g1_from_affine(&ax, &ay), &p));
    }
}
