//! P-521 elliptic-curve group operations (hand-written, unverified).
//!
//! Curve: y^2 = x^3 + a*x + b over GF(p), p = 2^521 - 1, a = -3 mod p.
//! Points are homogeneous projective (X : Y : Z); identity = (0 : 1 : 0).
//!
//! Point addition is a transcription of the Renes-Costello-Batina 2015
//! complete addition formula for general `a` (40 field operations), taken
//! op-for-op from the Qed-proved bedrock2 body in
//! `src/Bedrock/Curve/P256_G1_Add_Spec.v` (the op sequence is
//! curve-generic; only the constants a and 3b differ).
//!
//! Field-arithmetic discipline: the fiat-rust P-521 leaves use an
//! unsaturated Solinas representation with tight/loose limb bounds.
//! All group code below is written over tight-to-tight helpers that
//! carry after every add/sub and relax tight inputs before every mul,
//! so loose bounds are never chained.  This is conservative (extra
//! carries) and unverified; correctness over speed.
//!
//! Scalar representation: 66 little-endian bytes (`Scalar = [u8; 66]`);
//! scalar multiplication processes all 521 bits MSB-first with a
//! limb-mask conditional select and no secret-dependent branches.

use crate::{
    fp_add, fp_carry, fp_carry_mul, fp_carry_square, fp_from_bytes, fp_inv, fp_opp, fp_relax,
    fp_sub, fp_to_bytes, FpL, FpT,
};

// ---------------------------------------------------------------------------
// Tight-to-tight field helpers
// ---------------------------------------------------------------------------

#[inline]
fn zero_l() -> FpL {
    FpL([0u64; 9])
}

#[inline]
pub fn zero_t() -> FpT {
    FpT([0u64; 9])
}

/// a + b, carried back to tight bounds.
#[inline]
pub fn add_t(a: &FpT, b: &FpT) -> FpT {
    let mut l = zero_l();
    fp_add(&mut l, a, b);
    let mut t = zero_t();
    fp_carry(&mut t, &l);
    t
}

/// a - b, carried back to tight bounds.
#[inline]
pub fn sub_t(a: &FpT, b: &FpT) -> FpT {
    let mut l = zero_l();
    fp_sub(&mut l, a, b);
    let mut t = zero_t();
    fp_carry(&mut t, &l);
    t
}

/// -a, carried back to tight bounds.
#[inline]
pub fn opp_t(a: &FpT) -> FpT {
    let mut l = zero_l();
    fp_opp(&mut l, a);
    let mut t = zero_t();
    fp_carry(&mut t, &l);
    t
}

/// a * b (relax both tight inputs, carry_mul).
#[inline]
pub fn mul_t(a: &FpT, b: &FpT) -> FpT {
    let mut la = zero_l();
    let mut lb = zero_l();
    fp_relax(&mut la, a);
    fp_relax(&mut lb, b);
    let mut t = zero_t();
    fp_carry_mul(&mut t, &la, &lb);
    t
}

/// a^2 (relax, carry_square).
#[inline]
pub fn square_t(a: &FpT) -> FpT {
    let mut la = zero_l();
    fp_relax(&mut la, a);
    let mut t = zero_t();
    fp_carry_square(&mut t, &la);
    t
}

/// Canonical byte encoding (limb representations are not canonical).
#[inline]
pub fn to_bytes_t(a: &FpT) -> [u8; 66] {
    let mut bs = [0u8; 66];
    fp_to_bytes(&mut bs, a);
    bs
}

/// Field equality via canonical bytes.  NOT constant-time; test/support use.
#[inline]
pub fn eq_t(a: &FpT, b: &FpT) -> bool {
    to_bytes_t(a) == to_bytes_t(b)
}

#[inline]
pub fn is_zero_t(a: &FpT) -> bool {
    to_bytes_t(a) == [0u8; 66]
}

/// Field element from a small u64.
pub fn fp_from_u64(x: u64) -> FpT {
    let mut bs = [0u8; 66];
    bs[..8].copy_from_slice(&x.to_le_bytes());
    let mut t = zero_t();
    fp_from_bytes(&mut t, &bs);
    t
}

/// Parse a big-endian hex string (up to 132 hex digits) into 66
/// little-endian bytes.
pub fn be_hex_to_le_bytes(hex: &str) -> [u8; 66] {
    assert!(hex.len() <= 132 && hex.len() % 2 == 0, "bad hex length");
    let mut out = [0u8; 66];
    let nbytes = hex.len() / 2;
    let bytes = hex.as_bytes();
    let nyb = |c: u8| -> u8 {
        match c {
            b'0'..=b'9' => c - b'0',
            b'a'..=b'f' => c - b'a' + 10,
            b'A'..=b'F' => c - b'A' + 10,
            _ => panic!("bad hex digit"),
        }
    };
    for i in 0..nbytes {
        // hex byte i (big-endian) -> LE position nbytes-1-i
        let hi = nyb(bytes[2 * i]);
        let lo = nyb(bytes[2 * i + 1]);
        out[nbytes - 1 - i] = (hi << 4) | lo;
    }
    out
}

/// Field element from big-endian hex (standard notation).
pub fn fp_from_be_hex(hex: &str) -> FpT {
    let bs = be_hex_to_le_bytes(hex);
    let mut t = zero_t();
    fp_from_bytes(&mut t, &bs);
    t
}

// ---------------------------------------------------------------------------
// Curve constants (FIPS 186-4 / SEC2 "P-521" = secp521r1)
// ---------------------------------------------------------------------------

/// b coefficient, big-endian standard hex (FIPS 186-4 D.1.2.5).
pub const B_HEX: &str = "0051953eb9618e1c9a1f929a21a0b68540eea2da725b99b315f3b8b489918ef109e156193951ec7e937b1652c0bd3bb1bf073573df883d2c34f1ef451fd46b503f00";

/// Base-point x coordinate, big-endian standard hex.
pub const GX_HEX: &str = "00c6858e06b70404e9cd9e3ecb662395b4429c648139053fb521f828af606b4d3dbaa14b5e77efe75928fe1dc127a2ffa8de3348b3c1856a429bf97e7e31c2e5bd66";

/// Base-point y coordinate, big-endian standard hex.
pub const GY_HEX: &str = "011839296a789a3bc0045c8a5fb42c7d1bd998f54449579b446817afbd17273e662c97ee72995ef42640c550b9013fad0761353c7086a272c24088be94769fd16650";

/// Group order n, big-endian standard hex.
pub const N_HEX: &str = "01fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa51868783bf2f966b7fcc0148f709a5d03bb5c9b8899c47aebb6fb71e91386409";

/// a = -3 mod p.
pub fn const_a() -> FpT {
    opp_t(&fp_from_u64(3))
}

/// b.
pub fn const_b() -> FpT {
    fp_from_be_hex(B_HEX)
}

/// 3*b mod p.
pub fn const_b3() -> FpT {
    let b = const_b();
    add_t(&add_t(&b, &b), &b)
}

/// Group order as 66 little-endian bytes (scalar form).
pub fn order_le_bytes() -> [u8; 66] {
    be_hex_to_le_bytes(N_HEX)
}

// ---------------------------------------------------------------------------
// Projective group
// ---------------------------------------------------------------------------

/// Homogeneous projective point (X : Y : Z); identity = (0 : 1 : 0).
#[derive(Clone, Copy)]
pub struct G1 {
    pub x: FpT,
    pub y: FpT,
    pub z: FpT,
}

/// The identity element (0 : 1 : 0).
pub fn g1_identity() -> G1 {
    G1 {
        x: zero_t(),
        y: fp_from_u64(1),
        z: zero_t(),
    }
}

/// The standard base point G in projective coordinates (Z = 1).
pub fn g1_generator() -> G1 {
    G1 {
        x: fp_from_be_hex(GX_HEX),
        y: fp_from_be_hex(GY_HEX),
        z: fp_from_u64(1),
    }
}

pub fn g1_neg(p: &G1) -> G1 {
    G1 {
        x: p.x,
        y: opp_t(&p.y),
        z: p.z,
    }
}

/// Identity test: Z == 0 (all valid points with Z = 0 are the identity
/// class (0 : Y : 0)).  NOT constant-time; test/support use.
pub fn g1_is_identity(p: &G1) -> bool {
    is_zero_t(&p.z)
}

/// Complete projective point addition, Renes-Costello-Batina 2015
/// Algorithm 1 (general a), transcribed from the Qed-proved bedrock2 op
/// sequence in `src/Bedrock/Curve/P256_G1_Add_Spec.v` (40 field ops).
/// Complete: valid for all inputs, including P = Q and the identity.
pub fn g1_add(p: &G1, q: &G1) -> G1 {
    let a = const_a();
    let b3 = const_b3();
    let (x1, y1, z1) = (&p.x, &p.y, &p.z);
    let (x2, y2, z2) = (&q.x, &q.y, &q.z);

    // Steps 1-18 (a-independent part)
    let mut t0 = mul_t(x1, x2); //  1: t0 = X1*X2
    let mut t1 = mul_t(y1, y2); //  2: t1 = Y1*Y2
    let mut t2 = mul_t(z1, z2); //  3: t2 = Z1*Z2
    let mut t3 = add_t(x1, y1); //  4: t3 = X1+Y1
    let mut t4 = add_t(x2, y2); //  5: t4 = X2+Y2
    t3 = mul_t(&t3, &t4); //        6: t3 = t3*t4
    t4 = add_t(&t0, &t1); //        7: t4 = t0+t1
    t3 = sub_t(&t3, &t4); //        8: t3 = t3-t4
    t4 = add_t(x1, z1); //          9: t4 = X1+Z1
    let mut t5 = add_t(x2, z2); // 10: t5 = X2+Z2
    t4 = mul_t(&t4, &t5); //       11: t4 = t4*t5
    t5 = add_t(&t0, &t2); //       12: t5 = t0+t2
    t4 = sub_t(&t4, &t5); //       13: t4 = t4-t5
    t5 = add_t(y1, z1); //         14: t5 = Y1+Z1
    let mut x3 = add_t(y2, z2); // 15: X3 = Y2+Z2
    t5 = mul_t(&t5, &x3); //       16: t5 = t5*X3
    x3 = add_t(&t1, &t2); //       17: X3 = t1+t2
    t5 = sub_t(&t5, &x3); //       18: t5 = t5-X3
    // Steps 19-24
    let mut z3 = mul_t(&a, &t4); //   19: Z3 = a*t4
    x3 = mul_t(&b3, &t2); //          20: X3 = 3b*t2
    z3 = add_t(&x3, &z3); //          21: Z3 = X3+Z3
    x3 = sub_t(&t1, &z3); //          22: X3 = t1-Z3
    z3 = add_t(&z3, &t1); //          23: Z3 = Z3+t1
    let mut y3 = mul_t(&x3, &z3); //  24: Y3 = X3*Z3
    // Steps 25-32
    t1 = add_t(&t0, &t0); //          25: t1 = t0+t0
    t1 = add_t(&t1, &t0); //          26: t1 = t1+t0
    t2 = mul_t(&a, &t2); //           27: t2 = a*t2
    t4 = mul_t(&b3, &t4); //          28: t4 = 3b*t4
    t1 = add_t(&t1, &t2); //          29: t1 = t1+t2
    t2 = sub_t(&t0, &t2); //          30: t2 = t0-t2
    t2 = mul_t(&a, &t2); //           31: t2 = a*t2
    t4 = add_t(&t4, &t2); //          32: t4 = t4+t2
    // Steps 33-40
    t0 = mul_t(&t1, &t4); //          33: t0 = t1*t4
    y3 = add_t(&y3, &t0); //          34: Y3 = Y3+t0
    t0 = mul_t(&t5, &t4); //          35: t0 = t5*t4
    x3 = mul_t(&t3, &x3); //          36: X3 = t3*X3
    x3 = sub_t(&x3, &t0); //          37: X3 = X3-t0
    t0 = mul_t(&t3, &t1); //          38: t0 = t3*t1
    z3 = mul_t(&t5, &z3); //          39: Z3 = t5*Z3
    z3 = add_t(&z3, &t0); //          40: Z3 = Z3+t0

    G1 { x: x3, y: y3, z: z3 }
}

/// Doubling via the complete addition formula.
pub fn g1_double(p: &G1) -> G1 {
    g1_add(p, p)
}

// ---------------------------------------------------------------------------
// Affine conversion and on-curve check
// ---------------------------------------------------------------------------

/// Projective -> affine.  Returns None for the identity (Z = 0).
/// Uses the constant-time divstep inverse; the zero test is not CT.
pub fn g1_to_affine(p: &G1) -> Option<(FpT, FpT)> {
    if is_zero_t(&p.z) {
        return None;
    }
    let mut zinv = zero_t();
    fp_inv(&mut zinv, &p.z);
    Some((mul_t(&p.x, &zinv), mul_t(&p.y, &zinv)))
}

/// Affine -> projective (Z = 1).
pub fn g1_from_affine(x: &FpT, y: &FpT) -> G1 {
    G1 {
        x: *x,
        y: *y,
        z: fp_from_u64(1),
    }
}

/// Affine on-curve check: y^2 == x^3 + a*x + b.
pub fn affine_is_on_curve(x: &FpT, y: &FpT) -> bool {
    let lhs = square_t(y);
    let x2 = square_t(x);
    let x3 = mul_t(&x2, x);
    let ax = mul_t(&const_a(), x);
    let rhs = add_t(&add_t(&x3, &ax), &const_b());
    eq_t(&lhs, &rhs)
}

// ---------------------------------------------------------------------------
// Constant-time scalar multiplication
// ---------------------------------------------------------------------------

/// Scalar: 66 little-endian bytes (bits 0..=520 are used; bits above 520
/// MUST be zero — callers pass reduced scalars < 2^521).
pub type Scalar = [u8; 66];

/// Constant-time conditional select over tight field elements:
/// mask = 0 -> a, mask = all-ones -> b.
#[inline]
fn fp_cmov(a: &FpT, b: &FpT, mask: u64) -> FpT {
    let mut r = zero_t();
    for i in 0..9 {
        r.0[i] = (a.0[i] & !mask) | (b.0[i] & mask);
    }
    r
}

#[inline]
fn g1_cmov(a: &G1, b: &G1, mask: u64) -> G1 {
    G1 {
        x: fp_cmov(&a.x, &b.x, mask),
        y: fp_cmov(&a.y, &b.y, mask),
        z: fp_cmov(&a.z, &b.z, mask),
    }
}

/// Constant-time scalar multiplication: fixed-length MSB-first
/// double-and-add over all 521 scalar bits.  Every iteration performs
/// one complete doubling, one complete addition, and a limb-mask
/// conditional select; there are no secret-dependent branches or
/// memory accesses.  The complete RCB formula makes add(acc, base)
/// well-defined in every case (acc = identity, acc = base, ...).
pub fn g1_scalar_mul(k: &Scalar, p: &G1) -> G1 {
    let mut acc = g1_identity();
    // Bits 520 down to 0.
    for i in (0..521usize).rev() {
        acc = g1_double(&acc);
        let sum = g1_add(&acc, p);
        let bit = ((k[i / 8] >> (i % 8)) & 1) as u64;
        let mask = 0u64.wrapping_sub(bit);
        acc = g1_cmov(&acc, &sum, mask);
    }
    acc
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Projective-aware point equality via cross-multiplication:
    /// X1*Z2 == X2*Z1 and Y1*Z2 == Y2*Z1 (canonical-byte equality).
    fn g1_eq(p: &G1, q: &G1) -> bool {
        // Both-at-infinity fast path; mixed cases are handled soundly by
        // the cross-multiplication (Y*Z of the finite point is nonzero).
        if g1_is_identity(p) && g1_is_identity(q) {
            return true;
        }
        eq_t(&mul_t(&p.x, &q.z), &mul_t(&q.x, &p.z))
            && eq_t(&mul_t(&p.y, &q.z), &mul_t(&q.y, &p.z))
    }

    fn scalar_from_u64(x: u64) -> Scalar {
        let mut s = [0u8; 66];
        s[..8].copy_from_slice(&x.to_le_bytes());
        s
    }

    fn scalar_from_be_hex(hex: &str) -> Scalar {
        be_hex_to_le_bytes(hex)
    }

    /// Checked big-int addition of two 66-byte LE scalars; panics on
    /// carry out of 528 bits and asserts the sum stays below 2^521.
    fn scalar_add_checked(a: &Scalar, b: &Scalar) -> Scalar {
        let mut out = [0u8; 66];
        let mut carry = 0u16;
        for i in 0..66 {
            let s = a[i] as u16 + b[i] as u16 + carry;
            out[i] = (s & 0xff) as u8;
            carry = s >> 8;
        }
        assert_eq!(carry, 0, "scalar sum overflows 66 bytes");
        assert!(out[65] < 2, "scalar sum >= 2^521");
        out
    }

    #[test]
    fn generator_is_on_curve() {
        // Validates b, Gx, Gy jointly.
        let gx = fp_from_be_hex(GX_HEX);
        let gy = fp_from_be_hex(GY_HEX);
        assert!(affine_is_on_curve(&gx, &gy), "G not on curve");
    }

    #[test]
    fn order_times_generator_is_identity() {
        // Validates n together with add/double/scalar_mul.
        let g = g1_generator();
        let n = order_le_bytes();
        let ng = g1_scalar_mul(&n, &g);
        assert!(g1_is_identity(&ng), "n*G != identity");
    }

    #[test]
    fn add_g_g_equals_two_g() {
        let g = g1_generator();
        let gg = g1_add(&g, &g);
        let two_g = g1_scalar_mul(&scalar_from_u64(2), &g);
        assert!(g1_eq(&gg, &two_g), "G+G != 2*G");
        // And the result is on the curve.
        let (x, y) = g1_to_affine(&gg).expect("2G is not identity");
        assert!(affine_is_on_curve(&x, &y), "2G not on curve");
    }

    #[test]
    fn scalar_mul_distributes_over_scalar_addition() {
        let g = g1_generator();
        // Large fixed scalars kept below 2^512 so sums stay below 2^521.
        let big1 = scalar_from_be_hex(
            "7f0e1d2c3b4a59687766554433221100fedcba9876543210a5a5a5a5c3c3c3c3\
             0123456789abcdef0f1e2d3c4b5a69788796a5b4c3d2e1f000112233445566",
        );
        let big2 = scalar_from_be_hex(
            "10fedcba98765432a0b1c2d3e4f5061728394a5b6c7d8e9f0102030405060708\
             deadbeefcafebabe0011223344556677fedcfedcfedcfedc8899aabbccddee",
        );
        let pairs: [(Scalar, Scalar); 4] = [
            (scalar_from_u64(1), scalar_from_u64(1)),
            (scalar_from_u64(2), scalar_from_u64(3)),
            (scalar_from_u64(0x1234_5678_9abc_def0), scalar_from_u64(0xfeed_f00d_1234)),
            (big1, big2),
        ];
        for (k1, k2) in pairs.iter() {
            let sum = scalar_add_checked(k1, k2);
            let lhs = g1_scalar_mul(&sum, &g);
            let rhs = g1_add(&g1_scalar_mul(k1, &g), &g1_scalar_mul(k2, &g));
            assert!(g1_eq(&lhs, &rhs), "(k1+k2)*G != k1*G + k2*G");
        }
    }

    #[test]
    fn add_commutative_and_associative() {
        let g = g1_generator();
        let p = g1_scalar_mul(&scalar_from_u64(5), &g);
        let q = g1_scalar_mul(&scalar_from_u64(11), &g);
        let r = g1_scalar_mul(&scalar_from_u64(23), &g);
        // Commutativity
        assert!(g1_eq(&g1_add(&p, &q), &g1_add(&q, &p)), "P+Q != Q+P");
        // Associativity
        let lhs = g1_add(&g1_add(&p, &q), &r);
        let rhs = g1_add(&p, &g1_add(&q, &r));
        assert!(g1_eq(&lhs, &rhs), "(P+Q)+R != P+(Q+R)");
    }

    #[test]
    fn identity_laws() {
        let g = g1_generator();
        let p = g1_scalar_mul(&scalar_from_u64(7), &g);
        let o = g1_identity();
        // P + O = P
        assert!(g1_eq(&g1_add(&p, &o), &p), "P+O != P");
        assert!(g1_eq(&g1_add(&o, &p), &p), "O+P != P");
        // P + (-P) = O
        let sum = g1_add(&p, &g1_neg(&p));
        assert!(g1_is_identity(&sum), "P + (-P) != O");
        // O + O = O
        assert!(g1_is_identity(&g1_add(&o, &o)), "O+O != O");
    }

    #[test]
    fn affine_roundtrip() {
        let g = g1_generator();
        let p = g1_scalar_mul(&scalar_from_u64(9), &g);
        let (x, y) = g1_to_affine(&p).expect("9G is not identity");
        assert!(affine_is_on_curve(&x, &y), "9G affine not on curve");
        let p2 = g1_from_affine(&x, &y);
        assert!(g1_eq(&p, &p2), "affine roundtrip changed the point");
    }
}
