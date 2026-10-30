//! G1 and G2 group operations for BLS12-381: Jacobian addition, doubling and
//! double-and-add scalar multiplication, over the field tower of this crate.
//!
//! E : y² = x³ + 4 over Fp (G1) and E' : y² = x³ + 4(u + 1) over Fp2 (G2).
//! Field elements are in the Montgomery form of the tower (R = 2^384).
//!
//! The field operations are the verified leaves of this crate.  The group law
//! in this file is hand-written (EFD dbl-2009-l / add-2007-bl, ported from
//! `bls12-jasmin-rs`); it is not extracted from Rocq and is checked against
//! `blst` in `tests/group_vs_blst.rs`.  Scalar multiplication branches on the
//! scalar and is not constant time.

use crate::{fp2_add, fp2_mul, fp2_sub, fp_add, fp_mul, fp_square, fp_sub, Fp, Fp2};

/// Montgomery form of 1.
pub const FP_ONE: Fp = Fp([
    0x760900000002fffd, 0xebf4000bc40c0002, 0x5f48985753c758ba,
    0x77ce585370525745, 0x5c071a97a256ec6d, 0x15f65ec3fa80e493,
]);

/// Montgomery form of the curve coefficient b = 4.
pub const FP_B: Fp = Fp([
    0xaa270000000cfff3, 0x53cc0032fc34000a, 0x478fe97a6b0a807f,
    0xb1d37ebee6ba24d7, 0x8ec9733bbf78ab2f, 0x09d645513d83de7e,
]);

pub const FP2_ONE: Fp2 = Fp2 { c0: FP_ONE, c1: Fp([0; 6]) };

/// Twist coefficient b' = 4(u + 1).
pub const FP2_B_TWIST: Fp2 = Fp2 { c0: FP_B, c1: FP_B };

pub const G1_GEN_X: Fp = Fp([
    0x5cb38790fd530c16, 0x7817fc679976fff5, 0x154f95c7143ba1c1,
    0xf0ae6acdf3d0e747, 0xedce6ecc21dbf440, 0x120177419e0bfb75,
]);
pub const G1_GEN_Y: Fp = Fp([
    0xbaac93d50ce72271, 0x8c22631a7918fd8e, 0xdd595f13570725ce,
    0x51ac582950405194, 0x0e1c8c3fad0059c0, 0x0bbc3efc5008a26a,
]);

pub const G2_GEN_X: Fp2 = Fp2 {
    c0: Fp([0xf5f28fa202940a10, 0xb3f5fb2687b4961a, 0xa1a893b53e2ae580,
            0x9894999d1a3caee9, 0x6f67b7631863366b, 0x058191924350bcd7]),
    c1: Fp([0xa5a9c0759e23f606, 0xaaa0c59dbccd60c3, 0x3bb17e18e2867806,
            0x1b1ab6cc8541b367, 0xc2b6ed0ef2158547, 0x11922a097360edf3]),
};
pub const G2_GEN_Y: Fp2 = Fp2 {
    c0: Fp([0x4c730af860494c4a, 0x597cfa1f5e369c5a, 0xe7e6856caa0a635a,
            0xbbefb5e96e0d495f, 0x07d3a975f0ef25a2, 0x0083fd8e7e80dae5]),
    c1: Fp([0xadc0fc92df64b05d, 0x18aa270a2b1461dc, 0x86adac6a3be4eba0,
            0x79495c4ec93da33a, 0xe7175850a43ccaed, 0x0b2bc2a163de1bf2]),
};

/// Inverse in Fp, through the Fp2 inverse of (x, 0); the inverse of 0 is 0.
pub fn fp_inv(out: &mut Fp, x: &Fp) {
    let mut r = Fp2::zero();
    crate::fp2_inv(&mut r, &Fp2 { c0: *x, c1: Fp::zero() });
    *out = r.c0;
}

/// Inverse in Fp2; the inverse of 0 is 0.
pub fn fp2_inv(out: &mut Fp2, x: &Fp2) {
    crate::fp2_inv(out, x)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct G1Affine { pub x: Fp, pub y: Fp }

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct G2Affine { pub x: Fp2, pub y: Fp2 }

/// G1 point in Jacobian coordinates: (x, y) = (X/Z², Y/Z³); Z = 0 is the identity.
#[derive(Clone, Copy, Debug)]
pub struct G1Projective { pub x: Fp, pub y: Fp, pub z: Fp }

/// G2 point in Jacobian coordinates over Fp2.
#[derive(Clone, Copy, Debug)]
pub struct G2Projective { pub x: Fp2, pub y: Fp2, pub z: Fp2 }

pub fn g1_generator() -> G1Affine { G1Affine { x: G1_GEN_X, y: G1_GEN_Y } }
pub fn g2_generator() -> G2Affine { G2Affine { x: G2_GEN_X, y: G2_GEN_Y } }

impl G1Projective {
    pub fn identity() -> Self { G1Projective { x: FP_ONE, y: FP_ONE, z: Fp([0; 6]) } }
    pub fn is_identity(&self) -> bool { self.z == Fp([0; 6]) }
    pub fn from_affine(p: &G1Affine) -> Self { G1Projective { x: p.x, y: p.y, z: FP_ONE } }

    /// `None` for the identity.
    pub fn to_affine(&self) -> Option<G1Affine> {
        if self.is_identity() { return None; }
        let (mut zi, mut zi2, mut zi3) = (Fp::zero(), Fp::zero(), Fp::zero());
        fp_inv(&mut zi, &self.z);
        fp_square(&mut zi2, &zi);
        fp_mul(&mut zi3, &zi2, &zi);
        let (mut x, mut y) = (Fp::zero(), Fp::zero());
        fp_mul(&mut x, &self.x, &zi2);
        fp_mul(&mut y, &self.y, &zi3);
        Some(G1Affine { x, y })
    }
}

impl G2Projective {
    pub fn identity() -> Self { G2Projective { x: FP2_ONE, y: FP2_ONE, z: Fp2::zero() } }
    pub fn is_identity(&self) -> bool { self.z == Fp2::zero() }
    pub fn from_affine(p: &G2Affine) -> Self { G2Projective { x: p.x, y: p.y, z: FP2_ONE } }

    /// `None` for the identity.
    pub fn to_affine(&self) -> Option<G2Affine> {
        if self.is_identity() { return None; }
        let (mut zi, mut zi2, mut zi3) = (Fp2::zero(), Fp2::zero(), Fp2::zero());
        fp2_inv(&mut zi, &self.z);
        fp2_mul(&mut zi2, &zi, &zi);
        fp2_mul(&mut zi3, &zi2, &zi);
        let (mut x, mut y) = (Fp2::zero(), Fp2::zero());
        fp2_mul(&mut x, &self.x, &zi2);
        fp2_mul(&mut y, &self.y, &zi3);
        Some(G2Affine { x, y })
    }
}

/// The Jacobian formulas are the same over Fp and Fp2; `jacobian_law!`
/// instantiates them for one coordinate field.
macro_rules! jacobian_law {
    ($F:ty, $P:ident, $zero:expr, $add:ident, $sub:ident, $mul:ident,
     $double_fn:ident, $add_fn:ident, $smul_fn:ident) => {
        /// R = 2P (EFD dbl-2009-l, a = 0).
        pub fn $double_fn(r: &mut $P, p: &$P) {
            if p.is_identity() { *r = $P::identity(); return; }
            let z: $F = $zero;
            let (mut a, mut b, mut c, mut d) = (z, z, z, z);
            let (mut t0, mut t1, mut t2) = (z, z, z);
            $mul(&mut a, &p.y, &p.y);                       // A = Y²
            $mul(&mut t0, &p.x, &a);
            $add(&mut t1, &t0, &t0);
            $add(&mut b, &t1, &t1);                         // B = 4XA
            $mul(&mut t0, &a, &a);
            $add(&mut t1, &t0, &t0);
            $add(&mut t2, &t1, &t1);
            $add(&mut c, &t2, &t2);                         // C = 8A²
            $mul(&mut t0, &p.x, &p.x);
            $add(&mut t1, &t0, &t0);
            $add(&mut d, &t1, &t0);                         // D = 3X²
            let (mut x3, mut y3, mut z3) = (z, z, z);
            $mul(&mut t0, &d, &d);
            $add(&mut t1, &b, &b);
            $sub(&mut x3, &t0, &t1);                        // X3 = D² - 2B
            $sub(&mut t0, &b, &x3);
            $mul(&mut t1, &d, &t0);
            $sub(&mut y3, &t1, &c);                         // Y3 = D(B - X3) - C
            $mul(&mut t0, &p.y, &p.z);
            $add(&mut z3, &t0, &t0);                        // Z3 = 2YZ
            *r = $P { x: x3, y: y3, z: z3 };
        }

        /// R = P + Q (EFD add-2007-bl), with the doubling and inverse cases.
        pub fn $add_fn(r: &mut $P, p: &$P, q: &$P) {
            if p.is_identity() { *r = *q; return; }
            if q.is_identity() { *r = *p; return; }
            let z: $F = $zero;
            let (mut z1z1, mut z2z2, mut u1, mut u2, mut s1, mut s2) = (z, z, z, z, z, z);
            let (mut t0, mut t1) = (z, z);
            $mul(&mut z1z1, &p.z, &p.z);
            $mul(&mut z2z2, &q.z, &q.z);
            $mul(&mut u1, &p.x, &z2z2);                     // U1 = X1 Z2²
            $mul(&mut u2, &q.x, &z1z1);                     // U2 = X2 Z1²
            $mul(&mut t0, &q.z, &z2z2);
            $mul(&mut s1, &p.y, &t0);                       // S1 = Y1 Z2³
            $mul(&mut t0, &p.z, &z1z1);
            $mul(&mut s2, &q.y, &t0);                       // S2 = Y2 Z1³
            if u1 == u2 {
                if s1 == s2 { $double_fn(r, p); } else { *r = $P::identity(); }
                return;
            }
            let (mut h, mut i, mut j, mut rr, mut v) = (z, z, z, z, z);
            $sub(&mut h, &u2, &u1);                         // H = U2 - U1
            $add(&mut t0, &h, &h);
            $mul(&mut i, &t0, &t0);                         // I = (2H)²
            $mul(&mut j, &h, &i);                           // J = HI
            $sub(&mut t0, &s2, &s1);
            $add(&mut rr, &t0, &t0);                        // r = 2(S2 - S1)
            $mul(&mut v, &u1, &i);                          // V = U1 I
            let (mut x3, mut y3, mut z3) = (z, z, z);
            $mul(&mut t0, &rr, &rr);
            $sub(&mut t1, &t0, &j);
            $add(&mut t0, &v, &v);
            $sub(&mut x3, &t1, &t0);                        // X3 = r² - J - 2V
            $sub(&mut t0, &v, &x3);
            $mul(&mut t1, &rr, &t0);
            $mul(&mut t0, &s1, &j);
            let t2 = t0;
            $add(&mut t0, &t2, &t2);
            $sub(&mut y3, &t1, &t0);                        // Y3 = r(V - X3) - 2 S1 J
            $add(&mut t0, &p.z, &q.z);
            $mul(&mut t1, &t0, &t0);
            $sub(&mut t0, &t1, &z1z1);
            $sub(&mut t1, &t0, &z2z2);
            $mul(&mut z3, &t1, &h);                         // Z3 = ((Z1+Z2)² - Z1² - Z2²) H
            *r = $P { x: x3, y: y3, z: z3 };
        }

        /// R = kP for a 256-bit little-endian scalar (variable time).
        pub fn $smul_fn(r: &mut $P, k: &[u64; 4], p: &$P) {
            let mut acc = $P::identity();
            let mut base = *p;
            for i in 0..256 {
                if (k[i / 64] >> (i % 64)) & 1 == 1 {
                    let a = acc;
                    $add_fn(&mut acc, &a, &base);
                }
                let b = base;
                $double_fn(&mut base, &b);
            }
            *r = acc;
        }
    };
}

jacobian_law!(Fp, G1Projective, Fp::zero(), fp_add, fp_sub, fp_mul,
              g1_double, g1_add, g1_scalar_mul);
jacobian_law!(Fp2, G2Projective, Fp2::zero(), fp2_add, fp2_sub, fp2_mul,
              g2_double, g2_add, g2_scalar_mul);

/// e(P, Q) for affine points, through the crate's pairing.
pub fn pairing_affine(out: &mut crate::Fp12, p: &G1Affine, q: &G2Affine) {
    crate::pairing(out, &p.x, &p.y, &q.x, &q.y)
}
