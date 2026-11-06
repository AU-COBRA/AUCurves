//! G1 and G2 group operations for BLS12-381 over the field tower of this crate.
//!
//! E : y² = x³ + 4 over Fp (G1) and E' : y² = x³ + 4(u + 1) over Fp2 (G2).
//! Field elements are in the Montgomery form of the tower (R = 2^384).
//!
//! Provenance, operation by operation:
//!
//! * G1 addition [`g1_add`] and doubling [`g1_double`] call Rocq-emitted
//!   safe Rust (`g1_msm_extracted.rs`) printed from the Rupicola-derived
//!   bedrock2 bodies `CurveAdd.ladderstep_body` (RCB 2015 Algorithm 7, the
//!   complete a = 0 addition; `ladderstep_correct`, Qed) and
//!   `PointDoubleA0.rcb_double_a0_body` (Algorithm 9; `rcb_double_a0_correct`,
//!   Qed).  These are complete homogeneous formulas, so [`G1Projective`] is
//!   homogeneous: (x, y) = (X/Z, Y/Z), identity (0 : 1 : 0).  The printer
//!   (`src/Bedrock/ToSafeRustArena.v`) is trusted, not proved.
//! * G1 multi-scalar multiplication [`g1_msm`] calls the emitted bedrock2
//!   Pippenger `msm_bls12`.  `BLS12_MSM_Closed.msm_bls12_closed` (Qed, closed
//!   under the global context) covers exactly the emitted functions: on n
//!   points satisfying y^2 z = x^3 + 4 z^3 (not (0:0:0)) with tight
//!   coordinates and n scalars of four 64-bit limbs, the result is
//!   projectively equal to sum k_i P_i (k_i the 256-bit limb integer, the sum
//!   formed with the RCB addition, which is fiat-crypto's `Projective.add`).
//!   Its premises are the contracts of the field leaves the runtime supplies
//!   (`bls12_mul/add/sub`: fiat-crypto `spec_of_BinOp`; `bls12_zero/one`:
//!   `spec_of_store_const`).  The printer stays trusted.  Also tested against
//!   blst (`tests/msm_vs_blst.rs`).
//! * G1 scalar multiplication [`g1_scalar_mul`] calls the emitted bedrock2
//!   `g1_scalar_mul` (double-and-add, most significant bit first, over the
//!   same copy-out wrappers as the MSM).  `BLS12_MSM_Closed.g1_scalar_mul_closed`
//!   (Qed, closed) proves that for an on-curve P with tight coordinates the
//!   result is projectively equal to kP, k the 256-bit limb integer; same
//!   premises and trusted printer as the MSM.  [`g1_scalar_mul_loop`] keeps
//!   the previous hand-written loop over the emitted addition/doubling.
//! * G2 addition [`g2_add`] and doubling [`g2_double`] call Rocq-emitted safe
//!   Rust (`g2_extracted.rs`) printed from the same two RCB formulas derived by
//!   Rupicola over an abstract field and instantiated at Fp2
//!   (`CurveAddAF.af_curve_add_body` / `af_curve_double_body`).
//!   `BLS12_G2_Closed.g2_curve_add_closed` and `g2_curve_double_closed` (Qed,
//!   closed under the global context) prove that, for points on E'(Fp2) with
//!   reduced coordinates, the emitted functions return exactly (Leibniz
//!   equality of the coordinate triples) fiat-crypto's complete projective
//!   addition `Projective.add P Q` (resp. `P P`) on the twist.  Premises: the
//!   contracts of the Fp2 leaves `bls12_Fp2_mul/add/sub` the runtime supplies.
//!   [`G2Projective`] is therefore homogeneous, identity (0 : 1 : 0).
//! * G2 scalar multiplication [`g2_scalar_mul`] calls the emitted bedrock2
//!   `g2_scalar_mul` (double-and-add over in-place emitted add/double);
//!   `BLS12_G2_ScalarMul.g2_scalar_mul_closed` (Qed, closed) proves the result
//!   projectively equal to kP for on-curve P.  [`g2_scalar_mul_loop`] keeps a
//!   hand-written loop over the emitted add/double (benchmark, test oracle).
//! * [`handwritten`] keeps the previous unverified Jacobian G1 and G2 code,
//!   for benchmarks and as a test oracle.
//!
//! Everything is checked against `blst` in `tests/group_vs_blst.rs` (G2 in
//! more depth in `tests/g2_vs_blst.rs`).
//! Scalar multiplication branches on the scalar and is not constant time.

use crate::{fp2_add, fp2_mul, fp2_sub, fp_add, fp_mul, fp_square, fp_sub, Fp, Fp2};
use crate::bedrock_rt::{Mem, FE, FE2};
use crate::g1_msm_extracted as emitted;
use crate::g2_extracted as emitted2;

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

/// G1 point in homogeneous projective coordinates: (x, y) = (X/Z, Y/Z);
/// Z = 0 is the identity, represented as (0 : 1 : 0).  (Before the switch to
/// the emitted complete formulas this type was Jacobian; the old code is
/// [`handwritten::G1Jacobian`].)  Coordinates must be reduced (< p), as every
/// value produced by the tower is.
#[derive(Clone, Copy, Debug)]
pub struct G1Projective { pub x: Fp, pub y: Fp, pub z: Fp }

/// G2 point in homogeneous projective coordinates over Fp2: (x, y) = (X/Z, Y/Z);
/// Z = 0 is the identity, represented as (0 : 1 : 0).  (Before the switch to
/// the emitted complete formulas this type was Jacobian; the old code is
/// [`handwritten::G2Jacobian`].)  Coordinates must be reduced (< p).
#[derive(Clone, Copy, Debug)]
pub struct G2Projective { pub x: Fp2, pub y: Fp2, pub z: Fp2 }

pub fn g1_generator() -> G1Affine { G1Affine { x: G1_GEN_X, y: G1_GEN_Y } }
pub fn g2_generator() -> G2Affine { G2Affine { x: G2_GEN_X, y: G2_GEN_Y } }

impl G1Projective {
    pub fn identity() -> Self { G1Projective { x: Fp([0; 6]), y: FP_ONE, z: Fp([0; 6]) } }
    pub fn is_identity(&self) -> bool { self.z == Fp([0; 6]) }
    pub fn from_affine(p: &G1Affine) -> Self { G1Projective { x: p.x, y: p.y, z: FP_ONE } }

    /// `None` for the identity.
    pub fn to_affine(&self) -> Option<G1Affine> {
        if self.is_identity() { return None; }
        let mut zi = Fp::zero();
        fp_inv(&mut zi, &self.z);
        let (mut x, mut y) = (Fp::zero(), Fp::zero());
        fp_mul(&mut x, &self.x, &zi);
        fp_mul(&mut y, &self.y, &zi);
        Some(G1Affine { x, y })
    }
}

// ---- G1 through the emitted bedrock2 code ----

/// Fresh 3-felem region X ‖ Y ‖ Z holding `p`.
fn put_g1(m: &mut Mem, p: &G1Projective) -> u64 {
    let a = m.alloc(3 * FE);
    m.write_fp(a, &p.x);
    m.write_fp(a + FE, &p.y);
    m.write_fp(a + 2 * FE, &p.z);
    a
}

fn get_g1(m: &Mem, a: u64) -> G1Projective {
    G1Projective { x: m.read_fp(a), y: m.read_fp(a + FE), z: m.read_fp(a + 2 * FE) }
}

/// out := p + q with the emitted `curve_add` (argument order
/// X1 X2 Y1 Y2 Z1 Z2 Xout Yout Zout; output disjoint from the inputs).
#[inline]
fn em_add(m: &mut Mem, out: u64, p: u64, q: u64) {
    emitted::curve_add(m, p, q, p + FE, q + FE, p + 2 * FE, q + 2 * FE,
                       out, out + FE, out + 2 * FE);
}

/// out := 2p with the emitted `curve_double_a0` (output disjoint from input).
#[inline]
fn em_double(m: &mut Mem, out: u64, p: u64) {
    emitted::curve_double_a0(m, p, p + FE, p + 2 * FE, out, out + FE, out + 2 * FE);
}

/// R = P + Q: emitted RCB Algorithm 7 (complete, no special cases).
pub fn g1_add(r: &mut G1Projective, p: &G1Projective, q: &G1Projective) {
    let mut m = Mem::with_capacity(2048);
    let (pa, qa) = (put_g1(&mut m, p), put_g1(&mut m, q));
    let ra = put_g1(&mut m, &G1Projective::identity());
    em_add(&mut m, ra, pa, qa);
    *r = get_g1(&m, ra);
}

/// R = 2P: emitted RCB Algorithm 9 (complete).
pub fn g1_double(r: &mut G1Projective, p: &G1Projective) {
    let mut m = Mem::with_capacity(2048);
    let pa = put_g1(&mut m, p);
    let ra = put_g1(&mut m, &G1Projective::identity());
    em_double(&mut m, ra, pa);
    *r = get_g1(&m, ra);
}

/// R = kP for a 256-bit little-endian scalar k (variable time: the loop
/// branches on the bits of k), with the emitted bedrock2 `g1_scalar_mul`
/// (double-and-add from the most significant bit).
///
/// Verification status: `BLS12_MSM_Closed.g1_scalar_mul_closed` (Qed, closed)
/// covers the emitted functions: for P on the curve with reduced coordinates
/// the output is projectively equal to kP (k the full 256-bit integer, not
/// reduced mod r).  Premises: the field-leaf contracts of the runtime.
pub fn g1_scalar_mul(r: &mut G1Projective, k: &[u64; 4], p: &G1Projective) {
    let mut m = Mem::with_capacity(1024);
    let out = put_g1(&mut m, &G1Projective::identity());
    let sc = m.alloc(32);
    for (j, w) in k.iter().enumerate() {
        m.store64(sc + 8 * j as u64, *w);
    }
    let pa = put_g1(&mut m, p);
    emitted::g1_scalar_mul(&mut m, out, out + FE, out + 2 * FE, sc, pa, pa + FE, pa + 2 * FE);
    *r = get_g1(&m, out);
}

/// R = kP with a hand-written double-and-add loop (least significant bit
/// first) over the emitted `curve_add` / `curve_double_a0`.  The loop is not
/// verified; kept for the benchmark and as a test oracle for
/// [`g1_scalar_mul`].
pub fn g1_scalar_mul_loop(r: &mut G1Projective, k: &[u64; 4], p: &G1Projective) {
    let mut m = Mem::with_capacity(4096);
    let mut acc = put_g1(&mut m, &G1Projective::identity());
    let mut acc_t = put_g1(&mut m, &G1Projective::identity());
    let mut base = put_g1(&mut m, p);
    let mut base_t = put_g1(&mut m, &G1Projective::identity());
    for i in 0..256 {
        if (k[i / 64] >> (i % 64)) & 1 == 1 {
            em_add(&mut m, acc_t, acc, base);
            core::mem::swap(&mut acc, &mut acc_t);
        }
        em_double(&mut m, base_t, base);
        core::mem::swap(&mut base, &mut base_t);
    }
    *r = get_g1(&m, acc);
}

/// Σ scalars[i] · points[i] with the emitted bedrock2 Pippenger `msm_bls12`
/// (window c = 9, 29 windows, 511 buckets; any 256-bit scalars).
///
/// Verification status: see the module documentation — the body is the
/// bedrock2 program covered by `BLS12_MSM_Closed.msm_bls12_closed` (Qed):
/// for on-curve inputs the output is projectively equal to the sum.
///
/// Panics if the slices differ in length.
pub fn g1_msm(r: &mut G1Projective, points: &[G1Projective], scalars: &[[u64; 4]]) {
    assert_eq!(points.len(), scalars.len(), "g1_msm: {} points, {} scalars", points.len(), scalars.len());
    let n = points.len() as u64;
    let mut m = Mem::with_capacity(points.len() * 176 + 80 * 1024);
    let out = put_g1(&mut m, &G1Projective::identity());
    let sc = m.alloc(32 * n.max(1));
    let px = m.alloc(FE * n.max(1));
    let py = m.alloc(FE * n.max(1));
    let pz = m.alloc(FE * n.max(1));
    for (i, (p, k)) in points.iter().zip(scalars).enumerate() {
        let i = i as u64;
        for (j, w) in k.iter().enumerate() {
            m.store64(sc + 32 * i + 8 * j as u64, *w);
        }
        m.write_fp(px + FE * i, &p.x);
        m.write_fp(py + FE * i, &p.y);
        m.write_fp(pz + FE * i, &p.z);
    }
    emitted::msm_bls12(&mut m, out, out + FE, out + 2 * FE, sc, px, py, pz, n);
    *r = get_g1(&m, out);
}

/// [`g1_msm`] on affine points.
pub fn g1_msm_affine(r: &mut G1Projective, points: &[G1Affine], scalars: &[[u64; 4]]) {
    let ps: Vec<G1Projective> = points.iter().map(G1Projective::from_affine).collect();
    g1_msm(r, &ps, scalars)
}

impl G2Projective {
    pub fn identity() -> Self { G2Projective { x: Fp2::zero(), y: FP2_ONE, z: Fp2::zero() } }
    pub fn is_identity(&self) -> bool { self.z == Fp2::zero() }
    pub fn from_affine(p: &G2Affine) -> Self { G2Projective { x: p.x, y: p.y, z: FP2_ONE } }

    /// `None` for the identity.
    pub fn to_affine(&self) -> Option<G2Affine> {
        if self.is_identity() { return None; }
        let mut zi = Fp2::zero();
        fp2_inv(&mut zi, &self.z);
        let (mut x, mut y) = (Fp2::zero(), Fp2::zero());
        fp2_mul(&mut x, &self.x, &zi);
        fp2_mul(&mut y, &self.y, &zi);
        Some(G2Affine { x, y })
    }
}

// ---- G2 through the emitted bedrock2 code ----

/// Fresh 3-element region X ‖ Y ‖ Z (Fp2 each) holding `p`.
fn put_g2(m: &mut Mem, p: &G2Projective) -> u64 {
    let a = m.alloc(3 * FE2);
    m.write_fp2(a, &p.x);
    m.write_fp2(a + FE2, &p.y);
    m.write_fp2(a + 2 * FE2, &p.z);
    a
}

fn get_g2(m: &Mem, a: u64) -> G2Projective {
    G2Projective { x: m.read_fp2(a), y: m.read_fp2(a + FE2), z: m.read_fp2(a + 2 * FE2) }
}

/// out := p + q with the emitted `g2_curve_add` (argument order
/// X1 X2 Y1 Y2 Z1 Z2 Xout Yout Zout; output disjoint from the inputs, as in
/// the precondition of `g2_curve_add_closed`).
#[inline]
fn em2_add(m: &mut Mem, out: u64, p: u64, q: u64) {
    emitted2::g2_curve_add(m, p, q, p + FE2, q + FE2, p + 2 * FE2, q + 2 * FE2,
                           out, out + FE2, out + 2 * FE2);
}

/// out := 2p with the emitted `g2_curve_double` (output disjoint from input).
#[inline]
fn em2_double(m: &mut Mem, out: u64, p: u64) {
    emitted2::g2_curve_double(m, p, p + FE2, p + 2 * FE2, out, out + FE2, out + 2 * FE2);
}

/// R = P + Q on G2: emitted RCB Algorithm 7 over Fp2 (complete, no special
/// cases).  `BLS12_G2_Closed.g2_curve_add_closed`: for on-curve P, Q with
/// reduced coordinates, R is fiat-crypto's `Projective.add P Q`.
pub fn g2_add(r: &mut G2Projective, p: &G2Projective, q: &G2Projective) {
    let mut m = Mem::with_capacity(4096);
    let (pa, qa) = (put_g2(&mut m, p), put_g2(&mut m, q));
    let ra = put_g2(&mut m, &G2Projective::identity());
    em2_add(&mut m, ra, pa, qa);
    *r = get_g2(&m, ra);
}

/// R = 2P on G2: emitted RCB Algorithm 9 over Fp2 (complete).
/// `BLS12_G2_Closed.g2_curve_double_closed`: R is `Projective.add P P`.
pub fn g2_double(r: &mut G2Projective, p: &G2Projective) {
    let mut m = Mem::with_capacity(4096);
    let pa = put_g2(&mut m, p);
    let ra = put_g2(&mut m, &G2Projective::identity());
    em2_double(&mut m, ra, pa);
    *r = get_g2(&m, ra);
}

/// R = kP on G2 with a hand-written double-and-add loop (least significant
/// bit first, variable time) over the emitted `g2_curve_add` /
/// `g2_curve_double`.  The loop itself is not verified.
pub fn g2_scalar_mul_loop(r: &mut G2Projective, k: &[u64; 4], p: &G2Projective) {
    let mut m = Mem::with_capacity(8192);
    let mut acc = put_g2(&mut m, &G2Projective::identity());
    let mut acc_t = put_g2(&mut m, &G2Projective::identity());
    let mut base = put_g2(&mut m, p);
    let mut base_t = put_g2(&mut m, &G2Projective::identity());
    for i in 0..256 {
        if (k[i / 64] >> (i % 64)) & 1 == 1 {
            em2_add(&mut m, acc_t, acc, base);
            core::mem::swap(&mut acc, &mut acc_t);
        }
        em2_double(&mut m, base_t, base);
        core::mem::swap(&mut base, &mut base_t);
    }
    *r = get_g2(&m, acc);
}

/// R = kP on G2 for a 256-bit little-endian scalar k (variable time: the
/// loop branches on the bits of k), with the emitted bedrock2 `g2_scalar_mul`
/// (double-and-add from the most significant bit, over the in-place emitted
/// `g2_curve_double_ip` / `g2_curve_add_ip`).
///
/// Verification status: `BLS12_G2_ScalarMul.g2_scalar_mul_closed` (Qed,
/// closed) covers the emitted functions: for P on E'(Fp2) with reduced
/// coordinates the output is projectively equal to kP (k the full 256-bit
/// integer, not reduced mod r).  Premises: the Fp2 leaf contracts.
pub fn g2_scalar_mul(r: &mut G2Projective, k: &[u64; 4], p: &G2Projective) {
    let mut m = Mem::with_capacity(4096);
    let out = put_g2(&mut m, &G2Projective::identity());
    let sc = m.alloc(32);
    for (j, w) in k.iter().enumerate() {
        m.store64(sc + 8 * j as u64, *w);
    }
    let pa = put_g2(&mut m, p);
    emitted2::g2_scalar_mul(&mut m, out, out + FE2, out + 2 * FE2, sc, pa, pa + FE2, pa + 2 * FE2);
    *r = get_g2(&m, out);
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


/// The previous hand-written G1 and G2 group laws (Jacobian coordinates, EFD
/// dbl-2009-l / add-2007-bl, double-and-add).  Not verified; kept for the
/// benchmark (`examples/bench_group.rs`) and as an independent test oracle.
pub mod handwritten {
    use super::*;

    /// G1 point in Jacobian coordinates: (x, y) = (X/Z², Y/Z³); Z = 0 is the identity.
    #[derive(Clone, Copy, Debug)]
    pub struct G1Jacobian { pub x: Fp, pub y: Fp, pub z: Fp }

    impl G1Jacobian {
        pub fn identity() -> Self { G1Jacobian { x: FP_ONE, y: FP_ONE, z: Fp([0; 6]) } }
        pub fn is_identity(&self) -> bool { self.z == Fp([0; 6]) }
        pub fn from_affine(p: &G1Affine) -> Self { G1Jacobian { x: p.x, y: p.y, z: FP_ONE } }

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

    jacobian_law!(Fp, G1Jacobian, Fp::zero(), fp_add, fp_sub, fp_mul,
                  g1j_double, g1j_add, g1j_scalar_mul);

    /// G2 point in Jacobian coordinates over Fp2: (x, y) = (X/Z², Y/Z³).
    #[derive(Clone, Copy, Debug)]
    pub struct G2Jacobian { pub x: Fp2, pub y: Fp2, pub z: Fp2 }

    impl G2Jacobian {
        pub fn identity() -> Self { G2Jacobian { x: FP2_ONE, y: FP2_ONE, z: Fp2::zero() } }
        pub fn is_identity(&self) -> bool { self.z == Fp2::zero() }
        pub fn from_affine(p: &G2Affine) -> Self { G2Jacobian { x: p.x, y: p.y, z: FP2_ONE } }

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

    jacobian_law!(Fp2, G2Jacobian, Fp2::zero(), fp2_add, fp2_sub, fp2_mul,
                  g2j_double, g2j_add, g2j_scalar_mul);
}

/// e(P, Q) for affine points, through the crate's pairing.
pub fn pairing_affine(out: &mut crate::Fp12, p: &G1Affine, q: &G2Affine) {
    crate::pairing(out, &p.x, &p.y, &q.x, &q.y)
}
