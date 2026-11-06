//! The emitted G2 group law (`group::g2_add` / `g2_double`, bedrock2
//! `g2_curve_add` / `g2_curve_double`, covered by
//! `BLS12_G2_Closed.g2_curve_add_closed` / `g2_curve_double_closed`) and the
//! G2 scalar multiplication against blst, and against the hand-written
//! Jacobian code: random points, the identity, P + P, P + (-P), inputs with
//! Z != 1.  Points are compared in affine form, limb for limb (both libraries
//! use Montgomery form with R = 2^384).

use blst::*;
use bls12_381::group::*;
use bls12_381::group::handwritten::*;
use bls12_381::{Fp, Fp2};

/// The group order r, little-endian.
const R: [u64; 4] = [
    0xffffffff00000001, 0x53bda402fffe5bfe, 0x3339d80809a1d805, 0x73eda753299d7d48,
];

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }
    fn scalar(&mut self) -> [u64; 4] { [self.next(), self.next(), self.next(), self.next()] }
    /// A random nonzero Fp2 element (in Montgomery form, reduced): k·G's x.
    fn fp2(&mut self) -> Fp2 {
        let (_, p) = blst_point(&self.scalar());
        p.x
    }
}

fn le_bytes(k: &[u64; 4]) -> [u8; 32] {
    let mut b = [0u8; 32];
    for (i, w) in k.iter().enumerate() {
        b[8 * i..8 * i + 8].copy_from_slice(&w.to_le_bytes());
    }
    b
}

fn fp2_of(x: &blst_fp2) -> Fp2 { Fp2 { c0: Fp(x.fp[0].l), c1: Fp(x.fp[1].l) } }

/// k·G2 with blst, as a blst point and as our projective point (Z = 1).
fn blst_point(k: &[u64; 4]) -> (blst_p2, G2Projective) {
    let (mut p, mut a) = (blst_p2::default(), blst_p2_affine::default());
    unsafe {
        blst_p2_mult(&mut p, blst_p2_generator(), le_bytes(k).as_ptr(), 256);
        blst_p2_to_affine(&mut a, &p);
    }
    let q = if unsafe { blst_p2_is_inf(&p) } {
        G2Projective::identity()
    } else {
        G2Projective::from_affine(&G2Affine { x: fp2_of(&a.x), y: fp2_of(&a.y) })
    };
    (p, q)
}

type Aff = Option<(Vec<u64>, Vec<u64>, Vec<u64>, Vec<u64>)>;

fn blst_aff(p: &blst_p2) -> Aff {
    let mut a = blst_p2_affine::default();
    unsafe {
        if blst_p2_is_inf(p) { return None; }
        blst_p2_to_affine(&mut a, p);
    }
    Some((a.x.fp[0].l.to_vec(), a.x.fp[1].l.to_vec(), a.y.fp[0].l.to_vec(), a.y.fp[1].l.to_vec()))
}

fn aff(p: &G2Projective) -> Aff {
    p.to_affine().map(|a| (a.x.c0.0.to_vec(), a.x.c1.0.to_vec(), a.y.c0.0.to_vec(), a.y.c1.0.to_vec()))
}

fn aff_j(p: &G2Jacobian) -> Aff {
    p.to_affine().map(|a| (a.x.c0.0.to_vec(), a.x.c1.0.to_vec(), a.y.c0.0.to_vec(), a.y.c1.0.to_vec()))
}

fn add(p: &G2Projective, q: &G2Projective) -> G2Projective {
    let mut r = G2Projective::identity();
    g2_add(&mut r, p, q);
    r
}

fn dbl(p: &G2Projective) -> G2Projective {
    let mut r = G2Projective::identity();
    g2_double(&mut r, p);
    r
}

fn neg(p: &G2Projective) -> G2Projective {
    let mut y = Fp2::zero();
    bls12_381::fp2_sub(&mut y, &Fp2::zero(), &p.y);
    G2Projective { x: p.x, y, z: p.z }
}

/// (λX : λY : λZ), the same projective point with Z != 1.
fn scale(p: &G2Projective, l: &Fp2) -> G2Projective {
    let (mut x, mut y, mut z) = (Fp2::zero(), Fp2::zero(), Fp2::zero());
    bls12_381::fp2_mul(&mut x, &p.x, l);
    bls12_381::fp2_mul(&mut y, &p.y, l);
    bls12_381::fp2_mul(&mut z, &p.z, l);
    G2Projective { x, y, z }
}

fn blst_add(p: &blst_p2, q: &blst_p2) -> blst_p2 {
    let mut r = blst_p2::default();
    unsafe { blst_p2_add_or_double(&mut r, p, q) };
    r
}

#[test]
fn random_additions_match_blst() {
    let mut rng = Rng(11);
    for _ in 0..32 {
        let (bp, p) = blst_point(&rng.scalar());
        let (bq, q) = blst_point(&rng.scalar());
        assert_eq!(aff(&add(&p, &q)), blst_aff(&blst_add(&bp, &bq)));
        // Inputs with Z != 1 give the same affine result.
        let (lp, lq) = (rng.fp2(), rng.fp2());
        assert_eq!(aff(&add(&scale(&p, &lp), &scale(&q, &lq))), blst_aff(&blst_add(&bp, &bq)));
    }
}

#[test]
fn random_doublings_match_blst() {
    let mut rng = Rng(12);
    for _ in 0..32 {
        let (bp, p) = blst_point(&rng.scalar());
        let mut bd = blst_p2::default();
        unsafe { blst_p2_double(&mut bd, &bp) };
        assert_eq!(aff(&dbl(&p)), blst_aff(&bd));
        // P + P with the (complete) addition equals 2P.
        assert_eq!(aff(&add(&p, &p)), blst_aff(&bd));
        let l = rng.fp2();
        assert_eq!(aff(&dbl(&scale(&p, &l))), blst_aff(&bd));
        assert_eq!(aff(&add(&scale(&p, &l), &p)), blst_aff(&bd));
    }
}

#[test]
fn identity_and_inverse() {
    let mut rng = Rng(13);
    let o = G2Projective::identity();
    assert!(add(&o, &o).is_identity());
    assert!(dbl(&o).is_identity());
    for _ in 0..16 {
        let (bp, p) = blst_point(&rng.scalar());
        assert_eq!(aff(&add(&p, &o)), blst_aff(&bp));
        assert_eq!(aff(&add(&o, &p)), blst_aff(&bp));
        // P + (-P) = O, also with differently scaled representatives.
        assert!(add(&p, &neg(&p)).is_identity());
        let l = rng.fp2();
        assert!(add(&scale(&p, &l), &neg(&p)).is_identity());
    }
}

#[test]
fn associativity_and_commutativity() {
    let mut rng = Rng(14);
    for _ in 0..8 {
        let (_, p) = blst_point(&rng.scalar());
        let (_, q) = blst_point(&rng.scalar());
        let (_, s) = blst_point(&rng.scalar());
        assert_eq!(aff(&add(&p, &q)), aff(&add(&q, &p)));
        assert_eq!(aff(&add(&add(&p, &q), &s)), aff(&add(&p, &add(&q, &s))));
    }
}

#[test]
fn agrees_with_handwritten_jacobian() {
    let mut rng = Rng(15);
    for _ in 0..16 {
        let (_, p) = blst_point(&rng.scalar());
        let (_, q) = blst_point(&rng.scalar());
        let (pa, qa) = (p.to_affine().unwrap(), q.to_affine().unwrap());
        let (pj, qj) = (G2Jacobian::from_affine(&pa), G2Jacobian::from_affine(&qa));
        let (mut sj, mut dj) = (G2Jacobian::identity(), G2Jacobian::identity());
        g2j_add(&mut sj, &pj, &qj);
        g2j_double(&mut dj, &pj);
        assert_eq!(aff(&add(&p, &q)), aff_j(&sj));
        assert_eq!(aff(&dbl(&p)), aff_j(&dj));
    }
}

#[test]
fn scalar_mul_agrees_with_loop_and_jacobian() {
    let mut rng = Rng(17);
    for _ in 0..8 {
        let (_, p) = blst_point(&rng.scalar());
        let k = rng.scalar();
        let (mut a, mut b) = (G2Projective::identity(), G2Projective::identity());
        g2_scalar_mul(&mut a, &k, &p);
        g2_scalar_mul_loop(&mut b, &k, &p);
        let mut c = G2Jacobian::identity();
        g2j_scalar_mul(&mut c, &k, &G2Jacobian::from_affine(&p.to_affine().unwrap()));
        assert_eq!(aff(&a), aff(&b));
        assert_eq!(aff(&a), aff_j(&c));
    }
    // The identity as input, and an input with Z != 1.
    let mut r = G2Projective::identity();
    g2_scalar_mul(&mut r, &rng.scalar(), &G2Projective::identity());
    assert!(r.is_identity());
    let (bp, p) = blst_point(&rng.scalar());
    let k = rng.scalar();
    let l = rng.fp2();
    g2_scalar_mul(&mut r, &k, &scale(&p, &l));
    let mut br = blst_p2::default();
    unsafe { blst_p2_mult(&mut br, &bp, le_bytes(&k).as_ptr(), 256) };
    assert_eq!(aff(&r), blst_aff(&br));
}

#[test]
fn scalar_mul_matches_blst() {
    let mut rng = Rng(16);
    for _ in 0..24 {
        let (bp, p) = blst_point(&rng.scalar());
        let k = rng.scalar();
        let mut r = G2Projective::identity();
        g2_scalar_mul(&mut r, &k, &p);
        let mut br = blst_p2::default();
        unsafe { blst_p2_mult(&mut br, &bp, le_bytes(&k).as_ptr(), 256) };
        assert_eq!(aff(&r), blst_aff(&br), "k = {:x?}", k);
    }
    // Edge scalars on the generator.
    let g = G2Projective::from_affine(&g2_generator());
    let mut r_plus_1 = R; r_plus_1[0] += 1;
    let mut r_minus_1 = R; r_minus_1[0] -= 1;
    for k in [[0u64; 4], R, [1, 0, 0, 0], [2, 0, 0, 0], r_minus_1, r_plus_1, [u64::MAX; 4], [0, 0, 0, 1 << 63]] {
        let mut r = G2Projective::identity();
        g2_scalar_mul(&mut r, &k, &g);
        let mut br = blst_p2::default();
        unsafe { blst_p2_mult(&mut br, blst_p2_generator(), le_bytes(&k).as_ptr(), 256) };
        assert_eq!(aff(&r), blst_aff(&br), "k = {:x?}", k);
    }
}
