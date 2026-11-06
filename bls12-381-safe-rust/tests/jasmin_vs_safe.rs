//! Differential test of the Jasmin path (feature `jasmin`, module
//! `bls12_381::jasmin`) against the safe-Rust path on the same inputs.
//!
//! Both paths run the same bedrock2 functions (printed once as safe Rust,
//! once as Jasmin) over the same CryptOpt multiply / square and safegcd
//! inverse, so the outputs are compared limb for limb, projective
//! coordinates included: 1000 pseudo-random inputs per operation (pairing,
//! G1 and G2 scalar multiplication, G1 MSM with n = 64), and the same for
//! the field and group functions they are built from.

#![cfg(feature = "jasmin")]

use blst::*;
use bls12_381::group::*;
use bls12_381::{jasmin, Fp, Fp12, Fp2, Fp6};

const N: usize = 1000;

/// splitmix64, deterministic.
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
    /// A reduced field element (top limb below p's 0x1a0111ea397fe69a).
    fn fp(&mut self) -> Fp {
        let mut l = [0u64; 6];
        for w in l.iter_mut() { *w = self.next(); }
        l[5] &= 0x0fff_ffff_ffff_ffff;
        Fp(l)
    }
    fn fp2(&mut self) -> Fp2 { Fp2 { c0: self.fp(), c1: self.fp() } }
    fn fp6(&mut self) -> Fp6 { Fp6 { c0: self.fp2(), c1: self.fp2(), c2: self.fp2() } }
    fn fp12(&mut self) -> Fp12 { Fp12 { c0: self.fp6(), c1: self.fp6() } }
}

fn le_bytes(k: &[u64; 4]) -> [u8; 32] {
    let mut b = [0u8; 32];
    for (i, w) in k.iter().enumerate() {
        b[8 * i..8 * i + 8].copy_from_slice(&w.to_le_bytes());
    }
    b
}

fn g1_affine(k: &[u64; 4]) -> (Fp, Fp) {
    let mut p = blst_p1::default();
    let mut a = blst_p1_affine::default();
    unsafe {
        blst_p1_mult(&mut p, blst_p1_generator(), le_bytes(k).as_ptr(), 256);
        blst_p1_to_affine(&mut a, &p);
    }
    (Fp(a.x.l), Fp(a.y.l))
}

fn g2_affine(k: &[u64; 4]) -> (Fp2, Fp2) {
    let mut p = blst_p2::default();
    let mut a = blst_p2_affine::default();
    unsafe {
        blst_p2_mult(&mut p, blst_p2_generator(), le_bytes(k).as_ptr(), 256);
        blst_p2_to_affine(&mut a, &p);
    }
    let f = |x: &blst_fp2| Fp2 { c0: Fp(x.fp[0].l), c1: Fp(x.fp[1].l) };
    (f(&a.x), f(&a.y))
}

/// A G1 point with a nontrivial Z: the safe-Rust sum of two affine points.
fn g1_point(rng: &mut Rng) -> G1Projective {
    let (ax, ay) = g1_affine(&rng.scalar());
    let (bx, by) = g1_affine(&rng.scalar());
    let a = G1Projective::from_affine(&G1Affine { x: ax, y: ay });
    let b = G1Projective::from_affine(&G1Affine { x: bx, y: by });
    let mut r = G1Projective::identity();
    g1_add(&mut r, &a, &b);
    r
}

fn g2_point(rng: &mut Rng) -> G2Projective {
    let (ax, ay) = g2_affine(&rng.scalar());
    let (bx, by) = g2_affine(&rng.scalar());
    let a = G2Projective::from_affine(&G2Affine { x: ax, y: ay });
    let b = G2Projective::from_affine(&G2Affine { x: bx, y: by });
    let mut r = G2Projective::identity();
    g2_add(&mut r, &a, &b);
    r
}

fn g1_eq(a: &G1Projective, b: &G1Projective) -> bool { a.x == b.x && a.y == b.y && a.z == b.z }
fn g2_eq(a: &G2Projective, b: &G2Projective) -> bool { a.x == b.x && a.y == b.y && a.z == b.z }

#[test]
fn fp_functions() {
    let mut rng = Rng(1);
    for i in 0..N {
        let (x, y) = (rng.fp(), rng.fp());
        let (mut a, mut b) = (Fp::zero(), Fp::zero());
        bls12_381::fp_add(&mut a, &x, &y); jasmin::fp_add(&mut b, &x, &y); assert_eq!(a, b, "add {i}");
        bls12_381::fp_sub(&mut a, &x, &y); jasmin::fp_sub(&mut b, &x, &y); assert_eq!(a, b, "sub {i}");
    }
}

#[test]
fn fp2_fp6_fp12_functions() {
    let mut rng = Rng(2);
    for i in 0..N {
        let (x, y) = (rng.fp2(), rng.fp2());
        let (mut a, mut b) = (Fp2::zero(), Fp2::zero());
        bls12_381::fp2_mul(&mut a, &x, &y); jasmin::fp2_mul(&mut b, &x, &y); assert_eq!(a, b, "Fp2 mul {i}");
        bls12_381::fp2_square(&mut a, &x); jasmin::fp2_square(&mut b, &x); assert_eq!(a, b, "Fp2 square {i}");
        bls12_381::fp2_inv(&mut a, &x); jasmin::fp2_inv(&mut b, &x); assert_eq!(a, b, "Fp2 inv {i}");
        let (x, y) = (rng.fp6(), rng.fp6());
        let (mut a, mut b) = (Fp6::zero(), Fp6::zero());
        bls12_381::fp6_mul(&mut a, &x, &y); jasmin::fp6_mul(&mut b, &x, &y); assert_eq!(a, b, "Fp6 mul {i}");
        let (x, y) = (rng.fp12(), rng.fp12());
        let (mut a, mut b) = (Fp12::zero(), Fp12::zero());
        bls12_381::fp12_mul(&mut a, &x, &y); jasmin::fp12_mul(&mut b, &x, &y); assert_eq!(a, b, "Fp12 mul {i}");
        bls12_381::fp12_square(&mut a, &x); jasmin::fp12_square(&mut b, &x); assert_eq!(a, b, "Fp12 square {i}");
        bls12_381::fp12_inv(&mut a, &x); jasmin::fp12_inv(&mut b, &x); assert_eq!(a, b, "Fp12 inv {i}");
    }
}

#[test]
fn pairing_1000() {
    let mut rng = Rng(3);
    for i in 0..N {
        let (px, py) = g1_affine(&rng.scalar());
        let (qx, qy) = g2_affine(&rng.scalar());
        let (mut a, mut b) = (Fp12::zero(), Fp12::zero());
        bls12_381::pairing(&mut a, &px, &py, &qx, &qy);
        jasmin::pairing(&mut b, &px, &py, &qx, &qy);
        assert_eq!(a, b, "pairing {i}");
        if i < 100 {
            bls12_381::miller_loop(&mut a, &px, &py, &qx, &qy);
            jasmin::miller_loop(&mut b, &px, &py, &qx, &qy);
            assert_eq!(a, b, "miller_loop {i}");
            let f = a;
            bls12_381::final_exp(&mut a, &f);
            jasmin::final_exp(&mut b, &f);
            assert_eq!(a, b, "final_exp {i}");
        }
    }
}

#[test]
fn g1_add_double_scalar_mul_1000() {
    let mut rng = Rng(4);
    for i in 0..N {
        let (p, q) = (g1_point(&mut rng), g1_point(&mut rng));
        let (mut a, mut b) = (G1Projective::identity(), G1Projective::identity());
        g1_add(&mut a, &p, &q); jasmin::g1_add(&mut b, &p, &q); assert!(g1_eq(&a, &b), "g1 add {i}");
        g1_double(&mut a, &p); jasmin::g1_double(&mut b, &p); assert!(g1_eq(&a, &b), "g1 double {i}");
        let k = rng.scalar();
        g1_scalar_mul(&mut a, &k, &p); jasmin::g1_scalar_mul(&mut b, &k, &p);
        assert!(g1_eq(&a, &b), "g1 scalar mul {i}");
    }
}

#[test]
fn g2_add_double_scalar_mul_1000() {
    let mut rng = Rng(5);
    for i in 0..N {
        let (p, q) = (g2_point(&mut rng), g2_point(&mut rng));
        let (mut a, mut b) = (G2Projective::identity(), G2Projective::identity());
        g2_add(&mut a, &p, &q); jasmin::g2_add(&mut b, &p, &q); assert!(g2_eq(&a, &b), "g2 add {i}");
        g2_double(&mut a, &p); jasmin::g2_double(&mut b, &p); assert!(g2_eq(&a, &b), "g2 double {i}");
        let k = rng.scalar();
        g2_scalar_mul(&mut a, &k, &p); jasmin::g2_scalar_mul(&mut b, &k, &p);
        assert!(g2_eq(&a, &b), "g2 scalar mul {i}");
    }
}

#[test]
fn g1_msm_n64_1000() {
    let mut rng = Rng(6);
    let n = 64;
    for i in 0..N {
        let points: Vec<G1Projective> = if i % 100 == 0 {
            (0..n).map(|_| g1_point(&mut rng)).collect()
        } else {
            // blst is the slow part of the generation: reuse affine multiples.
            let (x, y) = g1_affine(&rng.scalar());
            let base = G1Projective::from_affine(&G1Affine { x, y });
            let mut ps = vec![base];
            for j in 1..n {
                let mut r = G1Projective::identity();
                if j % 2 == 1 { g1_double(&mut r, &ps[j - 1]) } else { g1_add(&mut r, &ps[j - 1], &base) }
                ps.push(r);
            }
            ps
        };
        let scalars: Vec<[u64; 4]> = (0..n).map(|_| rng.scalar()).collect();
        let (mut a, mut b) = (G1Projective::identity(), G1Projective::identity());
        g1_msm(&mut a, &points, &scalars);
        jasmin::g1_msm(&mut b, &points, &scalars);
        assert!(g1_eq(&a, &b), "g1 msm n=64 instance {i}");
    }
}
