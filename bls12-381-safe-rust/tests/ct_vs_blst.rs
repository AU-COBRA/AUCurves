//! The constant-time scalar multiplications `group::g1_scalar_mul_ct` /
//! `g2_scalar_mul_ct` (bedrock2 `g1_scalar_mul_ct` / `g2_scalar_mul_ct`,
//! covered by `BLS12_G1_CT_Closed.g1_scalar_mul_ct_closed` /
//! `BLS12_G2_ScalarMulCT.g2_scalar_mul_ct_closed`) against blst and against
//! the variable-time versions: random scalars and points, edge scalars,
//! the identity, inputs with Z != 1; and the `sk_to_pk` / `sign_hashed`
//! helpers against blst.  Affine comparison, limb for limb (both libraries
//! use Montgomery form with R = 2^384).

use blst::*;
use bls12_381::group::*;
use bls12_381::{Fp, Fp2};

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
}

fn le_bytes(k: &[u64; 4]) -> [u8; 32] {
    let mut b = [0u8; 32];
    for (i, w) in k.iter().enumerate() {
        b[8 * i..8 * i + 8].copy_from_slice(&w.to_le_bytes());
    }
    b
}

fn edge_scalars() -> Vec<[u64; 4]> {
    let mut rm1 = R; rm1[0] -= 1;
    let mut rp1 = R; rp1[0] += 1;
    vec![[0; 4], R, [1, 0, 0, 0], [2, 0, 0, 0], rm1, rp1, [u64::MAX; 4], [0, 0, 0, 1 << 63]]
}

// ---------------------------------------------------------------- G1

type Aff1 = Option<(Vec<u64>, Vec<u64>)>;

fn g1_blst_point(k: &[u64; 4]) -> (blst_p1, G1Projective) {
    let (mut p, mut a) = (blst_p1::default(), blst_p1_affine::default());
    unsafe {
        blst_p1_mult(&mut p, blst_p1_generator(), le_bytes(k).as_ptr(), 256);
        blst_p1_to_affine(&mut a, &p);
    }
    let q = if unsafe { blst_p1_is_inf(&p) } {
        G1Projective::identity()
    } else {
        G1Projective::from_affine(&G1Affine { x: Fp(a.x.l), y: Fp(a.y.l) })
    };
    (p, q)
}

fn g1_blst_mult(p: &blst_p1, k: &[u64; 4]) -> Aff1 {
    let (mut r, mut a) = (blst_p1::default(), blst_p1_affine::default());
    unsafe {
        blst_p1_mult(&mut r, p, le_bytes(k).as_ptr(), 256);
        if blst_p1_is_inf(&r) { return None; }
        blst_p1_to_affine(&mut a, &r);
    }
    Some((a.x.l.to_vec(), a.y.l.to_vec()))
}

fn aff1(p: &G1Projective) -> Aff1 { p.to_affine().map(|a| (a.x.0.to_vec(), a.y.0.to_vec())) }

fn g1ct(k: &[u64; 4], p: &G1Projective) -> G1Projective {
    let mut r = G1Projective::identity();
    g1_scalar_mul_ct(&mut r, k, p);
    r
}

#[test]
fn g1_ct_random_match_blst_and_vartime() {
    let mut rng = Rng(101);
    for _ in 0..24 {
        let (bp, p) = g1_blst_point(&rng.scalar());
        let k = rng.scalar();
        let c = aff1(&g1ct(&k, &p));
        assert_eq!(c, g1_blst_mult(&bp, &k), "k = {:x?}", k);
        let mut v = G1Projective::identity();
        g1_scalar_mul(&mut v, &k, &p);
        assert_eq!(c, aff1(&v));
    }
}

#[test]
fn g1_ct_edge_cases() {
    let (bg, g) = g1_blst_point(&[1, 0, 0, 0]);
    for k in edge_scalars() {
        assert_eq!(aff1(&g1ct(&k, &g)), g1_blst_mult(&bg, &k), "k = {:x?}", k);
    }
    assert!(g1ct(&[0; 4], &g).is_identity());
    assert!(g1ct(&R, &g).is_identity());
    assert!(g1ct(&[5, 6, 7, 8], &G1Projective::identity()).is_identity());
    // Z != 1 input: 3G from the emitted law.
    let mut g2 = G1Projective::identity();
    g1_double(&mut g2, &g);
    let mut g3 = G1Projective::identity();
    g1_add(&mut g3, &g2, &g);
    let k = [0x1234_5678_9abc_def0, 0x0fed_cba9_8765_4321, 3, 0];
    let mut b3 = blst_p1::default();
    unsafe { blst_p1_mult(&mut b3, &bg, le_bytes(&[3, 0, 0, 0]).as_ptr(), 256) };
    assert_eq!(aff1(&g1ct(&k, &g3)), g1_blst_mult(&b3, &k));
}

#[test]
fn sk_to_pk_matches_blst() {
    let mut rng = Rng(103);
    for _ in 0..8 {
        let mut sk = rng.scalar();
        sk[3] &= 0x3fff_ffff_ffff_ffff; // below r
        let pk = sk_to_pk(&sk);
        let (_, want) = g1_blst_point(&sk);
        assert_eq!(aff1(&pk), aff1(&want));
    }
}

// ---------------------------------------------------------------- G2

type Aff2 = Option<(Vec<u64>, Vec<u64>, Vec<u64>, Vec<u64>)>;

fn fp2_of(x: &blst_fp2) -> Fp2 { Fp2 { c0: Fp(x.fp[0].l), c1: Fp(x.fp[1].l) } }

fn g2_blst_point(k: &[u64; 4]) -> (blst_p2, G2Projective) {
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

fn g2_blst_mult(p: &blst_p2, k: &[u64; 4]) -> Aff2 {
    let (mut r, mut a) = (blst_p2::default(), blst_p2_affine::default());
    unsafe {
        blst_p2_mult(&mut r, p, le_bytes(k).as_ptr(), 256);
        if blst_p2_is_inf(&r) { return None; }
        blst_p2_to_affine(&mut a, &r);
    }
    Some((a.x.fp[0].l.to_vec(), a.x.fp[1].l.to_vec(), a.y.fp[0].l.to_vec(), a.y.fp[1].l.to_vec()))
}

fn aff2(p: &G2Projective) -> Aff2 {
    p.to_affine().map(|a| (a.x.c0.0.to_vec(), a.x.c1.0.to_vec(), a.y.c0.0.to_vec(), a.y.c1.0.to_vec()))
}

fn g2ct(k: &[u64; 4], p: &G2Projective) -> G2Projective {
    let mut r = G2Projective::identity();
    g2_scalar_mul_ct(&mut r, k, p);
    r
}

#[test]
fn g2_ct_random_match_blst_and_vartime() {
    let mut rng = Rng(201);
    for _ in 0..24 {
        let (bp, p) = g2_blst_point(&rng.scalar());
        let k = rng.scalar();
        let c = aff2(&g2ct(&k, &p));
        assert_eq!(c, g2_blst_mult(&bp, &k), "k = {:x?}", k);
        let mut v = G2Projective::identity();
        g2_scalar_mul(&mut v, &k, &p);
        assert_eq!(c, aff2(&v));
    }
}

#[test]
fn g2_ct_edge_cases() {
    let (bg, g) = g2_blst_point(&[1, 0, 0, 0]);
    for k in edge_scalars() {
        assert_eq!(aff2(&g2ct(&k, &g)), g2_blst_mult(&bg, &k), "k = {:x?}", k);
    }
    assert!(g2ct(&[5, 6, 7, 8], &G2Projective::identity()).is_identity());
    // Z != 1 input: 3G from the emitted law.
    let mut g2 = G2Projective::identity();
    g2_double(&mut g2, &g);
    let mut g3 = G2Projective::identity();
    g2_add(&mut g3, &g2, &g);
    let k = [0x1234_5678_9abc_def0, 0x0fed_cba9_8765_4321, 3, 0];
    let mut b3 = blst_p2::default();
    unsafe { blst_p2_mult(&mut b3, &bg, le_bytes(&[3, 0, 0, 0]).as_ptr(), 256) };
    assert_eq!(aff2(&g2ct(&k, &g3)), g2_blst_mult(&b3, &k));
}

#[test]
fn sign_hashed_matches_blst() {
    let mut rng = Rng(203);
    for _ in 0..4 {
        let mut sk = rng.scalar();
        sk[3] &= 0x3fff_ffff_ffff_ffff;
        let (bh, h) = g2_blst_point(&rng.scalar());
        assert_eq!(aff2(&sign_hashed(&sk, &h)), g2_blst_mult(&bh, &sk));
    }
}
