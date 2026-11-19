//! The emitted GLV Shamir scalar multiplication `group::g1_scalar_mul_glv`
//! (bedrock2 `bls12_glv_shamir`, covered by `BLS12_GLV_Closed.g1_glv_closed`)
//! against blst and against the emitted double-and-add `g1_scalar_mul`, on
//! random scalars and points of G1 and on edge cases; plus the hand-written
//! decomposition `glv_split` and the endomorphism constant.

use blst::*;
use bls12_381::group::*;
use bls12_381::{fp_mul, Fp};

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

fn blst_point(k: &[u64; 4]) -> (blst_p1, G1Projective) {
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

fn blst_mult(p: &blst_p1, k: &[u64; 4]) -> Option<(Vec<u64>, Vec<u64>)> {
    let (mut r, mut a) = (blst_p1::default(), blst_p1_affine::default());
    unsafe {
        blst_p1_mult(&mut r, p, le_bytes(k).as_ptr(), 256);
        if blst_p1_is_inf(&r) { return None; }
        blst_p1_to_affine(&mut a, &r);
    }
    Some((a.x.l.to_vec(), a.y.l.to_vec()))
}

fn aff(p: &G1Projective) -> Option<(Vec<u64>, Vec<u64>)> {
    p.to_affine().map(|a| (a.x.0.to_vec(), a.y.0.to_vec()))
}

fn glv(k: &[u64; 4], p: &G1Projective) -> G1Projective {
    let mut r = G1Projective::identity();
    g1_scalar_mul_glv(&mut r, k, p);
    r
}

fn dbl_add(k: &[u64; 4], p: &G1Projective) -> G1Projective {
    let mut r = G1Projective::identity();
    g1_scalar_mul(&mut r, k, p);
    r
}

fn u128_limbs(x: u128) -> [u64; 4] { [x as u64, (x >> 64) as u64, 0, 0] }

#[test]
fn random_scalars_and_points_match_blst_and_dbl_add() {
    let mut rng = Rng(21);
    for _ in 0..24 {
        let (bp, p) = blst_point(&rng.scalar());
        let k = rng.scalar();
        let g = aff(&glv(&k, &p));
        assert_eq!(g, blst_mult(&bp, &k), "k = {:x?}", k);
        assert_eq!(g, aff(&dbl_add(&k, &p)), "k = {:x?}", k);
    }
}

#[test]
fn split_recombines() {
    // k mod r = k1 + lambda k2, k1 < lambda, k2 <= lambda + 1 (checked through the group:
    // [k] G = [k1] G + [lambda] ([k2] G), and the bounds directly).
    let mut rng = Rng(5);
    let (_, g) = blst_point(&[1, 0, 0, 0]);
    for _ in 0..16 {
        let k = rng.scalar();
        let (k1, k2) = glv_split(&k);
        assert!(k1 < GLV_LAMBDA);
        assert!(k2 <= GLV_LAMBDA + 1);
        let a = dbl_add(&u128_limbs(k1), &g);
        let b = dbl_add(&u128_limbs(GLV_LAMBDA), &dbl_add(&u128_limbs(k2), &g));
        let mut s = G1Projective::identity();
        g1_add(&mut s, &a, &b);
        assert_eq!(aff(&s), aff(&dbl_add(&k, &g)), "k = {:x?}", k);
    }
}

#[test]
fn any_k1_k2_is_k1_p_plus_k2_phi() {
    // g1_glv_closed: the emitted loop computes k1 P + k2 Phi for any 128-bit k1, k2.
    let mut rng = Rng(9);
    for _ in 0..8 {
        let (_, p) = blst_point(&rng.scalar());
        let (k1, k2) = (((rng.next() as u128) << 64) | rng.next() as u128,
                        ((rng.next() as u128) << 64) | rng.next() as u128);
        let mut r = G1Projective::identity();
        g1_scalar_mul_glv_split(&mut r, k1, k2, &p);
        let mut phi = p;
        fp_mul(&mut phi.x, &GLV_OMEGA, &p.x);
        let mut s = G1Projective::identity();
        g1_add(&mut s, &dbl_add(&u128_limbs(k1), &p), &dbl_add(&u128_limbs(k2), &phi));
        assert_eq!(aff(&r), aff(&s));
    }
}

#[test]
fn omega_is_the_lambda_eigenvector() {
    // phi(G) = [lambda] G for GLV_OMEGA; and for omega^2 = bls12_omega (BLS12_Endomorphism)
    // it is [lambda^2] G instead.
    let (_, g) = blst_point(&[1, 0, 0, 0]);
    let mut phi = g;
    fp_mul(&mut phi.x, &GLV_OMEGA, &g.x);
    assert_eq!(aff(&phi), aff(&dbl_add(&u128_limbs(GLV_LAMBDA), &g)));
    let mut w2 = Fp([0; 6]);
    fp_mul(&mut w2, &GLV_OMEGA, &GLV_OMEGA);
    let mut phi2 = g;
    fp_mul(&mut phi2.x, &w2, &g.x);
    assert_ne!(aff(&phi2), aff(&dbl_add(&u128_limbs(GLV_LAMBDA), &g)));
}

#[test]
fn edge_cases() {
    let (bg, g) = blst_point(&[1, 0, 0, 0]);
    assert!(glv(&[0; 4], &g).is_identity());
    assert!(glv(&R, &g).is_identity());
    let mut rm1 = R; rm1[0] -= 1;
    let mut rp1 = R; rp1[0] += 1;
    // lambda^2 + lambda = r - 1: k2 = lambda + 1, k1 = 0.
    for k in [[1, 0, 0, 0], [2, 0, 0, 0], rm1, rp1, [u64::MAX; 4], [0, 0, 0, 1u64 << 63],
              u128_limbs(GLV_LAMBDA), u128_limbs(GLV_LAMBDA - 1), u128_limbs(u128::MAX)] {
        assert_eq!(aff(&glv(&k, &g)), blst_mult(&bg, &k), "k = {:x?}", k);
    }
    assert!(glv(&[5, 6, 7, 8], &G1Projective::identity()).is_identity());
    // Z != 1 input: 3G.
    let mut g2 = G1Projective::identity();
    g1_double(&mut g2, &g);
    let mut g3 = G1Projective::identity();
    g1_add(&mut g3, &g2, &g);
    let k = [0x1234_5678_9abc_def0, 0x0fed_cba9_8765_4321, 3, 0];
    let mut k3 = blst_p1::default();
    unsafe { blst_p1_mult(&mut k3, &bg, le_bytes(&[3, 0, 0, 0]).as_ptr(), 256) };
    assert_eq!(aff(&glv(&k, &g3)), blst_mult(&k3, &k));
}
