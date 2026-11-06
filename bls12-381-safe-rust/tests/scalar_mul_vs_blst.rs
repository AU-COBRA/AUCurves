//! The emitted G1 scalar multiplication `group::g1_scalar_mul` (bedrock2
//! `g1_scalar_mul`, covered by `BLS12_MSM_Closed.g1_scalar_mul_closed`)
//! against blst, against the hand-written loop over the emitted group law
//! (`g1_scalar_mul_loop`) and against the hand-written Jacobian code, on
//! random scalars and points and on edge cases.

use blst::*;
use bls12_381::group::*;
use bls12_381::group::handwritten::*;

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
}

fn le_bytes(k: &[u64; 4]) -> [u8; 32] {
    let mut b = [0u8; 32];
    for (i, w) in k.iter().enumerate() {
        b[8 * i..8 * i + 8].copy_from_slice(&w.to_le_bytes());
    }
    b
}

/// k·G with blst, as a blst point and as our projective point.
fn blst_point(k: &[u64; 4]) -> (blst_p1, G1Projective) {
    let (mut p, mut a) = (blst_p1::default(), blst_p1_affine::default());
    unsafe {
        blst_p1_mult(&mut p, blst_p1_generator(), le_bytes(k).as_ptr(), 256);
        blst_p1_to_affine(&mut a, &p);
    }
    let q = if unsafe { blst_p1_is_inf(&p) } {
        G1Projective::identity()
    } else {
        G1Projective::from_affine(&G1Affine { x: bls12_381::Fp(a.x.l), y: bls12_381::Fp(a.y.l) })
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

fn emitted(k: &[u64; 4], p: &G1Projective) -> G1Projective {
    let mut r = G1Projective::identity();
    g1_scalar_mul(&mut r, k, p);
    r
}

#[test]
fn random_scalars_and_points_match_blst() {
    let mut rng = Rng(7);
    for _ in 0..24 {
        let (bp, p) = blst_point(&rng.scalar());
        let k = rng.scalar();
        assert_eq!(aff(&emitted(&k, &p)), blst_mult(&bp, &k), "k = {:x?}", k);
    }
}

#[test]
fn agrees_with_handwritten_loops() {
    let mut rng = Rng(11);
    for _ in 0..8 {
        let (_, p) = blst_point(&rng.scalar());
        let pa = p.to_affine().unwrap();
        let k = rng.scalar();
        let mut l = G1Projective::identity();
        g1_scalar_mul_loop(&mut l, &k, &p);
        let mut j = G1Jacobian::identity();
        g1j_scalar_mul(&mut j, &k, &G1Jacobian::from_affine(&pa));
        let e = aff(&emitted(&k, &p));
        assert_eq!(e, aff(&l));
        assert_eq!(e, j.to_affine().map(|a| (a.x.0.to_vec(), a.y.0.to_vec())));
    }
}

#[test]
fn edge_cases() {
    let (bg, g) = blst_point(&[1, 0, 0, 0]);
    // k = 0 and k = r give the identity.
    assert!(emitted(&[0; 4], &g).is_identity());
    assert!(emitted(&R, &g).is_identity());
    // k = 1, 2, r - 1, r + 1, 2^256 - 1 (not reduced mod r).
    let mut rm1 = R; rm1[0] -= 1;
    let mut rp1 = R; rp1[0] += 1;
    for k in [[1, 0, 0, 0], [2, 0, 0, 0], rm1, rp1, [u64::MAX; 4], [0, 0, 0, 1u64 << 63]] {
        assert_eq!(aff(&emitted(&k, &g)), blst_mult(&bg, &k), "k = {:x?}", k);
    }
    // The identity as input.
    assert!(emitted(&[5, 6, 7, 8], &G1Projective::identity()).is_identity());
    // A non-normalised input (Z != 1): 3G from the emitted addition.
    let mut g2 = G1Projective::identity();
    g1_double(&mut g2, &g);
    let mut g3 = G1Projective::identity();
    g1_add(&mut g3, &g2, &g);
    let k = [0x1234_5678_9abc_def0, 0x0fed_cba9_8765_4321, 3, 0];
    let mut k3 = blst_p1::default();
    unsafe { blst_p1_mult(&mut k3, &bg, le_bytes(&[3, 0, 0, 0]).as_ptr(), 256) };
    assert_eq!(aff(&emitted(&k, &g3)), blst_mult(&k3, &k));
}
