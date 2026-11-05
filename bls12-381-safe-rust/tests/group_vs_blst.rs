//! The G1/G2 group law of `group.rs` against blst: generators, scalar
//! multiples of the generators (compared limb for limb, since both use the
//! Montgomery representation with R = 2^384), the order r, and bilinearity
//! of the pairing on the resulting points.

use blst::*;
use bls12_381::group::*;
use bls12_381::Fp12;

/// The group order r, little-endian.
const R: [u64; 4] = [
    0xffffffff00000001, 0x53bda402fffe5bfe, 0x3339d80809a1d805, 0x73eda753299d7d48,
];

const SCALARS: [[u64; 4]; 4] = [
    [1, 0, 0, 0],
    [2, 0, 0, 0],
    [0xdeadbeefcafef00d, 0, 0, 0],
    [0x0123456789abcdef, 0xfedcba9876543210, 0x0f1e2d3c4b5a6978, 0x1234567890abcdef],
];

fn le_bytes(k: &[u64; 4]) -> [u8; 32] {
    let mut b = [0u8; 32];
    for (i, w) in k.iter().enumerate() {
        b[8 * i..8 * i + 8].copy_from_slice(&w.to_le_bytes());
    }
    b
}

fn ours_g1(k: &[u64; 4]) -> G1Projective {
    let mut r = G1Projective::identity();
    g1_scalar_mul(&mut r, k, &G1Projective::from_affine(&g1_generator()));
    r
}

fn ours_g2(k: &[u64; 4]) -> G2Projective {
    let mut r = G2Projective::identity();
    g2_scalar_mul(&mut r, k, &G2Projective::from_affine(&g2_generator()));
    r
}

fn blst_g1(k: &[u64; 4]) -> blst_p1_affine {
    let (mut p, mut a) = (blst_p1::default(), blst_p1_affine::default());
    unsafe {
        blst_p1_mult(&mut p, blst_p1_generator(), le_bytes(k).as_ptr(), 256);
        blst_p1_to_affine(&mut a, &p);
    }
    a
}

fn blst_g2(k: &[u64; 4]) -> blst_p2_affine {
    let (mut p, mut a) = (blst_p2::default(), blst_p2_affine::default());
    unsafe {
        blst_p2_mult(&mut p, blst_p2_generator(), le_bytes(k).as_ptr(), 256);
        blst_p2_to_affine(&mut a, &p);
    }
    a
}

#[test]
fn generators_match_blst() {
    let (g1, g2) = unsafe { (*blst_p1_affine_generator(), *blst_p2_affine_generator()) };
    assert_eq!(g1_generator().x.0, g1.x.l);
    assert_eq!(g1_generator().y.0, g1.y.l);
    assert_eq!(g2_generator().x.c0.0, g2.x.fp[0].l);
    assert_eq!(g2_generator().x.c1.0, g2.x.fp[1].l);
    assert_eq!(g2_generator().y.c0.0, g2.y.fp[0].l);
    assert_eq!(g2_generator().y.c1.0, g2.y.fp[1].l);
}

#[test]
fn g1_scalar_mul_matches_blst() {
    for k in &SCALARS {
        let ours = ours_g1(k).to_affine().expect("nonzero multiple");
        let theirs = blst_g1(k);
        assert_eq!(ours.x.0, theirs.x.l, "x of {:x?}·G1", k);
        assert_eq!(ours.y.0, theirs.y.l, "y of {:x?}·G1", k);
    }
}

#[test]
fn g2_scalar_mul_matches_blst() {
    for k in &SCALARS {
        let ours = ours_g2(k).to_affine().expect("nonzero multiple");
        let theirs = blst_g2(k);
        assert_eq!([ours.x.c0.0, ours.x.c1.0], [theirs.x.fp[0].l, theirs.x.fp[1].l]);
        assert_eq!([ours.y.c0.0, ours.y.c1.0], [theirs.y.fp[0].l, theirs.y.fp[1].l]);
    }
}

#[test]
fn generators_have_order_r() {
    assert!(ours_g1(&R).is_identity());
    assert!(ours_g2(&R).is_identity());
}

#[test]
fn addition_agrees_with_scalar_mul() {
    // 2G + 3G = 5G, and G + G = 2G through the doubling case of g1_add.
    let (g2x, g3x, g5x) = (ours_g1(&[2, 0, 0, 0]), ours_g1(&[3, 0, 0, 0]), ours_g1(&[5, 0, 0, 0]));
    let mut s = G1Projective::identity();
    g1_add(&mut s, &g2x, &g3x);
    assert_eq!(s.to_affine(), g5x.to_affine());
    let g = G1Projective::from_affine(&g1_generator());
    g1_add(&mut s, &g, &g);
    assert_eq!(s.to_affine(), g2x.to_affine());
    let (h2, h3, h5) = (ours_g2(&[2, 0, 0, 0]), ours_g2(&[3, 0, 0, 0]), ours_g2(&[5, 0, 0, 0]));
    let mut t = G2Projective::identity();
    g2_add(&mut t, &h2, &h3);
    assert_eq!(t.to_affine(), h5.to_affine());
}

#[test]
fn pairing_is_bilinear() {
    // e(aP, bQ) = e(abP, Q) with a = 6, b = 7.
    let (a_p, b_q) = (ours_g1(&[6, 0, 0, 0]), ours_g2(&[7, 0, 0, 0]));
    let ab_p = ours_g1(&[42, 0, 0, 0]);
    let q = g2_generator();
    let (mut lhs, mut rhs) = (Fp12::zero(), Fp12::zero());
    pairing_affine(&mut lhs, &a_p.to_affine().unwrap(), &b_q.to_affine().unwrap());
    pairing_affine(&mut rhs, &ab_p.to_affine().unwrap(), &q);
    assert_eq!(lhs, rhs);
    let mut base = Fp12::zero();
    pairing_affine(&mut base, &g1_generator(), &q);
    assert_ne!(base, lhs);
}
