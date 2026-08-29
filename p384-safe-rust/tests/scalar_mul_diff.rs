//! Differential test: the Rocq-emitted w = 4 wNAF scalar multiplication
//! (`src/scalar_mul_extracted.rs`, generated from
//! `src/Bedrock/Curve/NistWnafScalarMultRustCmd.v`) against the
//! hand-written constant-time ladder `group::g1_scalar_mul`.
//!
//! The two use different algorithms, so the projective coordinates
//! differ; they are compared as projective POINTS, which is the `pt_eq`
//! under which `p384_wNAF_Instance.p384_wnaf_single_full` states its
//! conclusion.
//!
//! Run with: cargo test -p p384-safe-rust --features extracted
#![cfg(feature = "extracted")]

use p384::group::*;
use p384::wnaf::{g1_scalar_mul_wnaf, point_from_bytes, point_to_bytes, wnaf_digits_w4, LIMBS};
use p384::{fp_mul, Fp};

fn pt_eq(p: &G1, q: &G1) -> bool {
    let (pi, qi) = (g1_is_identity(p), g1_is_identity(q));
    if pi || qi {
        return pi == qi;
    }
    let mut l = Fp([0u64; LIMBS]);
    let mut r = Fp([0u64; LIMBS]);
    fp_mul(&mut l, &p.x, &q.z);
    fp_mul(&mut r, &q.x, &p.z);
    if l.0 != r.0 {
        return false;
    }
    fp_mul(&mut l, &p.y, &q.z);
    fp_mul(&mut r, &q.y, &p.z);
    l.0 == r.0
}

/// xorshift64*, reproducible without a dependency.
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }
    /// A scalar below 2^384 (the driver's digit budget).
    fn scalar(&mut self) -> [u64; LIMBS] {
        let mut s = [0u64; LIMBS];
        for limb in s.iter_mut() {
            *limb = self.next();
        }
        s[LIMBS - 1] &= u64::MAX;
        s
    }
}

fn small(v: u64) -> [u64; LIMBS] {
    let mut s = [0u64; LIMBS];
    s[0] = v;
    s
}

#[test]
fn point_bytes_roundtrip() {
    let g = g1_generator();
    let pts = [g1_identity(), g, g1_add(&g, &g), g1_neg(&g)];
    for p in &pts {
        let q = point_from_bytes(&point_to_bytes(p));
        assert_eq!(p.x.0, q.x.0);
        assert_eq!(p.y.0, q.y.0);
        assert_eq!(p.z.0, q.z.0);
    }
}

#[test]
fn wnaf_matches_repeated_addition_small() {
    let g = g1_generator();
    let mut acc = g1_identity();
    for k in 0..40u64 {
        let got = g1_scalar_mul_wnaf(&small(k), &g);
        assert!(pt_eq(&got, &acc), "wnaf({k}) != {k}*G by repeated addition");
        acc = g1_add(&acc, &g);
    }
}

#[test]
fn wnaf_matches_ladder_on_kat_scalars() {
    let g = g1_generator();
    let base_pts = [g, g1_add(&g, &g), g1_scalar_mul(&small(7), &g)];

    let mut kats: Vec<[u64; LIMBS]> = (0..24u64).map(small).collect();
    kats.push(small(u64::MAX));
    kats.push(small(0x8000_0000_0000_0000));
    kats.push(N_CANON);
    let mut nm1 = N_CANON;
    nm1[0] -= 1;
    kats.push(nm1);

    for p in &base_pts {
        for s in &kats {
            let want = g1_scalar_mul(s, p);
            let got = g1_scalar_mul_wnaf(s, p);
            assert!(pt_eq(&got, &want), "wnaf != ladder for {s:016x?}");
        }
    }
    assert!(g1_is_identity(&g1_scalar_mul_wnaf(&N_CANON, &g)));
}

#[test]
fn wnaf_matches_ladder_on_random_scalars() {
    let g = g1_generator();
    let p = g1_scalar_mul(&small(0x5eed_1234_5678_9abc), &g);
    let mut rng = Rng(0x0123_4567_89ab_cdef);
    for i in 0..128 {
        let s = rng.scalar();
        let want = g1_scalar_mul(&s, &p);
        let got = g1_scalar_mul_wnaf(&s, &p);
        assert!(pt_eq(&got, &want), "wnaf != ladder at random trial {i}");
    }
}

#[test]
fn wnaf_on_identity() {
    let o = g1_identity();
    let mut rng = Rng(0xdead_beef_cafe_0001);
    for _ in 0..8 {
        assert!(g1_is_identity(&g1_scalar_mul_wnaf(&rng.scalar(), &o)));
    }
}

#[test]
fn digit_expansion_small_cases() {
    let d = wnaf_digits_w4(&small(1));
    assert_eq!(d[0] as i64, 1);
    assert!(d[1..].iter().all(|&x| x == 0));

    // 15 mod 16 = 15 >= 8, so d0 = -1 and k := (15+1)/2 = 8.
    let d = wnaf_digits_w4(&small(15));
    assert_eq!(d[0] as i64, -1);
    assert_eq!(d[4] as i64, 1);
    assert!(d[1..4].iter().all(|&x| x == 0));
    assert!(d[5..].iter().all(|&x| x == 0));

    let d = wnaf_digits_w4(&small(7));
    assert_eq!(d[0] as i64, 7);
    assert!(d[1..].iter().all(|&x| x == 0));
}
