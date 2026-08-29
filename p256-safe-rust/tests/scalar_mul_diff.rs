//! Differential test: the Rocq-emitted w = 4 wNAF scalar multiplication
//! (`src/scalar_mul_extracted.rs`, generated from
//! `src/Bedrock/Curve/NistWnafScalarMultRustCmd.v`) against the
//! hand-written constant-time ladder `group::g1_scalar_mul`.
//!
//! The two use different algorithms — 256 doublings + 256 masked
//! additions versus 257 doublings + one addition per nonzero wNAF digit
//! over a table of odd multiples — so the projective coordinates differ;
//! they are compared as projective POINTS (cross-multiplication), which
//! is exactly the `pt_eq` under which
//! `P256_wNAF_Instance.p256_wnaf_single_full` states its conclusion.
//!
//! Run with: cargo test -p p256-safe-rust --features extracted
#![cfg(feature = "extracted")]

use p256::group::*;
use p256::wnaf::{g1_scalar_mul_wnaf, point_from_bytes, point_to_bytes, wnaf_digits_w4};
use p256::{fp_mul, Fp};

/// Projective equality: X1*Z2 == X2*Z1 and Y1*Z2 == Y2*Z1, with the
/// identity (Z = 0) handled separately.  Same predicate as the
/// `g1_eq` helper in `group.rs`'s test module.
fn pt_eq(p: &G1, q: &G1) -> bool {
    let (pi, qi) = (g1_is_identity(p), g1_is_identity(q));
    if pi || qi {
        return pi == qi;
    }
    let mut l = Fp([0u64; 4]);
    let mut r = Fp([0u64; 4]);
    fp_mul(&mut l, &p.x, &q.z);
    fp_mul(&mut r, &q.x, &p.z);
    if l.0 != r.0 {
        return false;
    }
    fp_mul(&mut l, &p.y, &q.z);
    fp_mul(&mut r, &q.y, &p.z);
    l.0 == r.0
}

/// xorshift64*, so the "random" scalars are reproducible without a
/// dependency.
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
    fn scalar(&mut self) -> [u8; 32] {
        let mut s = [0u8; 32];
        for chunk in s.chunks_mut(8) {
            chunk.copy_from_slice(&self.next().to_le_bytes());
        }
        // Keep the top byte small so the scalar stays below the group
        // order; the wNAF path itself only needs k < 2^256.
        s[0] &= 0x3f;
        s
    }
}

fn scalar_from_u64(k: u64) -> [u8; 32] {
    let mut s = [0u8; 32];
    s[24..32].copy_from_slice(&k.to_be_bytes());
    s
}

#[test]
fn point_bytes_roundtrip() {
    let g = g1_generator();
    let pts = [g1_identity(), g, g1_add(&g, &g), g1_neg(&g)];
    for p in &pts {
        let b = point_to_bytes(p);
        let q = point_from_bytes(&b);
        assert_eq!(p.x.0, q.x.0);
        assert_eq!(p.y.0, q.y.0);
        assert_eq!(p.z.0, q.z.0);
    }
}

/// The emitted driver's fixed KAT vectors: small scalars whose value is
/// checkable by repeated addition, independently of either ladder.
#[test]
fn wnaf_matches_repeated_addition_small() {
    let g = g1_generator();
    let mut acc = g1_identity();
    for k in 0..40u64 {
        let got = g1_scalar_mul_wnaf(&scalar_from_u64(k), &g);
        assert!(pt_eq(&got, &acc), "wnaf({k}) != {k}·G by repeated addition");
        acc = g1_add(&acc, &g);
    }
}

/// The KAT vectors used elsewhere in the crate: the generator, its
/// small multiples, and the group order.
#[test]
fn wnaf_matches_ladder_on_kat_scalars() {
    let g = g1_generator();
    let base_pts = [g, g1_add(&g, &g), g1_scalar_mul(&scalar_from_u64(7), &g)];

    let mut kats: Vec<[u8; 32]> = (0..24u64).map(scalar_from_u64).collect();
    kats.push(scalar_from_u64(u64::MAX));
    kats.push(scalar_from_u64(0x8000_0000_0000_0000));
    // n, the group order: n·P must be the identity for P in <G>.
    let mut n_be = [0u8; 32];
    for (i, limb) in N_CANON.iter().enumerate() {
        let be = limb.to_be_bytes();
        let start = 32 - 8 * (i + 1);
        n_be[start..start + 8].copy_from_slice(&be);
    }
    kats.push(n_be);
    // n - 1
    let mut nm1 = n_be;
    nm1[31] -= 1;
    kats.push(nm1);
    // The bench scalar of examples/bench_compare.rs.
    let mut k = [0u8; 32];
    k[0] = 0x1a;
    for (i, b) in k.iter_mut().enumerate().skip(1) {
        *b = (i as u8).wrapping_mul(37).wrapping_add(11);
    }
    kats.push(k);

    for p in &base_pts {
        for s in &kats {
            let want = g1_scalar_mul(s, p);
            let got = g1_scalar_mul_wnaf(s, p);
            assert!(
                pt_eq(&got, &want),
                "wnaf != ladder for scalar {s:02x?} on a KAT point"
            );
        }
    }

    // n·G is the identity through the emitted path too.
    assert!(g1_is_identity(&g1_scalar_mul_wnaf(&n_be, &g)));
}

#[test]
fn wnaf_matches_ladder_on_random_scalars() {
    let g = g1_generator();
    let p = g1_scalar_mul(&scalar_from_u64(0x5eed_1234_5678_9abc), &g);
    let mut rng = Rng(0x0123_4567_89ab_cdef);
    for i in 0..256 {
        let s = rng.scalar();
        let want = g1_scalar_mul(&s, &p);
        let got = g1_scalar_mul_wnaf(&s, &p);
        assert!(pt_eq(&got, &want), "wnaf != ladder at random trial {i}");
    }
}

/// The identity is a fixed point of the emitted driver (the complete
/// formulas make every addition with (0:1:0) correct).
#[test]
fn wnaf_on_identity() {
    let o = g1_identity();
    let mut rng = Rng(0xdead_beef_cafe_0001);
    for _ in 0..8 {
        let s = rng.scalar();
        assert!(g1_is_identity(&g1_scalar_mul_wnaf(&s, &o)));
    }
}

/// The digit array the encoder produces is the one the driver consumes:
/// re-running the driver on digits built for `k1 + k2` must agree with
/// adding the two results.
#[test]
fn wnaf_additive_in_the_scalar() {
    let g = g1_generator();
    let mut rng = Rng(0x00c0_ffee_0000_0007);
    for _ in 0..32 {
        let mut a = rng.scalar();
        let mut b = rng.scalar();
        a[0] &= 0x0f;
        b[0] &= 0x0f;
        let mut sum = [0u8; 32];
        let mut carry = 0u16;
        for i in (0..32).rev() {
            let s = a[i] as u16 + b[i] as u16 + carry;
            sum[i] = s as u8;
            carry = s >> 8;
        }
        assert_eq!(carry, 0);
        let pa = g1_scalar_mul_wnaf(&a, &g);
        let pb = g1_scalar_mul_wnaf(&b, &g);
        let ps = g1_scalar_mul_wnaf(&sum, &g);
        assert!(pt_eq(&g1_add(&pa, &pb), &ps));
    }
}

/// The digits are exactly what `wNAF.v` specifies for a couple of hand
/// computations: `wnaf_digit 4 k` for small k.
#[test]
fn digit_expansion_small_cases() {
    // k = 1  ->  [1, 0, 0, ...]
    let d = wnaf_digits_w4(&scalar_from_u64(1));
    assert_eq!(d[0] as i64, 1);
    assert!(d[1..].iter().all(|&x| x == 0));

    // k = 15 -> 15 mod 16 = 15 >= 8, so d0 = -1, k := (15+1)/2 = 8,
    // then 8 even -> 0, 4 -> 0, 2 -> 0, 1 -> 1.
    let d = wnaf_digits_w4(&scalar_from_u64(15));
    assert_eq!(d[0] as i64, -1);
    assert_eq!(d[1] as i64, 0);
    assert_eq!(d[2] as i64, 0);
    assert_eq!(d[3] as i64, 0);
    assert_eq!(d[4] as i64, 1);
    assert!(d[5..].iter().all(|&x| x == 0));

    // k = 7 -> 7 < 8 so d0 = 7, k := 0.
    let d = wnaf_digits_w4(&scalar_from_u64(7));
    assert_eq!(d[0] as i64, 7);
    assert!(d[1..].iter().all(|&x| x == 0));
}
