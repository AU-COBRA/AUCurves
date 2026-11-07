//! `group::g1_msm` (the Rocq-emitted bedrock2 Pippenger `msm_bls12`) against
//! blst: Σ kᵢ·Pᵢ computed by blst as a naive sum of `blst_p1_mult`, for
//! n ∈ {1, 2, 16, 256} with pseudo-random 256-bit scalars and points, plus
//! edge cases (empty input, zero scalars, identity points, repeated points,
//! the group order, the all-ones scalar).  Coordinates are compared limb for
//! limb in affine form (both sides use Montgomery limbs with R = 2^384).

use blst::*;
use bls12_381::group::*;

/// The group order r, little-endian.
const R: [u64; 4] = [
    0xffffffff00000001, 0x53bda402fffe5bfe, 0x3339d80809a1d805, 0x73eda753299d7d48,
];

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
}

fn le_bytes(k: &[u64; 4]) -> [u8; 32] {
    let mut b = [0u8; 32];
    for (i, w) in k.iter().enumerate() {
        b[8 * i..8 * i + 8].copy_from_slice(&w.to_le_bytes());
    }
    b
}

fn blst_mul_gen(k: &[u64; 4]) -> blst_p1 {
    let mut p = blst_p1::default();
    unsafe { blst_p1_mult(&mut p, blst_p1_generator(), le_bytes(k).as_ptr(), 256) };
    p
}

/// blst point as our G1Projective (affine, Z = 1), or the identity.
fn ours_of_blst(p: &blst_p1) -> G1Projective {
    let mut a = blst_p1_affine::default();
    unsafe {
        if blst_p1_is_inf(p) { return G1Projective::identity(); }
        blst_p1_to_affine(&mut a, p);
    }
    G1Projective::from_affine(&G1Affine { x: bls12_381::Fp(a.x.l), y: bls12_381::Fp(a.y.l) })
}

/// Naive Σ kᵢ·Pᵢ with blst, in affine form (`None` for the identity).
fn blst_msm(points: &[blst_p1], scalars: &[[u64; 4]]) -> Option<([u64; 6], [u64; 6])> {
    let mut acc = blst_p1::default();
    for (p, k) in points.iter().zip(scalars) {
        let mut t = blst_p1::default();
        let mut s = blst_p1::default();
        unsafe {
            blst_p1_mult(&mut t, p, le_bytes(k).as_ptr(), 256);
            blst_p1_add_or_double(&mut s, &acc, &t);
        }
        acc = s;
    }
    unsafe {
        if blst_p1_is_inf(&acc) { return None; }
        let mut a = blst_p1_affine::default();
        blst_p1_to_affine(&mut a, &acc);
        Some((a.x.l, a.y.l))
    }
}

fn ours_msm(points: &[blst_p1], scalars: &[[u64; 4]]) -> Option<([u64; 6], [u64; 6])> {
    let ps: Vec<G1Projective> = points.iter().map(ours_of_blst).collect();
    let mut r = G1Projective::identity();
    g1_msm(&mut r, &ps, scalars);
    r.to_affine().map(|a| (a.x.0, a.y.0))
}

fn random_instance(n: usize, seed: u64) -> (Vec<blst_p1>, Vec<[u64; 4]>) {
    let mut rng = Rng(seed);
    let points = (0..n).map(|_| blst_mul_gen(&rng.scalar())).collect();
    let scalars = (0..n).map(|_| rng.scalar()).collect();
    (points, scalars)
}

fn check(n: usize, seed: u64) {
    let (points, scalars) = random_instance(n, seed);
    assert_eq!(ours_msm(&points, &scalars), blst_msm(&points, &scalars), "n = {}", n);
}

#[test] fn msm_n1() { check(1, 1); }
#[test] fn msm_n2() { check(2, 2); }
#[test] fn msm_n16() { check(16, 16); }
#[test] fn msm_n256() { check(256, 256); }

#[test]
fn msm_empty_is_identity() {
    let mut r = G1Projective::identity();
    g1_msm(&mut r, &[], &[]);
    assert!(r.is_identity());
}

#[test]
fn msm_edge_cases() {
    let (mut points, mut scalars) = random_instance(8, 99);
    scalars[0] = [0; 4];                                 // zero scalar
    scalars[1] = R;                                      // the group order
    scalars[2] = [u64::MAX; 4];                          // 2^256 - 1
    scalars[3] = [1, 0, 0, 0];
    points[4] = blst_p1::default();                      // identity point
    points[5] = points[6];                               // repeated point ...
    scalars[5] = scalars[6];                             // ... with the same scalar: same buckets
    assert_eq!(ours_msm(&points, &scalars), blst_msm(&points, &scalars));
}

/// Input points with Z != 1: `msm_curve_add` adds a point to a bucket with the mixed
/// formula only when its Z is 1 (Montgomery words of one); the others, here every second
/// point scaled to (l x : l y : l), take the complete projective addition.
#[test]
fn msm_projective_inputs() {
    let (points, scalars) = random_instance(64, 64);
    let lam = ours_of_blst(&blst_mul_gen(&[3, 0, 0, 0])).x; // a nonzero field element
    let mut ps: Vec<G1Projective> = points.iter().map(ours_of_blst).collect();
    for (i, p) in ps.iter_mut().enumerate() {
        if i % 2 == 1 {
            let (x, y, z) = (p.x, p.y, p.z);
            bls12_381::fp_mul(&mut p.x, &x, &lam);
            bls12_381::fp_mul(&mut p.y, &y, &lam);
            bls12_381::fp_mul(&mut p.z, &z, &lam);
        }
    }
    let mut r = G1Projective::identity();
    g1_msm(&mut r, &ps, &scalars);
    assert_eq!(r.to_affine().map(|a| (a.x.0, a.y.0)), blst_msm(&points, &scalars));
}

#[test]
fn msm_sum_to_identity() {
    // k·P + (r - k)·P = 0.
    let p = blst_mul_gen(&[7, 0, 0, 0]);
    let k = [5u64, 0, 0, 0];
    let mut rk = R;
    rk[0] -= 5;
    assert_eq!(ours_msm(&[p, p], &[k, rk]), None);
}

#[test]
fn msm_n1_agrees_with_scalar_mul_and_handwritten() {
    let mut rng = Rng(7);
    let k = rng.scalar();
    let g = G1Projective::from_affine(&g1_generator());
    let (mut a, mut b) = (G1Projective::identity(), G1Projective::identity());
    g1_msm(&mut a, &[g], &[k]);
    g1_scalar_mul(&mut b, &k, &g);
    let mut c = handwritten::G1Jacobian::identity();
    handwritten::g1j_scalar_mul(&mut c, &k, &handwritten::G1Jacobian::from_affine(&g1_generator()));
    assert_eq!(a.to_affine(), b.to_affine());
    assert_eq!(a.to_affine(), c.to_affine());
}
