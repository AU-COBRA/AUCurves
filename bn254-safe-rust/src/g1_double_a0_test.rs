//! Differential test for the Rocq-emitted Algorithm 9 doubling
//! (BN254 (alt_bn128)).
//!
//! `g1_double_a0_extracted.rs` is machine-emitted; this file holds a
//! REFERENCE transcription of RCB 2015 Algorithm 9 in the paper's
//! in-place form, over the crate's struct-typed `tower::Fp` leaves,
//! with `3b` recomputed here from `bn254_from_word`.  The two are
//! independent down to the leaf calls: different slot discipline (the
//! paper's buffer reuse against the emitted SSA form), different
//! representation (`Fp` records against `[u8; 32]` byte slots),
//! different source of the curve constant.
//!
//! Both are input-oblivious straight-line chains, so agreement on
//! arbitrary field elements — not only on-curve points — pins the
//! emitted operand mapping, the byte ABI, the limb endianness and the
//! baked-in `cB3` constant.  Curve `b = 3`, so `3b = 9`.

use crate::g1_double_a0_extracted::g1_proj_double_limbs;
use crate::tower::{bn254_add, bn254_from_word, bn254_mul, bn254_sub, Fp};

const LIMBS: usize = 4;

fn three_b() -> Fp {
    let mut o = Fp([0u64; LIMBS]);
    bn254_from_word(&mut o, 9u64);
    o
}

/// RCB 2015 Algorithm 9, transcribed in the paper's in-place form.
fn alg9_reference(x: &Fp, y: &Fp, z: &Fp, b3: &Fp) -> [Fp; 3] {
    let mut u = Fp([0u64; LIMBS]);
    let mut t0 = Fp([0u64; LIMBS]); bn254_mul(&mut t0, y, y);     // 1
    let mut z3 = Fp([0u64; LIMBS]); bn254_add(&mut z3, &t0, &t0); // 2
    bn254_add(&mut u, &z3, &z3); z3 = u;                          // 3
    bn254_add(&mut u, &z3, &z3); z3 = u;                          // 4
    let mut t1 = Fp([0u64; LIMBS]); bn254_mul(&mut t1, y, z);     // 5
    let mut t2 = Fp([0u64; LIMBS]); bn254_mul(&mut t2, z, z);     // 6
    bn254_mul(&mut u, b3, &t2); t2 = u;                           // 7
    let mut x3 = Fp([0u64; LIMBS]); bn254_mul(&mut x3, &t2, &z3); // 8
    let mut y3 = Fp([0u64; LIMBS]); bn254_add(&mut y3, &t0, &t2); // 9
    bn254_mul(&mut u, &t1, &z3); z3 = u;                          // 10
    bn254_add(&mut u, &t2, &t2); t1 = u;                          // 11
    bn254_add(&mut u, &t1, &t2); t2 = u;                          // 12
    bn254_sub(&mut u, &t0, &t2); t0 = u;                          // 13
    bn254_mul(&mut u, &t0, &y3); y3 = u;                          // 14
    bn254_add(&mut u, &x3, &y3); y3 = u;                          // 15
    bn254_mul(&mut u, x, y); t1 = u;                              // 16
    bn254_mul(&mut u, &t0, &t1); x3 = u;                          // 17
    bn254_add(&mut u, &x3, &x3); x3 = u;                          // 18
    [x3, y3, z3]
}

fn emitted(x: &Fp, y: &Fp, z: &Fp) -> [Fp; 3] {
    let r = g1_proj_double_limbs(&[x.0, y.0, z.0]);
    [Fp(r[0]), Fp(r[1]), Fp(r[2])]
}

fn agree(x: &Fp, y: &Fp, z: &Fp, b3: &Fp, what: &str) {
    let got = emitted(x, y, z);
    let want = alg9_reference(x, y, z, b3);
    for (i, c) in ["X3", "Y3", "Z3"].iter().enumerate() {
        assert_eq!(got[i].0, want[i].0,
                   "emitted != reference in {c} on {what}");
    }
}

/// Deterministic field elements: `from_word` of an LCG stream, folded
/// through `mul`/`add` so every value is a reduced Montgomery element.
struct Rng(u64);
impl Rng {
    fn next_fp(&mut self) -> Fp {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        let mut a = Fp([0u64; LIMBS]);
        bn254_from_word(&mut a, self.0 | 1);
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        let mut b = Fp([0u64; LIMBS]);
        bn254_from_word(&mut b, self.0 | 1);
        let mut c = Fp([0u64; LIMBS]);
        bn254_mul(&mut c, &a, &b);
        let mut d = Fp([0u64; LIMBS]);
        bn254_add(&mut d, &c, &a);
        let mut e = Fp([0u64; LIMBS]);
        bn254_mul(&mut e, &d, &c);
        e
    }
}

fn word(w: u64) -> Fp {
    let mut o = Fp([0u64; LIMBS]);
    bn254_from_word(&mut o, w);
    o
}

/// The headline differential test.
#[test]
fn emitted_alg9_matches_reference() {
    let b3 = three_b();
    let zero = Fp([0u64; LIMBS]);
    let one = word(1);

    // Structured inputs, including the projective identity (0 : 1 : 0)
    // and the degenerate Z = 0 / Y = 0 cases.
    agree(&zero, &one, &zero, &b3, "identity (0:1:0)");
    agree(&zero, &zero, &zero, &b3, "all zero");
    agree(&one, &one, &one, &b3, "(1:1:1)");
    agree(&zero, &zero, &one, &b3, "(0:0:1)");
    agree(&one, &zero, &one, &b3, "(1:0:1)");
    agree(&one, &one, &zero, &b3, "(1:1:0)");
    agree(&word(2), &word(3), &word(5), &b3, "(2:3:5)");

    // Pseudo-random field elements.
    let mut rng = Rng(0x0123_4567_89ab_cdef);
    for i in 0..64 {
        let (x, y, z) = (rng.next_fp(), rng.next_fp(), rng.next_fp());
        agree(&x, &y, &z, &b3, &format!("random #{i}"));
        // Non-vacuity: the compared outputs must not be identically zero.
        let d = emitted(&x, &y, &z);
        assert!(d.iter().any(|c| c.0 != [0u64; LIMBS]),
                "emitted output is all-zero on random #{i}; test would pass trivially");
    }
}

/// Direct check of the emitted `cB3` byte constant, independent of the
/// reference body: on `(X, Y, Z) = (0, 0, 1)` Algorithm 9 collapses to
/// `X3 = 0`, `Z3 = 0`, `Y3 = -27b^2` (t0 = 0, t2 = 3b, t2c = 9b,
/// t0b = -9b, ya = 3b, yb = -27b^2, xa = 0).
#[test]
fn emitted_curve_constant_is_three_b() {
    let b3 = three_b();
    let zero = Fp([0u64; LIMBS]);
    let one = word(1);
    let got = emitted(&zero, &zero, &one);

    let mut sq = Fp([0u64; LIMBS]); bn254_mul(&mut sq, &b3, &b3);   // 9b^2
    let mut t = Fp([0u64; LIMBS]); bn254_add(&mut t, &sq, &sq);      // 18b^2
    let mut s = Fp([0u64; LIMBS]); bn254_add(&mut s, &t, &sq);       // 27b^2
    let mut neg = Fp([0u64; LIMBS]); bn254_sub(&mut neg, &zero, &s); // -27b^2

    // Non-vacuity: -27b^2 must not be zero, or the comparison below
    // would pass for any constant.
    assert_ne!(neg.0, zero.0, "-27b^2 is zero; this test would pass trivially");

    assert_eq!(got[0].0, zero.0, "X3 should be 0 on (0:0:1)");
    assert_eq!(got[2].0, zero.0, "Z3 should be 0 on (0:0:1)");
    assert_eq!(got[1].0, neg.0,
               "Y3 on (0:0:1) should be -27b^2; the baked-in cB3 is wrong");
}

// ─────────────────────────────────────────────────────────────────────
// On-curve cross-check, BN254 (alt_bn128) only: the G1 generator is (1, 2) on
// y^2 = x^3 + 3, so on-curve projective points are available here
// without any large constant.  The test asserts the point IS on the
// curve before using it, so a wrong generator fails loudly.
// ─────────────────────────────────────────────────────────────────────

/// RCB 2015 Algorithm 7 (a = 0 complete addition), reference form, so
/// the emitted doubling can be checked against `Alg7(P, P)` — the Rust
/// image of `PointDoubleA0.rcb_double_a0_eq_ladderstep`, which holds
/// coordinate for coordinate on ON-CURVE input.
fn alg7_reference(p: &[Fp; 3], q: &[Fp; 3], b3: &Fp) -> [Fp; 3] {
    let z = Fp([0u64; LIMBS]);
    let (x1, y1, z1) = (p[0], p[1], p[2]);
    let (x2, y2, z2) = (q[0], q[1], q[2]);
    let mut u = z;
    let mut t0 = z; bn254_mul(&mut t0, &x1, &x2);
    let mut t1 = z; bn254_mul(&mut t1, &y1, &y2);
    let mut t2 = z; bn254_mul(&mut t2, &z1, &z2);
    let mut t3 = z; bn254_add(&mut t3, &x1, &y1);
    let mut t4 = z; bn254_add(&mut t4, &x2, &y2);
    bn254_mul(&mut u, &t3, &t4); t3 = u;
    bn254_add(&mut u, &t0, &t1); t4 = u;
    bn254_sub(&mut u, &t3, &t4); t3 = u;
    bn254_add(&mut u, &x1, &z1); t4 = u;
    let mut t5 = z; bn254_add(&mut t5, &x2, &z2);
    bn254_mul(&mut u, &t4, &t5); t4 = u;
    bn254_add(&mut u, &t0, &t2); t5 = u;
    bn254_sub(&mut u, &t4, &t5); t4 = u;
    bn254_add(&mut u, &y1, &z1); t5 = u;
    let mut xo = z; bn254_add(&mut xo, &y2, &z2);
    bn254_mul(&mut u, &t5, &xo); t5 = u;
    bn254_add(&mut u, &t1, &t2); xo = u;
    bn254_sub(&mut u, &t5, &xo); t5 = u;
    let mut zo = z; bn254_mul(&mut zo, b3, &t2);
    bn254_sub(&mut u, &t1, &zo); xo = u;
    bn254_add(&mut u, &zo, &t1); zo = u;
    let mut yo = z; bn254_mul(&mut yo, &xo, &zo);
    bn254_add(&mut u, &t0, &t0); t1 = u;
    bn254_add(&mut u, &t1, &t0); t1 = u;
    bn254_mul(&mut u, b3, &t4); t4 = u;
    bn254_mul(&mut u, &t1, &t4); t0 = u;
    bn254_add(&mut u, &yo, &t0); yo = u;
    bn254_mul(&mut u, &t5, &t4); t0 = u;
    bn254_mul(&mut u, &t3, &xo); xo = u;
    bn254_sub(&mut u, &xo, &t0); xo = u;
    bn254_mul(&mut u, &t3, &t1); t0 = u;
    bn254_mul(&mut u, &t5, &zo); zo = u;
    bn254_add(&mut u, &zo, &t0); zo = u;
    [xo, yo, zo]
}

/// `Y^2 Z == X^3 + b Z^3`, the homogeneous curve equation at a = 0.
fn on_curve(p: &[Fp; 3], b: u64) -> bool {
    let z0 = Fp([0u64; LIMBS]);
    let (x, y, zc) = (p[0], p[1], p[2]);
    let mut y2 = z0; bn254_mul(&mut y2, &y, &y);
    let mut lhs = z0; bn254_mul(&mut lhs, &y2, &zc);
    let mut x2 = z0; bn254_mul(&mut x2, &x, &x);
    let mut x3 = z0; bn254_mul(&mut x3, &x2, &x);
    let mut z2 = z0; bn254_mul(&mut z2, &zc, &zc);
    let mut z3 = z0; bn254_mul(&mut z3, &z2, &zc);
    let mut bz3 = z0; bn254_mul(&mut bz3, &word(b), &z3);
    let mut rhs = z0; bn254_add(&mut rhs, &x3, &bz3);
    lhs.0 == rhs.0
}

#[test]
fn emitted_alg9_on_curve_points() {
    let b3 = three_b();
    // BN254 (alt_bn128) G1 generator (1, 2); asserted on-curve below.
    let g = [word(1), word(2), word(1)];
    assert!(on_curve(&g, 3), "the assumed G1 generator is not on the curve");

    let mut p = g;
    for k in 0..24 {
        let d = emitted(&p[0], &p[1], &p[2]);
        // (a) against Algorithm 7 applied to a repeated argument,
        //     coordinate for coordinate.
        let s = alg7_reference(&p, &p, &b3);
        assert_eq!([d[0].0, d[1].0, d[2].0], [s[0].0, s[1].0, s[2].0],
                   "emitted Alg 9 != Alg 7(P, P) at 2^{k}·G");
        // (b) the result is still on the curve.
        assert!(on_curve(&d, 3), "emitted doubling left the curve at 2^{k}·G");
        p = d;
    }

    // A non-normalised representative of the same point, Z != 1.
    let lambda = word(7);
    let z0 = Fp([0u64; LIMBS]);
    let mut sx = z0; bn254_mul(&mut sx, &g[0], &lambda);
    let mut sy = z0; bn254_mul(&mut sy, &g[1], &lambda);
    let mut sz = z0; bn254_mul(&mut sz, &g[2], &lambda);
    let gs = [sx, sy, sz];
    assert!(on_curve(&gs, 3));
    let d = emitted(&gs[0], &gs[1], &gs[2]);
    let s = alg7_reference(&gs, &gs, &b3);
    assert_eq!([d[0].0, d[1].0, d[2].0], [s[0].0, s[1].0, s[2].0],
               "emitted Alg 9 != Alg 7(P, P) on a Z != 1 representative");
    assert!(on_curve(&d, 3));
}
