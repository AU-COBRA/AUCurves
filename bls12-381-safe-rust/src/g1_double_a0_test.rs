//! Differential test for the Rocq-emitted Algorithm 9 doubling
//! (BLS12-381).
//!
//! `g1_double_a0_extracted.rs` is machine-emitted; this file holds a
//! REFERENCE transcription of RCB 2015 Algorithm 9 in the paper's
//! in-place form, over the crate's struct-typed `tower::Fp` leaves,
//! with `3b` recomputed here from `bls12_from_word`.  The two are
//! independent down to the leaf calls: different slot discipline (the
//! paper's buffer reuse against the emitted SSA form), different
//! representation (`Fp` records against `[u8; 48]` byte slots),
//! different source of the curve constant.
//!
//! Both are input-oblivious straight-line chains, so agreement on
//! arbitrary field elements — not only on-curve points — pins the
//! emitted operand mapping, the byte ABI, the limb endianness and the
//! baked-in `cB3` constant.  Curve `b = 4`, so `3b = 12`.

use crate::g1_double_a0_extracted::g1_proj_double_limbs;
use crate::tower::{bls12_add, bls12_from_word, bls12_mul, bls12_sub, Fp};

const LIMBS: usize = 6;

fn three_b() -> Fp {
    let mut o = Fp([0u64; LIMBS]);
    bls12_from_word(&mut o, 12u64);
    o
}

/// RCB 2015 Algorithm 9, transcribed in the paper's in-place form.
fn alg9_reference(x: &Fp, y: &Fp, z: &Fp, b3: &Fp) -> [Fp; 3] {
    let mut u = Fp([0u64; LIMBS]);
    let mut t0 = Fp([0u64; LIMBS]); bls12_mul(&mut t0, y, y);     // 1
    let mut z3 = Fp([0u64; LIMBS]); bls12_add(&mut z3, &t0, &t0); // 2
    bls12_add(&mut u, &z3, &z3); z3 = u;                          // 3
    bls12_add(&mut u, &z3, &z3); z3 = u;                          // 4
    let mut t1 = Fp([0u64; LIMBS]); bls12_mul(&mut t1, y, z);     // 5
    let mut t2 = Fp([0u64; LIMBS]); bls12_mul(&mut t2, z, z);     // 6
    bls12_mul(&mut u, b3, &t2); t2 = u;                           // 7
    let mut x3 = Fp([0u64; LIMBS]); bls12_mul(&mut x3, &t2, &z3); // 8
    let mut y3 = Fp([0u64; LIMBS]); bls12_add(&mut y3, &t0, &t2); // 9
    bls12_mul(&mut u, &t1, &z3); z3 = u;                          // 10
    bls12_add(&mut u, &t2, &t2); t1 = u;                          // 11
    bls12_add(&mut u, &t1, &t2); t2 = u;                          // 12
    bls12_sub(&mut u, &t0, &t2); t0 = u;                          // 13
    bls12_mul(&mut u, &t0, &y3); y3 = u;                          // 14
    bls12_add(&mut u, &x3, &y3); y3 = u;                          // 15
    bls12_mul(&mut u, x, y); t1 = u;                              // 16
    bls12_mul(&mut u, &t0, &t1); x3 = u;                          // 17
    bls12_add(&mut u, &x3, &x3); x3 = u;                          // 18
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
        bls12_from_word(&mut a, self.0 | 1);
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        let mut b = Fp([0u64; LIMBS]);
        bls12_from_word(&mut b, self.0 | 1);
        let mut c = Fp([0u64; LIMBS]);
        bls12_mul(&mut c, &a, &b);
        let mut d = Fp([0u64; LIMBS]);
        bls12_add(&mut d, &c, &a);
        let mut e = Fp([0u64; LIMBS]);
        bls12_mul(&mut e, &d, &c);
        e
    }
}

fn word(w: u64) -> Fp {
    let mut o = Fp([0u64; LIMBS]);
    bls12_from_word(&mut o, w);
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

    let mut sq = Fp([0u64; LIMBS]); bls12_mul(&mut sq, &b3, &b3);   // 9b^2
    let mut t = Fp([0u64; LIMBS]); bls12_add(&mut t, &sq, &sq);      // 18b^2
    let mut s = Fp([0u64; LIMBS]); bls12_add(&mut s, &t, &sq);       // 27b^2
    let mut neg = Fp([0u64; LIMBS]); bls12_sub(&mut neg, &zero, &s); // -27b^2

    // Non-vacuity: -27b^2 must not be zero, or the comparison below
    // would pass for any constant.
    assert_ne!(neg.0, zero.0, "-27b^2 is zero; this test would pass trivially");

    assert_eq!(got[0].0, zero.0, "X3 should be 0 on (0:0:1)");
    assert_eq!(got[2].0, zero.0, "Z3 should be 0 on (0:0:1)");
    assert_eq!(got[1].0, neg.0,
               "Y3 on (0:0:1) should be -27b^2; the baked-in cB3 is wrong");
}
