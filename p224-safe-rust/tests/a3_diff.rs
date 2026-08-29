//! Differential test for the `a = -3` specialised point formulas.
//!
//! Three implementations of the same function are compared:
//!
//! | path                                        | source                     |
//! |---------------------------------------------|----------------------------|
//! | `group::g1_add_general_a` (RCB Algorithm 1) | reference, 40 ops          |
//! | `group::g1_add_a3` / `g1_double_a3`         | hand-written, Alg. 4 / 6   |
//! | `g1_a3_extracted::*` (feature `extracted`)  | Rocq-emitted, Alg. 4 / 6   |
//!
//! `src/Bedrock/Group/CurveAdd/CurveA3Equiv.v` proves the a = -3 chains
//! equal to the general-a chain *as polynomial identities*, with no
//! on-curve or non-degeneracy hypothesis.  So the agreement asserted
//! here is exact equality of the projective triple, which is
//! stronger than projective equivalence, and it must hold on the
//! exceptional inputs too: the identity, `P + (-P)`, and doubling
//! the identity.
//!
//! Run with:
//!   cargo test -p p224-safe-rust --test a3_diff
//!   cargo test -p p224-safe-rust --test a3_diff --features extracted

use p224::group::*;
use p224::{fp_mul, Fp};

// The published NIST P-224 k*G vectors of tests/kat_vectors.rs.
const K2_X: &str = "706a46dc76dcb76798e60e6d89474788d16dc18032d268fd1a704fa6";
const K2_Y: &str = "1c2b76a7bc25e7702a704fa986892849fca629487acf3709d2e4e8bb";
const K3_X: &str = "df1b1d66a551d0d31eff822558b9d2cc75c2180279fe0d08fd896d04";
const K3_Y: &str = "a3f7f03cadd0be444c0aa56830130ddf77d317344e1af3591981a925";
const K5_X: &str = "31c49ae75bce7807cdff22055d94ee9021fedbb5ab51c57526f011aa";
const K5_Y: &str = "27e8bff1745635ec5ba0c9f1c2ede15414c6507d29ffe37e790a079b";
const K10_X: &str = "aea9e17a306517eb89152aa7096d2c381ec813c51aa880e7bee2c0fd";
const K10_Y: &str = "39bb30eab337e0a521b6cba1abe4b2b3a3e524c14a3fe3eb116b655f";
const KBIG_HEX: &str = "1a2b3c4d5e6f708192a3b4c5d6e7f8090f1e2d3c4b5a697887960123";

/// Big-endian hex -> canonical little-endian u64 limbs (zero-padded).
fn hex_to_limbs(s: &str) -> [u64; 4] {
    let bytes: Vec<u8> = (0..s.len() / 2)
        .map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap())
        .collect();
    let mut be = [0u8; 32];
    be[32 - bytes.len()..].copy_from_slice(&bytes);
    let mut limbs = [0u64; 4];
    for (i, limb) in limbs.iter_mut().enumerate() {
        let end = 32 - 8 * i;
        *limb = u64::from_be_bytes(be[end - 8..end].try_into().unwrap());
    }
    limbs
}

/// `k * P` by MSB-first double-and-add using only `g1_add_general_a`.
fn ref_mul(k: &[u64; 4], p: &G1) -> G1 {
    let mut acc = g1_identity();
    for i in (0..256).rev() {
        acc = g1_add_general_a(&acc, &acc);
        if (k[i / 64] >> (i % 64)) & 1 == 1 {
            acc = g1_add_general_a(&acc, p);
        }
    }
    acc
}

fn test_points() -> Vec<G1> {
    let g = g1_generator();
    let mut pts = vec![g1_identity(), g];

    for (x, y) in [
        (K2_X, K2_Y),
        (K3_X, K3_Y),
        (K5_X, K5_Y),
        (K10_X, K10_Y),
    ] {
        pts.push(g1_from_affine(&hex_to_limbs(x), &hex_to_limbs(y)));
    }
    pts.push(ref_mul(&hex_to_limbs(KBIG_HEX), &g));

    // Points with a non-trivial Z, reached by repeated general-a addition.
    let mut acc = g;
    for _ in 0..6 {
        acc = g1_add_general_a(&acc, &g);
        pts.push(acc);
    }

    // Deterministic pseudo-random multiples (xorshift64).
    let mut state: u64 = 0x9e37_79b9_7f4a_7c15;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    for _ in 0..6 {
        let k = [next(), next(), next(), next() >> 32];
        pts.push(ref_mul(&k, &g));
    }

    let negs: Vec<G1> = pts.iter().map(g1_neg).collect();
    pts.extend(negs);
    pts
}

fn eq(p: &G1, q: &G1) -> bool {
    p.x.0 == q.x.0 && p.y.0 == q.y.0 && p.z.0 == q.z.0
}

/// Projective equality via cross-multiplication.
fn proj_eq(p: &G1, q: &G1) -> bool {
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

#[test]
fn a3_add_matches_general_a() {
    let pts = test_points();
    for (i, p) in pts.iter().enumerate() {
        for (j, q) in pts.iter().enumerate() {
            assert!(
                eq(&g1_add_a3(p, q), &g1_add_general_a(p, q)),
                "g1_add_a3 != g1_add_general_a at ({i}, {j})"
            );
        }
    }
}

#[test]
fn a3_double_matches_general_a() {
    for (i, p) in test_points().iter().enumerate() {
        assert!(
            eq(&g1_double_a3(p), &g1_add_general_a(p, p)),
            "g1_double_a3 != g1_add_general_a(p, p) at {i}"
        );
    }
}

#[test]
fn a3_exceptional_cases() {
    let o = g1_identity();
    let g = g1_generator();
    let p = ref_mul(&[7, 0, 0, 0], &g);
    let np = g1_neg(&p);

    for (name, a, b) in [
        ("O + O", o, o),
        ("P + O", p, o),
        ("O + P", o, p),
        ("P + (-P)", p, np),
        ("(-P) + P", np, p),
        ("P + P", p, p),
    ] {
        assert!(
            eq(&g1_add_a3(&a, &b), &g1_add_general_a(&a, &b)),
            "g1_add_a3 disagrees on {name}"
        );
    }

    assert!(eq(&g1_double_a3(&o), &g1_add_general_a(&o, &o)), "2*O");
    assert!(g1_is_identity(&g1_double_a3(&o)), "2*O is not the identity");
    assert!(g1_is_identity(&g1_add_a3(&p, &np)), "P + (-P) is not O");
    // P + O is projectively equal to P, not triple-equal: the complete
    // formula returns a rescaled representative.
    assert!(proj_eq(&g1_add_a3(&p, &o), &p), "P + O != P projectively");
}

#[test]
fn default_path_is_a3() {
    let g = g1_generator();
    let p = ref_mul(&[11, 0, 0, 0], &g);
    assert!(eq(&g1_add(&p, &g), &g1_add_a3(&p, &g)));
    assert!(eq(&g1_double(&p), &g1_double_a3(&p)));
}

#[test]
fn scalar_mul_matches_reference_ladder() {
    let g = g1_generator();
    for k in [1u64, 2, 3, 7, 1023, u64::MAX] {
        let s = [k, 0, 0, 0];
        let want = ref_mul(&s, &g);
        assert!(proj_eq(&g1_scalar_mul(&s, &g), &want), "ladder differs at k = {k}");
        assert!(
            proj_eq(&g1_scalar_mul_base(&s), &want),
            "fixed base differs at k = {k}"
        );
    }
}

#[cfg(feature = "extracted")]
mod extracted {
    use super::*;
    use p224::g1_a3_extracted::{p224_g1_add_a3_extracted, p224_g1_double_a3_extracted};

    fn ser(p: &G1) -> [u8; 96] {
        let mut out = [0u8; 96];
        for (i, w) in p.x.0.iter().enumerate() {
            out[8 * i..8 * i + 8].copy_from_slice(&w.to_le_bytes());
        }
        for (i, w) in p.y.0.iter().enumerate() {
            out[32 + 8 * i..32 + 8 * i + 8].copy_from_slice(&w.to_le_bytes());
        }
        for (i, w) in p.z.0.iter().enumerate() {
            out[64 + 8 * i..64 + 8 * i + 8].copy_from_slice(&w.to_le_bytes());
        }
        out
    }

    #[test]
    fn extracted_a3_add_matches_handwritten() {
        let pts = test_points();
        for (i, p) in pts.iter().enumerate() {
            for (j, q) in pts.iter().enumerate() {
                let expected = ser(&g1_add_general_a(p, q));
                let mut out = [0u8; 96];
                let mut a = ser(p);
                let mut b = ser(q);
                p224_g1_add_a3_extracted(&mut out, &mut a, &mut b);
                assert_eq!(out, expected, "extracted a3 add differs at ({i}, {j})");
                assert_eq!(a, ser(p));
                assert_eq!(b, ser(q));
            }
        }
    }

    #[test]
    fn extracted_a3_double_matches_handwritten() {
        for (i, p) in test_points().iter().enumerate() {
            let expected = ser(&g1_add_general_a(p, p));
            let mut out = [0u8; 96];
            let mut a = ser(p);
            p224_g1_double_a3_extracted(&mut out, &mut a);
            assert_eq!(out, expected, "extracted a3 double differs at {i}");
            assert_eq!(a, ser(p));
        }
    }

    /// The `cB` byte literal of the emitted body must be `B_MONT`, read
    /// little-endian.
    #[test]
    fn extracted_b_literal_matches_b_mont() {
        let cb: [u8; 32] = [
            205, 89, 192, 99, 246, 205, 104, 231, 16, 19, 240, 204, 243, 194, 122, 16, 81, 129,
            82, 200, 152, 186, 206, 61, 147, 47, 192, 127, 0, 0, 0, 0,
        ];
        let mut limbs = [0u64; 4];
        for (i, w) in limbs.iter_mut().enumerate() {
            *w = u64::from_le_bytes(cb[8 * i..8 * i + 8].try_into().unwrap());
        }
        assert_eq!(B_MONT.0, limbs, "B_MONT vs g1_a3_extracted cB");
    }
}
