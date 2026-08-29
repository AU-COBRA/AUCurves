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
//!   cargo test -p p384-safe-rust --test a3_diff
//!   cargo test -p p384-safe-rust --test a3_diff --features extracted

use p384::group::*;
use p384::{fp_mul, fp_to_montgomery, Fp, FpRaw};

// The NIST P-384 k*G vectors of tests/kat_vectors.rs.
const K2_X: &str = concat!(
    "08d999057ba3d2d969260045c55b97f089025959a6f434d6",
    "51d207d19fb96e9e4fe0e86ebe0e64f85b96a9c75295df61"
);
const K2_Y: &str = concat!(
    "8e80f1fa5b1b3cedb7bfe8dffd6dba74b275d875bc6cc43e",
    "904e505f256ab4255ffd43e94d39e22d61501e700a940e80"
);
const K3_X: &str = concat!(
    "077a41d4606ffa1464793c7e5fdc7d98cb9d3910202dcd06",
    "bea4f240d3566da6b408bbae5026580d02d7e5c70500c831"
);
const K3_Y: &str = concat!(
    "c995f7ca0b0c42837d0bbe9602a9fc998520b41c85115aa5",
    "f7684c0edc111eacc24abd6be4b5d298b65f28600a2f1df1"
);
const K5_X: &str = concat!(
    "11de24a2c251c777573cac5ea025e467f208e51dbff98fc5",
    "4f6661cbe56583b037882f4a1ca297e60abcdbc3836d84bc"
);
const K5_Y: &str = concat!(
    "8fa696c77440f92d0f5837e90a00e7c5284b447754d5dee8",
    "8c986533b6901aeb3177686d0ae8fb33184414abe6c1713a"
);
const K10_X: &str = concat!(
    "a669c5563bd67eec678d29d6ef4fde864f372d90b79b9e88",
    "931d5c29291238cced8e85ab507bf91aa9cb2d13186658fb"
);
const K10_Y: &str = concat!(
    "a988b72ae7c1279f22d9083db5f0ecddf70119550c183c31",
    "c502df78c3b705a8296d8195248288d997784f6ab73a21dd"
);
const KBIG_HEX: &str = concat!(
    "1a2b3c4d5e6f708192a3b4c5d6e7f8091a2b3c4d5e6f7081",
    "92a3b4c5d6e7f8090f1e2d3c4b5a69788796a5b4c3d2e1f0"
);

/// Big-endian hex -> canonical little-endian u64 limbs (zero-padded).
fn hex_to_limbs(s: &str) -> [u64; 6] {
    let bytes: Vec<u8> = (0..s.len() / 2)
        .map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap())
        .collect();
    let mut be = [0u8; 48];
    be[48 - bytes.len()..].copy_from_slice(&bytes);
    let mut limbs = [0u64; 6];
    for (i, limb) in limbs.iter_mut().enumerate() {
        let end = 48 - 8 * i;
        *limb = u64::from_be_bytes(be[end - 8..end].try_into().unwrap());
    }
    limbs
}

fn hex_to_fp(s: &str) -> Fp {
    let mut out = Fp([0u64; 6]);
    fp_to_montgomery(&mut out, &FpRaw(hex_to_limbs(s)));
    out
}

/// `k * P` by MSB-first double-and-add using only `g1_add_general_a`.
fn ref_mul(k: &[u64; 6], p: &G1) -> G1 {
    let mut acc = g1_identity();
    for i in (0..384).rev() {
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

    for (x, y) in [(K2_X, K2_Y), (K3_X, K3_Y), (K5_X, K5_Y), (K10_X, K10_Y)] {
        pts.push(g1_from_affine(&hex_to_fp(x), &hex_to_fp(y)));
    }
    pts.push(ref_mul(&hex_to_limbs(KBIG_HEX), &g));

    // Points with a non-trivial Z, reached by repeated general-a addition.
    let mut acc = g;
    for _ in 0..4 {
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
    for _ in 0..4 {
        let k = [next(), next(), next(), next(), next(), next() >> 8];
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
    let mut l = Fp([0u64; 6]);
    let mut r = Fp([0u64; 6]);
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
    let p = ref_mul(&[7, 0, 0, 0, 0, 0], &g);
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
    let p = ref_mul(&[11, 0, 0, 0, 0, 0], &g);
    assert!(eq(&g1_add(&p, &g), &g1_add_a3(&p, &g)));
    assert!(eq(&g1_double(&p), &g1_double_a3(&p)));
}

#[test]
fn scalar_mul_matches_reference_ladder() {
    let g = g1_generator();
    for k in [1u64, 2, 3, 7, 1023, u64::MAX] {
        let s = [k, 0, 0, 0, 0, 0];
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
    use p384::g1_a3_extracted::{p384_g1_add_a3_extracted, p384_g1_double_a3_extracted};

    fn ser(p: &G1) -> [u8; 144] {
        let mut out = [0u8; 144];
        for (i, w) in p.x.0.iter().enumerate() {
            out[8 * i..8 * i + 8].copy_from_slice(&w.to_le_bytes());
        }
        for (i, w) in p.y.0.iter().enumerate() {
            out[48 + 8 * i..48 + 8 * i + 8].copy_from_slice(&w.to_le_bytes());
        }
        for (i, w) in p.z.0.iter().enumerate() {
            out[96 + 8 * i..96 + 8 * i + 8].copy_from_slice(&w.to_le_bytes());
        }
        out
    }

    #[test]
    fn extracted_a3_add_matches_handwritten() {
        let pts = test_points();
        for (i, p) in pts.iter().enumerate() {
            for (j, q) in pts.iter().enumerate() {
                let expected = ser(&g1_add_general_a(p, q));
                let mut out = [0u8; 144];
                let mut a = ser(p);
                let mut b = ser(q);
                p384_g1_add_a3_extracted(&mut out, &mut a, &mut b);
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
            let mut out = [0u8; 144];
            let mut a = ser(p);
            p384_g1_double_a3_extracted(&mut out, &mut a);
            assert_eq!(out, expected, "extracted a3 double differs at {i}");
            assert_eq!(a, ser(p));
        }
    }

    /// The `cB` byte literal of the emitted body must be `B_MONT`, read
    /// little-endian.
    #[test]
    fn extracted_b_literal_matches_b_mont() {
        let cb: [u8; 48] = [
            204, 45, 65, 157, 113, 136, 17, 8, 236, 50, 76, 122, 216, 173, 41, 247, 46, 2, 32,
            25, 155, 32, 242, 119, 226, 138, 147, 148, 238, 75, 55, 227, 148, 32, 2, 31, 244,
            33, 43, 182, 249, 191, 79, 96, 75, 17, 8, 205,
        ];
        let mut limbs = [0u64; 6];
        for (i, w) in limbs.iter_mut().enumerate() {
            *w = u64::from_le_bytes(cb[8 * i..8 * i + 8].try_into().unwrap());
        }
        assert_eq!(B_MONT.0, limbs, "B_MONT vs g1_a3_extracted cB");
    }
}
