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
//!   cargo test -p p256-safe-rust --test a3_diff
//!   cargo test -p p256-safe-rust --test a3_diff --features extracted

use p256::group::*;
use p256::{fp_to_montgomery, Fp, FpRaw};

// ---------------------------------------------------------------------------
// Test-point construction (all through the general-a reference path, so the
// inputs to the comparison are never produced by the code under test)
// ---------------------------------------------------------------------------

fn hex_to_fp(s: &str) -> Fp {
    let bytes: Vec<u8> = (0..s.len() / 2)
        .map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap())
        .collect();
    // big-endian hex -> little-endian u64 limbs
    let mut limbs = [0u64; 4];
    for (i, limb) in limbs.iter_mut().enumerate() {
        let end = bytes.len() - 8 * i;
        let mut w = [0u8; 8];
        w.copy_from_slice(&bytes[end - 8..end]);
        *limb = u64::from_be_bytes(w);
    }
    let mut out = Fp([0u64; 4]);
    fp_to_montgomery(&mut out, &FpRaw(limbs));
    out
}

/// `k * G` by MSB-first double-and-add using only `g1_add_general_a`.
fn ref_mul(k: &[u8; 32], p: &G1) -> G1 {
    let mut acc = g1_identity();
    for i in 0..256 {
        acc = g1_add_general_a(&acc, &acc);
        if (k[i / 8] >> (7 - (i % 8))) & 1 == 1 {
            acc = g1_add_general_a(&acc, p);
        }
    }
    acc
}

fn scalar(k: u64) -> [u8; 32] {
    let mut s = [0u8; 32];
    s[24..32].copy_from_slice(&k.to_be_bytes());
    s
}

/// The published NIST P-256 `k*G` vectors used by `tests/kat_vectors.rs`,
/// as projective points with Z = 1, plus multiples reached by repeated
/// general-a addition, plus the exceptional inputs.
fn test_points() -> Vec<G1> {
    let g = g1_generator();
    let mut pts = vec![g1_identity(), g];

    // KAT affine vectors (FIPS/SEC published k*G table, k = 2, 3, 5, 10).
    let kat: [(&str, &str); 4] = [
        (
            "7cf27b188d034f7e8a52380304b51ac3c08969e277f21b35a60b48fc47669978",
            "07775510db8ed040293d9ac69f7430dbba7dade63ce982299e04b79d227873d1",
        ),
        (
            "5ecbe4d1a6330a44c8f7ef951d4bf165e6c6b721efada985fb41661bc6e7fd6c",
            "8734640c4998ff7e374b06ce1a64a2ecd82ab036384fb83d9a79b127a27d5032",
        ),
        (
            "51590b7a515140d2d784c85608668fdfef8c82fd1f5be52421554a0dc3d033ed",
            "e0c17da8904a727d8ae1bf36bf8a79260d012f00d4d80888d1d0bb44fda16da4",
        ),
        (
            "cef66d6b2a3a993e591214d1ea223fb545ca6c471c48306e4c36069404c5723f",
            "878662a229aaae906e123cdd9d3b4c10590ded29fe751eeeca34bbaa44af0773",
        ),
    ];
    for (x, y) in kat.iter() {
        pts.push(g1_from_affine(&hex_to_fp(x), &hex_to_fp(y)));
    }

    // The KBIG regression anchor of tests/kat_vectors.rs.
    let kbig: [u8; 32] = [
        0x1a, 0x2b, 0x3c, 0x4d, 0x5e, 0x6f, 0x70, 0x81, 0x92, 0xa3, 0xb4, 0xc5, 0xd6, 0xe7,
        0xf8, 0x09, 0x1a, 0x2b, 0x3c, 0x4d, 0x5e, 0x6f, 0x70, 0x81, 0x92, 0xa3, 0xb4, 0xc5,
        0xd6, 0xe7, 0xf8, 0x09,
    ];
    pts.push(ref_mul(&kbig, &g));

    // Points with a non-trivial Z, reached by repeated general-a addition.
    let mut acc = g;
    for _ in 0..6 {
        acc = g1_add_general_a(&acc, &g);
        pts.push(acc);
    }

    // Deterministic pseudo-random multiples (xorshift64), so the test
    // covers scalars outside any table.
    let mut state: u64 = 0x9e37_79b9_7f4a_7c15;
    for _ in 0..6 {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        let mut s = [0u8; 32];
        for c in s.chunks_mut(8) {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            c.copy_from_slice(&state.to_be_bytes());
        }
        pts.push(ref_mul(&s, &g));
    }

    // Negations, which give the P + (-P) exceptional case below.
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
    p256::fp_mul(&mut l, &p.x, &q.z);
    p256::fp_mul(&mut r, &q.x, &p.z);
    if l.0 != r.0 {
        return false;
    }
    p256::fp_mul(&mut l, &p.y, &q.z);
    p256::fp_mul(&mut r, &q.y, &p.z);
    l.0 == r.0
}

fn show(p: &G1) -> String {
    format!("({:016x?}, {:016x?}, {:016x?})", p.x.0, p.y.0, p.z.0)
}

// ---------------------------------------------------------------------------
// Hand-written A3 against the general-a reference
// ---------------------------------------------------------------------------

#[test]
fn a3_add_matches_general_a() {
    let pts = test_points();
    for (i, p) in pts.iter().enumerate() {
        for (j, q) in pts.iter().enumerate() {
            let want = g1_add_general_a(p, q);
            let got = g1_add_a3(p, q);
            assert!(
                eq(&got, &want),
                "g1_add_a3 != g1_add_general_a at ({i}, {j}):\n  a3      {}\n  general {}",
                show(&got),
                show(&want)
            );
        }
    }
}

#[test]
fn a3_double_matches_general_a() {
    for (i, p) in test_points().iter().enumerate() {
        let want = g1_add_general_a(p, p);
        let got = g1_double_a3(p);
        assert!(
            eq(&got, &want),
            "g1_double_a3 != g1_add_general_a(p, p) at {i}:\n  a3      {}\n  general {}",
            show(&got),
            show(&want)
        );
    }
}

/// The exceptional inputs, called out separately so a failure names the
/// case rather than an index.
#[test]
fn a3_exceptional_cases() {
    let o = g1_identity();
    let g = g1_generator();
    let p = ref_mul(&scalar(7), &g);
    let np = g1_neg(&p);

    let cases: [(&str, G1, G1); 6] = [
        ("O + O", o, o),
        ("P + O", p, o),
        ("O + P", o, p),
        ("P + (-P)", p, np),
        ("(-P) + P", np, p),
        ("P + P", p, p),
    ];
    for (name, a, b) in cases.iter() {
        let want = g1_add_general_a(a, b);
        let got = g1_add_a3(a, b);
        assert!(eq(&got, &want), "g1_add_a3 disagrees on {name}");
    }

    // Doubling the identity, and the identity's own completeness.
    assert!(eq(&g1_double_a3(&o), &g1_add_general_a(&o, &o)), "2*O");
    assert!(g1_is_identity(&g1_double_a3(&o)), "2*O is not the identity");
    assert!(g1_is_identity(&g1_add_a3(&p, &np)), "P + (-P) is not O");
    // P + O is projectively equal to P, not triple-equal: the complete
    // formula returns a rescaled representative, exactly as the general-a
    // body does.
    assert!(proj_eq(&g1_add_a3(&p, &o), &p), "P + O != P projectively");
    assert!(proj_eq(&g1_add_a3(&o, &p), &p), "O + P != P projectively");
}

/// The default entry points must be the a = -3 bodies.
#[test]
fn default_path_is_a3() {
    let g = g1_generator();
    let p = ref_mul(&scalar(11), &g);
    assert!(eq(&g1_add(&p, &g), &g1_add_a3(&p, &g)));
    assert!(eq(&g1_double(&p), &g1_double_a3(&p)));
}

/// The scalar-multiplication entry points must still agree with the
/// general-a reference ladder end to end.
#[test]
fn scalar_mul_matches_reference_ladder() {
    let g = g1_generator();
    for k in [1u64, 2, 3, 7, 1023, u64::MAX] {
        let s = scalar(k);
        let want = ref_mul(&s, &g);
        assert!(eq(&g1_scalar_mul(&s, &g), &want), "ladder differs at k = {k}");
        // The fixed-base path is projectively equal, not triple-equal.
        let base = g1_scalar_mul_base(&s);
        assert!(
            g1_is_identity(&base) == g1_is_identity(&want),
            "fixed base identity mismatch at k = {k}"
        );
        if !g1_is_identity(&want) {
            let (bx, by) = g1_to_affine(&base).unwrap();
            let (wx, wy) = g1_to_affine(&want).unwrap();
            assert_eq!((bx.0, by.0), (wx.0, wy.0), "fixed base differs at k = {k}");
        }
    }
}

// ---------------------------------------------------------------------------
// Rocq-emitted A3 bodies against the hand-written A3
// ---------------------------------------------------------------------------

#[cfg(feature = "extracted")]
mod extracted {
    use super::*;
    use p256::g1_a3_extracted::{p256_g1_add_a3_extracted, p256_g1_double_a3_extracted};

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
                p256_g1_add_a3_extracted(&mut out, &mut a, &mut b);
                assert_eq!(out, expected, "extracted a3 add differs at ({i}, {j})");
                // inputs must be preserved
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
            p256_g1_double_a3_extracted(&mut out, &mut a);
            assert_eq!(out, expected, "extracted a3 double differs at {i}");
            assert_eq!(a, ser(p));
        }
    }

    /// The `cB` byte literal of the emitted body must be `B_MONT`, read
    /// little-endian — the same drift guard the general-a body has for
    /// `cA` / `cB3`.
    #[test]
    fn extracted_b_literal_matches_b_mont() {
        let cb: [u8; 32] = [
            223, 189, 196, 41, 98, 223, 156, 216, 144, 48, 132, 120, 205, 5, 240, 172, 214,
            46, 33, 247, 171, 32, 162, 229, 52, 72, 135, 4, 29, 6, 48, 220,
        ];
        let mut limbs = [0u64; 4];
        for (i, w) in limbs.iter_mut().enumerate() {
            *w = u64::from_le_bytes(cb[8 * i..8 * i + 8].try_into().unwrap());
        }
        assert_eq!(B_MONT.0, limbs, "B_MONT vs g1_a3_extracted cB");
    }
}
