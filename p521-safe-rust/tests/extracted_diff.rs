//! Differential test: the Rocq-emitted `p521_g1_add_extracted`
//! (`src/g1_extracted.rs`, generated from
//! `src/Bedrock/Curve/NistG1AddRustCmd.v`) against the hand-written
//! `group::g1_add`.
//!
//! The P-521 extracted ABI is CANONICAL 66-byte little-endian field
//! elements (X ‖ Y ‖ Z, 198 bytes per point); the leaf shims carry
//! after every add/sub exactly like the hand-written `add_t`/`sub_t`
//! helpers, so canonical-byte outputs must agree exactly.
//!
//! Run with: cargo test -p p521-safe-rust --features extracted
#![cfg(feature = "extracted")]

use p521::group::*;
use p521::g1_extracted::p521_g1_add_extracted;
use p521::{fp_from_bytes, FpT};

fn ser(p: &G1) -> [u8; 198] {
    let mut out = [0u8; 198];
    out[..66].copy_from_slice(&to_bytes_t(&p.x));
    out[66..132].copy_from_slice(&to_bytes_t(&p.y));
    out[132..].copy_from_slice(&to_bytes_t(&p.z));
    out
}

fn de_fp(bs: &[u8]) -> FpT {
    let mut arr = [0u8; 66];
    arr.copy_from_slice(bs);
    let mut t = FpT([0u64; 9]);
    fp_from_bytes(&mut t, &arr);
    t
}

#[test]
fn extracted_add_matches_handwritten() {
    let g = g1_generator();
    let g2 = g1_add(&g, &g);
    let g3 = g1_add(&g2, &g);
    let pts = [g1_identity(), g, g2, g3, g1_neg(&g)];
    for p in &pts {
        for q in &pts {
            let expected = g1_add(p, q);
            let mut out = [0u8; 198];
            let mut a = ser(p);
            let mut b = ser(q);
            p521_g1_add_extracted(&mut out, &mut a, &mut b);
            // Compare canonically per coordinate.
            assert!(eq_t(&de_fp(&out[..66]), &expected.x), "X mismatch");
            assert!(eq_t(&de_fp(&out[66..132]), &expected.y), "Y mismatch");
            assert!(eq_t(&de_fp(&out[132..]), &expected.z), "Z mismatch");
            assert_eq!(a, ser(p));
            assert_eq!(b, ser(q));
        }
    }
}
