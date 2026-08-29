//! Differential test: the Rocq-emitted `p224_g1_add_extracted`
//! (`src/g1_extracted.rs`, generated from
//! `src/Bedrock/Curve/NistG1AddRustCmd.v`) against the hand-written
//! `group::g1_add`.  Byte-identical outputs expected.
//!
//! Run with: cargo test -p p224-safe-rust --features extracted
#![cfg(feature = "extracted")]

use p224::group::*;
use p224::g1_extracted::p224_g1_add_extracted;

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
fn extracted_add_matches_handwritten() {
    let g = g1_generator();
    let g2 = g1_add_general_a(&g, &g);
    let g3 = g1_add_general_a(&g2, &g);
    let pts = [g1_identity(), g, g2, g3, g1_neg(&g)];
    for p in &pts {
        for q in &pts {
            let expected = ser(&g1_add_general_a(p, q));
            let mut out = [0u8; 96];
            let mut a = ser(p);
            let mut b = ser(q);
            p224_g1_add_extracted(&mut out, &mut a, &mut b);
            assert_eq!(out, expected, "extracted != handwritten");
            assert_eq!(a, ser(p));
            assert_eq!(b, ser(q));
        }
    }
}
