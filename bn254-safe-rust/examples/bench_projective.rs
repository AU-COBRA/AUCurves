//! Benchmark the hand-coded projective Miller loop vs the verified
//! affine pairing.  Cross-check confirms the pairing value agrees
//! after final exponentiation (the Z-factor that accumulates in the
//! projective raw Miller vanishes in the BN final exp).
use bn254::*;
use bn254::projective::pairing_projective_hand;
use std::time::Instant;

const N_PAIR: usize = 100;

fn main() {
    let p_x = Fp([0xd35d438dc58f0d9d, 0x0a78eb28f5c70b3d, 0x666ea36f7879462c, 0x0e0a77c19a07df2f]);
    let p_y = Fp([0xa6ba871b8b1e1b3a, 0x14f1d651eb8e167b, 0xccdd46def0f28c58, 0x1c14ef83340fbe5e]);
    let q_x = Fp2 { c0: Fp([0x8e83b5d102bc2026,0xdceb1935497b0172,0xfbb8264797811adf,0x19573841af96503b]),
                    c1: Fp([0xafb4737da84c6140,0x6043dd5a5802d8c4,0x09e950fc52a02f86,0x14fef0833aea7b6b]) };
    let q_y = Fp2 { c0: Fp([0x619dfa9d886be9f6,0xfe7fd297f59e9b78,0xff9e1a62231b7dfe,0x28fd7eebae9e4206]),
                    c1: Fp([0x64095b56c71856ee,0xdc57f922327d3cbb,0x55f935be33351076,0x0da4a0e693fd6482]) };

    // Cross-check: projective pairing == affine pairing on the BN254 generators.
    let mut a = Fp12::zero();
    let mut b = Fp12::zero();
    pairing(&mut a, &p_x, &p_y, &q_x, &q_y);
    pairing_projective_hand(&mut b, &p_x, &p_y, &q_x, &q_y);
    assert_eq!(a.c0.c0.c0.0, b.c0.c0.c0.0, "projective != affine (c0.c0.c0)");
    assert_eq!(a.c1.c2.c1.0, b.c1.c2.c1.0, "projective != affine (c1.c2.c1)");
    println!("Cross-check: projective pairing == affine pairing on generators OK\n");

    // Warmup
    pairing(&mut a, &p_x, &p_y, &q_x, &q_y);
    pairing_projective_hand(&mut b, &p_x, &p_y, &q_x, &q_y);

    println!("{:<28} {:>14}", "variant", "pairing (us)");
    println!("{:-<46}", "");

    let start = Instant::now();
    for _ in 0..N_PAIR { pairing(&mut a, &p_x, &p_y, &q_x, &q_y); }
    let aff_us = start.elapsed().as_micros() as f64 / N_PAIR as f64;
    println!("{:<28} {:>11.1}", "affine (verified)", aff_us);

    let start = Instant::now();
    for _ in 0..N_PAIR { pairing_projective_hand(&mut b, &p_x, &p_y, &q_x, &q_y); }
    let proj_us = start.elapsed().as_micros() as f64 / N_PAIR as f64;
    println!("{:<28} {:>11.1}", "projective (hand-coded)", proj_us);

    println!("\nspeedup: {:.2}x", aff_us / proj_us);
}
