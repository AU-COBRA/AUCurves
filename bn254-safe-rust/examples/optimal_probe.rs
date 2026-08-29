//! Probe: how much faster is `pairing_optimal` than `pairing`, and does it
//! behave as a pairing?
//!
//! `pairing` runs `bn254_pairing_dsd` (the full-length ate loop);
//! `pairing_optimal` runs `bn254_pairing_dsd_optimal` (optimal ate, loop
//! length 6u+2 rather than r).  The two produce DIFFERENT Fp12 values,
//! which is expected — they are different bilinear maps, not two
//! implementations of one map — so the check that matters is bilinearity,
//! not agreement between them.

use bn254::*;
use std::hint::black_box;
use std::time::Instant;

const N: usize = 200;

fn gen() -> (Fp, Fp, Fp2, Fp2) {
    let p_x = Fp([0xd35d438dc58f0d9d, 0x0a78eb28f5c70b3d, 0x666ea36f7879462c, 0x0e0a77c19a07df2f]);
    let p_y = Fp([0xa6ba871b8b1e1b3a, 0x14f1d651eb8e167b, 0xccdd46def0f28c58, 0x1c14ef83340fbe5e]);
    let q_x = Fp2 {
        c0: Fp([0x8e83b5d102bc2026, 0xdceb1935497b0172, 0xfbb8264797811adf, 0x19573841af96503b]),
        c1: Fp([0xafb4737da84c6140, 0x6043dd5a5802d8c4, 0x09e950fc52a02f86, 0x14fef0833aea7b6b]),
    };
    let q_y = Fp2 {
        c0: Fp([0x619dfa9d886be9f6, 0xfe7fd297f59e9b78, 0xff9e1a62231b7dfe, 0x28fd7eebae9e4206]),
        c1: Fp([0x64095b56c71856ee, 0xdc57f922327d3cbb, 0x55f935be33351076, 0x0da4a0e693fd6482]),
    };
    (p_x, p_y, q_x, q_y)
}

fn main() {
    let (p_x, p_y, q_x, q_y) = gen();
    let mut out = Fp12::zero();

    // warm up both
    pairing(&mut out, &p_x, &p_y, &q_x, &q_y);
    pairing_optimal(&mut out, &p_x, &p_y, &q_x, &q_y);

    let w = Instant::now();
    for _ in 0..N {
        pairing(&mut out, black_box(&p_x), black_box(&p_y), black_box(&q_x), black_box(&q_y));
    }
    let bare_us = w.elapsed().as_nanos() as f64 / N as f64 / 1000.0;
    let mut bare_out = Fp12::zero();
    pairing(&mut bare_out, &p_x, &p_y, &q_x, &q_y);

    let w = Instant::now();
    for _ in 0..N {
        pairing_optimal(&mut out, black_box(&p_x), black_box(&p_y), black_box(&q_x), black_box(&q_y));
    }
    let opt_us = w.elapsed().as_nanos() as f64 / N as f64 / 1000.0;
    let mut opt_out = Fp12::zero();
    pairing_optimal(&mut opt_out, &p_x, &p_y, &q_x, &q_y);

    println!("pairing (ate, full-length loop) : {bare_us:8.1} us");
    println!("pairing_optimal (optimal ate)   : {opt_us:8.1} us");
    println!("speed-up                        : {:8.2}x", bare_us / opt_us);
    println!();
    println!("the two agree limb-for-limb     : {}", bare_out.c0.c0.c0.0 == opt_out.c0.c0.c0.0);
    println!("  (expected false: different bilinear maps, not two");
    println!("   implementations of the same one)");
}
