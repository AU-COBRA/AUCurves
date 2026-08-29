//! Microbenchmarks for the P-256 field and group operations.
//!
//! Run with:
//!   cargo run --release --example bench -p p256-safe-rust
//!   cargo run --release --example bench -p p256-safe-rust --features extracted
//!
//! Each measurement warms up for `iters / 10` calls, then times `iters`
//! calls and reports nanoseconds per operation.  Inputs and outputs pass
//! through `std::hint::black_box` so the optimizer cannot hoist the work out
//! of the loop.  No external crates.

use p256::group::*;
use p256::{fp_add, fp_inv, fp_mul, fp_square, fp_to_montgomery, Fp, FpRaw};
use std::hint::black_box;
use std::time::Instant;

fn time<F: FnMut()>(label: &str, iters: u64, mut f: F) {
    for _ in 0..(iters / 10 + 1) {
        f();
    }
    let start = Instant::now();
    for _ in 0..iters {
        f();
    }
    let elapsed = start.elapsed();
    println!(
        "{:<28} {:>12.1} ns/op   ({} iters)",
        label,
        elapsed.as_nanos() as f64 / iters as f64,
        iters
    );
}

fn to_mont(canon: [u64; 4]) -> Fp {
    let mut out = Fp([0u64; 4]);
    fp_to_montgomery(&mut out, &FpRaw(canon));
    out
}

fn main() {
    println!("P-256 (secp256r1) — 4 x u64 Montgomery, R = 2^256");
    #[cfg(feature = "extracted")]
    println!("feature: extracted (Rocq-emitted g1_add compiled in)");
    #[cfg(not(feature = "extracted"))]
    println!("feature: default (hand-written g1_add only)");
    println!();

    let x = to_mont(GX_CANON);
    let y = to_mont(GY_CANON);

    // ---------------- field ----------------
    let mut out = Fp([0u64; 4]);
    time("fp_add", 20_000_000, || {
        fp_add(black_box(&mut out), black_box(&x), black_box(&y))
    });
    time("fp_mul", 20_000_000, || {
        fp_mul(black_box(&mut out), black_box(&x), black_box(&y))
    });
    time("fp_square", 20_000_000, || {
        fp_square(black_box(&mut out), black_box(&x))
    });
    time("fp_inv (divstep)", 200_000, || {
        fp_inv(black_box(&mut out), black_box(&x))
    });

    // ---------------- group ----------------
    let g = g1_generator();
    let g2 = g1_double(&g);
    let mut acc = g2;
    time("g1_add", 2_000_000, || {
        acc = g1_add(black_box(&acc), black_box(&g))
    });
    time("g1_double", 2_000_000, || {
        acc = g1_double(black_box(&acc))
    });
    black_box(&acc);

    let mut k = [0u8; 32];
    k[0] = 0x1a;
    for (i, b) in k.iter_mut().enumerate().skip(1) {
        *b = (i as u8).wrapping_mul(37).wrapping_add(11);
    }
    time("g1_scalar_mul (256-bit)", 2_000, || {
        acc = g1_scalar_mul(black_box(&k), black_box(&g))
    });
    black_box(&acc);

    // ------------- extracted add -------------
    #[cfg(feature = "extracted")]
    {
        use p256::g1_extracted::p256_g1_add_extracted;
        fn ser(pt: &G1) -> [u8; 96] {
            let mut out = [0u8; 96];
            for (i, w) in pt.x.0.iter().enumerate() {
                out[8 * i..8 * i + 8].copy_from_slice(&w.to_le_bytes());
            }
            for (i, w) in pt.y.0.iter().enumerate() {
                out[32 + 8 * i..32 + 8 * i + 8].copy_from_slice(&w.to_le_bytes());
            }
            for (i, w) in pt.z.0.iter().enumerate() {
                out[64 + 8 * i..64 + 8 * i + 8].copy_from_slice(&w.to_le_bytes());
            }
            out
        }
        let mut a = ser(&g2);
        let mut b = ser(&g);
        let mut o = [0u8; 96];
        time("g1_add (extracted)", 2_000_000, || {
            p256_g1_add_extracted(black_box(&mut o), black_box(&mut a), black_box(&mut b))
        });
        black_box(&o);
    }
}
