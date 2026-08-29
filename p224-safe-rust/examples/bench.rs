//! Microbenchmarks for the P-224 field and group operations.
//!
//! Run with:
//!   cargo run --release --example bench -p p224-safe-rust
//!   cargo run --release --example bench -p p224-safe-rust --features extracted
//!
//! Each measurement warms up for `iters / 10` calls, then times `iters`
//! calls and reports nanoseconds per operation.  Inputs and outputs pass
//! through `std::hint::black_box` so the optimizer cannot hoist the work out
//! of the loop.  No external crates.

use p224::group::*;
use p224::{fp_add, fp_inv, fp_mul, fp_square, fp_to_montgomery, Fp, FpRaw};
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
    println!("P-224 (secp224r1) — 4 x u64 Montgomery, R = 2^256");
    #[cfg(feature = "extracted")]
    println!("feature: extracted (Rocq-emitted g1_add compiled in)");
    #[cfg(not(feature = "extracted"))]
    println!("feature: default (hand-written g1_add only)");
    println!();

    let x = to_mont(P224_GX);
    let y = to_mont(P224_GY);

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

    let k: [u64; 4] = [
        0x0f1e_2d3c_4b5a_6978,
        0x8796_a5b4_c3d2_e1f0,
        0x1a2b_3c4d_5e6f_7081,
        0x0000_0000_02a3_b4c5,
    ];
    time("g1_scalar_mul (224-bit)", 2_000, || {
        acc = g1_scalar_mul(black_box(&k), black_box(&g))
    });
    time("g1_scalar_mul_base (224-bit)", 20_000, || {
        acc = g1_scalar_mul_base(black_box(&k))
    });
    black_box(&acc);
    println!(
        "    (fixed-base table: W={}, {} windows x {} entries = {} bytes of .rodata)",
        BASE_W, BASE_WINDOWS, BASE_TSIZE, BASE_TABLE_BYTES
    );

    // ------------- extracted add -------------
    #[cfg(feature = "extracted")]
    {
        use p224::g1_extracted::p224_g1_add_extracted;
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
            p224_g1_add_extracted(black_box(&mut o), black_box(&mut a), black_box(&mut b))
        });
        black_box(&o);

        // The Rocq-emitted w=4 wNAF driver (variable time; see
        // src/scalar_mul_extracted.rs).  Compare against the
        // "g1_scalar_mul" line above, which is the constant-time
        // width-1 double-and-add-always ladder.
        use p224::wnaf::g1_scalar_mul_wnaf;
        time("g1_scalar_mul wNAF (extr)", 2_000, || {
            acc = g1_scalar_mul_wnaf(black_box(&k), black_box(&g))
        });
        black_box(&acc);
    }
}
