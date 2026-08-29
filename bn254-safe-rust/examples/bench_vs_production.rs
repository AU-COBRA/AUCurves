//! Benchmark our bn254-safe-rust (extracted from verified bedrock2) against
//! arkworks-rs/ark-bn254 (production Rust implementation).
//!
//! Run with:
//!   cargo run --release --example bench_vs_production
//!
//! Requires `ark-bn254` + `ark-ec` + `ark-ff` in [dev-dependencies].
//!
//! ## Measurement notes
//!
//! Both arms report **TSC cycles** alongside wall-clock nanoseconds.  This
//! machine reports `constant_tsc` + `nonstop_tsc`, so the counter ticks at a
//! fixed reference rate independent of the core's actual frequency.  That
//! makes cycle counts far more stable than nanoseconds when the machine is
//! busy — which it usually is here.  Read the cycle column as the primary
//! result.  (These are *reference* cycles, not retired core cycles; a true
//! core-cycle count needs perf_event_open, and `perf_event_paranoid` is 4
//! on this host, so it is unavailable without a root sysctl.)
//!
//! ## Why the field loops look the way they do
//!
//! An earlier version of this file timed the arkworks multiply as
//!
//!     for _ in 0..N { let _ = black_box(a * b); }
//!
//! with `a` and `b` bound outside the loop.  `black_box` on the *result*
//! stops the value being discarded but does nothing to stop LLVM hoisting
//! the loop-invariant `a * b` out of the loop, so the loop body became
//! empty and the arm reported 1.2 ns/op — about five cycles, which no
//! 254-bit Montgomery multiply can achieve.  Our arm wrote through
//! `&mut c` each iteration and was not hoisted, so the two arms measured
//! different things and the reported ratio (16.5x) was meaningless.
//!
//! Both arms are now the same shape: a serial dependency chain where each
//! iteration consumes the previous result, with `black_box` on the
//! *operands* so nothing is loop-invariant.  This measures multiply
//! latency for both.  `assert_plausible` below fails the run rather than
//! printing another impossible number.
use bn254::*;
use std::hint::black_box;
use std::time::Instant;

// Arkworks imports
use ark_bn254::{Bn254, G1Projective, G2Projective};
use ark_ec::{pairing::Pairing, PrimeGroup};
use ark_ff::UniformRand;

const N_PAIRING: usize = 100;
const N_FP_MUL: usize = 1_000_000;

/// Serialising TSC read.  `lfence` on both sides keeps the counter read
/// from drifting across the region being timed.
#[inline]
fn rdtsc() -> u64 {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        use core::arch::x86_64::{_mm_lfence, _rdtsc};
        _mm_lfence();
        let t = _rdtsc();
        _mm_lfence();
        t
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        0
    }
}

/// A single measurement: cycles per op and nanoseconds per op.
#[derive(Clone, Copy)]
struct M {
    cyc: f64,
    ns: f64,
}

/// Refuse to report a field-multiply figure that cannot be real.
///
/// A 4x64 Montgomery multiply is 16 `mul`-class instructions plus the
/// reduction; nothing under ~10 cycles is achievable.  A number below the
/// floor means the loop was optimised away, which is the bug described in
/// the module comment above.
fn assert_plausible(label: &str, m: M) {
    const FLOOR_CYCLES: f64 = 10.0;
    assert!(
        m.cyc >= FLOOR_CYCLES,
        "{label}: {:.2} cycles/op is below the {FLOOR_CYCLES} cycle floor for a \
         254-bit Montgomery multiply — the timing loop was optimised away. \
         Check that the operands are inside black_box and that each iteration \
         consumes the previous result.",
        m.cyc
    );
}

fn bench_ours() -> (M, M) {
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

    // Warmup
    let mut out = Fp12::zero();
    pairing(&mut out, &p_x, &p_y, &q_x, &q_y);

    let a = Fp([0x7a17caa950ad28d7, 0x1f6ac17ae15521b9, 0x334bea4e696bd284, 0x2a1f6744ce179d8e]);
    let b = Fp([0xe4b1c5ae034e46ca, 0x9cdb2d3b64716da7, 0x47d8eb76d8dd067e, 0x15d0085520f5bbc3]);

    // Latency chain: acc <- acc * b, operands black_boxed so nothing is
    // loop-invariant and nothing can be hoisted.
    let mut acc = a;
    let mut c = Fp::zero();
    let t0 = rdtsc();
    let w0 = Instant::now();
    for _ in 0..N_FP_MUL {
        fp_mul(&mut c, black_box(&acc), black_box(&b));
        acc = c;
    }
    let mul = M {
        cyc: (rdtsc() - t0) as f64 / N_FP_MUL as f64,
        ns: w0.elapsed().as_nanos() as f64 / N_FP_MUL as f64,
    };
    black_box(&acc);

    let t0 = rdtsc();
    let w0 = Instant::now();
    for _ in 0..N_PAIRING {
        pairing(&mut out, black_box(&p_x), black_box(&p_y), black_box(&q_x), black_box(&q_y));
    }
    let pair = M {
        cyc: (rdtsc() - t0) as f64 / N_PAIRING as f64,
        ns: w0.elapsed().as_nanos() as f64 / N_PAIRING as f64,
    };
    black_box(&out);

    (mul, pair)
}

fn bench_arkworks() -> (M, M) {
    let mut rng = ark_std::test_rng();
    let p = G1Projective::generator();
    let q = G2Projective::generator();

    // Warmup
    let _ = Bn254::pairing(p, q);

    use ark_bn254::Fq;
    let a = Fq::rand(&mut rng);
    let b = Fq::rand(&mut rng);

    // Same shape as the arm above: serial chain, operands black_boxed.
    let mut acc = a;
    let t0 = rdtsc();
    let w0 = Instant::now();
    for _ in 0..N_FP_MUL {
        acc = black_box(acc) * black_box(b);
    }
    let mul = M {
        cyc: (rdtsc() - t0) as f64 / N_FP_MUL as f64,
        ns: w0.elapsed().as_nanos() as f64 / N_FP_MUL as f64,
    };
    black_box(acc);

    let t0 = rdtsc();
    let w0 = Instant::now();
    for _ in 0..N_PAIRING {
        let _ = black_box(Bn254::pairing(black_box(p), black_box(q)));
    }
    let pair = M {
        cyc: (rdtsc() - t0) as f64 / N_PAIRING as f64,
        ns: w0.elapsed().as_nanos() as f64 / N_PAIRING as f64,
    };

    (mul, pair)
}

fn main() {
    println!("BN254 benchmark: our extraction vs. arkworks");
    println!("cycles are invariant-TSC reference cycles; read them, not the ns\n");

    let (ours_mul, ours_pair) = bench_ours();
    let (ark_mul, ark_pair) = bench_arkworks();

    assert_plausible("ours Fp mul", ours_mul);
    assert_plausible("arkworks Fp mul", ark_mul);

    println!(
        "{:<20} {:>12} {:>11} {:>12} {:>11} {:>9}",
        "op", "ours (cyc)", "ours", "ark (cyc)", "arkworks", "ratio"
    );
    println!("{:-<80}", "");
    println!(
        "{:<20} {:>12.1} {:>8.1} ns {:>12.1} {:>8.1} ns {:>8.2}x",
        "Fp mul", ours_mul.cyc, ours_mul.ns, ark_mul.cyc, ark_mul.ns,
        ours_mul.cyc / ark_mul.cyc
    );
    println!(
        "{:<20} {:>12.0} {:>8.1} us {:>12.0} {:>8.1} us {:>8.2}x",
        "Pairing (full)", ours_pair.cyc, ours_pair.ns / 1000.0,
        ark_pair.cyc, ark_pair.ns / 1000.0,
        ours_pair.cyc / ark_pair.cyc
    );
    println!("\n(ratio = how many times slower ours is vs. arkworks, on cycles)");
    println!("Both field loops are serial latency chains with black_boxed operands.");
}
