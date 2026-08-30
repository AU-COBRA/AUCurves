//! Per-stage BN254 breakdown: where does the pairing gap against arkworks
//! come from?
//!
//!   cargo run --release --example bench_breakdown
//!
//! Compares each tower level (Fp, Fp2, Fp12) and each pairing stage (Miller
//! loop, full pairing) against arkworks, so the gap can be located in the
//! base field, the Fp12 layer, or the pairing plumbing.
//!
//! ## Measurement notes
//!
//! The primary column is **cycles**; nanoseconds are secondary.  Cycles come
//! from `_rdtsc` fenced by `lfence` on both sides.  This host reports
//! `constant_tsc` + `nonstop_tsc`, so the counter ticks at a fixed reference
//! rate independent of the core's actual frequency.  These are *invariant-TSC
//! reference cycles*, not retired core cycles; a true core-cycle count needs
//! `perf_event_open`, and `perf_event_paranoid` is 4 on this host, so it is
//! unavailable without a root sysctl.  Reference cycles are far more stable
//! than wall-clock nanoseconds under background load, so the ratios are
//! computed on cycles.
//!
//! Both arms run in ONE process and are INTERLEAVED: within a round, ours is
//! timed for an operation, then arkworks' is, and per row the round MINIMUM
//! over `ROUNDS` rounds is reported.
//!
//! Every field loop is a serial dependency chain — iteration `i + 1` consumes
//! the result of iteration `i` — with the *operands* inside `black_box`.
//! Before this file was converted it used `std::ptr::read_volatile` on the
//! arkworks operands and a bare call on ours, so the two arms were not the
//! same shape: the volatile read forces a reload every iteration that our arm
//! did not pay for.  A serial chain with `black_box`ed operands defeats
//! hoisting on both arms with the same instruction budget.  `assert_floor`
//! fails the run rather than printing a figure only an optimised-away loop
//! could produce.
use bn254::*;
use std::hint::black_box;
use std::time::Instant;

use ark_bn254::{Bn254, Fq, Fq12, Fq2, G1Affine, G1Projective, G2Affine, G2Projective};
use ark_ec::{bn::G2Prepared, pairing::Pairing, PrimeGroup};
use ark_ff::{Field, UniformRand};

const ROUNDS: usize = 5;
const N: u64 = 200_000;
const N12: u64 = 5_000;
const N_PAIR: u64 = 30;

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

/// A single measurement: reference cycles per op and nanoseconds per op.
#[derive(Clone, Copy)]
struct M {
    cyc: f64,
    ns: f64,
}

impl M {
    fn worst() -> Self {
        M { cyc: f64::INFINITY, ns: f64::INFINITY }
    }
    fn min(self, o: Self) -> Self {
        if o.cyc < self.cyc {
            o
        } else {
            self
        }
    }
}

fn round<F: FnMut()>(iters: u64, mut f: F) -> M {
    let t0 = rdtsc();
    let w0 = Instant::now();
    for _ in 0..iters {
        f();
    }
    M {
        cyc: (rdtsc() - t0) as f64 / iters as f64,
        ns: w0.elapsed().as_nanos() as f64 / iters as f64,
    }
}

fn assert_floor(label: &str, m: M, floor: f64) {
    assert!(
        m.cyc >= floor,
        "{label}: {:.2} cycles/op is below the {floor} cycle floor — the timing \
         loop was optimised away.  Check that the operands are inside black_box \
         and that each iteration consumes the previous result.",
        m.cyc
    );
}

fn main() {
    println!("BN254 per-stage benchmark: ours vs ark-bn254 — one process,");
    println!("{ROUNDS} interleaved rounds, per-row minimum.");
    println!();
    println!("cycles are invariant-TSC REFERENCE cycles (constant_tsc + nonstop_tsc),");
    println!("not retired core cycles.  Ratios are computed on cycles.");
    println!();

    // ---- Setup: ours ----
    let p_x = Fp([0xd35d438dc58f0d9d, 0x0a78eb28f5c70b3d, 0x666ea36f7879462c, 0x0e0a77c19a07df2f]);
    let p_y = Fp([0xa6ba871b8b1e1b3a, 0x14f1d651eb8e167b, 0xccdd46def0f28c58, 0x1c14ef83340fbe5e]);
    let q_x = Fp2 { c0: Fp([0x8e83b5d102bc2026,0xdceb1935497b0172,0xfbb8264797811adf,0x19573841af96503b]),
                    c1: Fp([0xafb4737da84c6140,0x6043dd5a5802d8c4,0x09e950fc52a02f86,0x14fef0833aea7b6b]) };
    let q_y = Fp2 { c0: Fp([0x619dfa9d886be9f6,0xfe7fd297f59e9b78,0xff9e1a62231b7dfe,0x28fd7eebae9e4206]),
                    c1: Fp([0x64095b56c71856ee,0xdc57f922327d3cbb,0x55f935be33351076,0x0da4a0e693fd6482]) };

    let a = Fp([0x7a17caa950ad28d7, 0x1f6ac17ae15521b9, 0x334bea4e696bd284, 0x2a1f6744ce179d8e]);
    let b = Fp([0xe4b1c5ae034e46ca, 0x9cdb2d3b64716da7, 0x47d8eb76d8dd067e, 0x15d0085520f5bbc3]);

    let a2 = Fp2 { c0: a, c1: b };
    let b2 = Fp2 { c0: b, c1: a };

    let mut a12 = Fp12::zero();
    pairing(&mut a12, &p_x, &p_y, &q_x, &q_y);
    let mut b12 = Fp12::zero();
    pairing(&mut b12, &p_x, &p_y, &q_x, &q_y);

    let mut out_pair = Fp12::zero();
    pairing(&mut out_pair, &p_x, &p_y, &q_x, &q_y); // warmup

    // ---- Setup: ark ----
    let mut rng = ark_std::test_rng();
    let pa = G1Projective::generator();
    let qa = G2Projective::generator();
    let pa_aff: G1Affine = pa.into();
    let qa_aff: G2Affine = qa.into();
    let qa_prep: G2Prepared<ark_bn254::Config> = qa_aff.into();
    let _ = Bn254::pairing(pa, qa); // warmup
    let aa = Fq::rand(&mut rng);
    let bb = Fq::rand(&mut rng);
    let aa2 = Fq2::rand(&mut rng);
    let bb2 = Fq2::rand(&mut rng);
    let aa12 = Fq12::rand(&mut rng);
    let bb12 = Fq12::rand(&mut rng);

    let (mut o_mul, mut o_sqr, mut o_mul2, mut o_mul12, mut o_sqr12) =
        (M::worst(), M::worst(), M::worst(), M::worst(), M::worst());
    let (mut a_mul, mut a_sqr, mut a_mul2, mut a_mul12, mut a_sqr12) =
        (M::worst(), M::worst(), M::worst(), M::worst(), M::worst());
    let (mut o_miller, mut a_miller, mut o_pair, mut a_pair) =
        (M::worst(), M::worst(), M::worst(), M::worst());

    for _ in 0..ROUNDS {
        // ---- Fp mul: serial chain both sides ----
        let mut acc = a;
        let mut c = Fp::zero();
        o_mul = o_mul.min(round(N, || {
            fp_mul(&mut c, black_box(&acc), black_box(&b));
            acc = c;
        }));
        black_box(&acc);
        let mut xa = aa;
        a_mul = a_mul.min(round(N, || {
            xa = *black_box(&xa) * *black_box(&bb);
        }));
        black_box(xa);

        // ---- Fp square ----
        let mut acc = a;
        let mut c = Fp::zero();
        o_sqr = o_sqr.min(round(N, || {
            fp_square(&mut c, black_box(&acc));
            acc = c;
        }));
        black_box(&acc);
        let mut xa = aa;
        a_sqr = a_sqr.min(round(N, || {
            xa = black_box(&xa).square();
        }));
        black_box(xa);

        // ---- Fp2 mul ----
        let mut acc = a2;
        let mut c2 = Fp2::zero();
        o_mul2 = o_mul2.min(round(N, || {
            fp2_mul(&mut c2, black_box(&acc), black_box(&b2));
            acc = c2;
        }));
        black_box(&acc);
        let mut xa = aa2;
        a_mul2 = a_mul2.min(round(N, || {
            xa = *black_box(&xa) * *black_box(&bb2);
        }));
        black_box(xa);

        // ---- Fp12 mul ----
        let mut acc = a12;
        let mut c12 = Fp12::zero();
        o_mul12 = o_mul12.min(round(N12, || {
            fp12_mul(&mut c12, black_box(&acc), black_box(&b12));
            acc = c12;
        }));
        black_box(&acc);
        let mut xa = aa12;
        a_mul12 = a_mul12.min(round(N12, || {
            xa = *black_box(&xa) * *black_box(&bb12);
        }));
        black_box(xa);

        // ---- Fp12 square ----
        let mut acc = a12;
        let mut c12 = Fp12::zero();
        o_sqr12 = o_sqr12.min(round(N12, || {
            fp12_square(&mut c12, black_box(&acc));
            acc = c12;
        }));
        black_box(&acc);
        let mut xa = aa12;
        a_sqr12 = a_sqr12.min(round(N12, || {
            xa = black_box(&xa).square();
        }));
        black_box(xa);

        // ---- Miller loop ----
        o_miller = o_miller.min(round(N_PAIR, || {
            miller_loop(black_box(&mut out_pair), black_box(&p_x), black_box(&p_y),
                        black_box(&q_x), black_box(&q_y));
        }));
        // NOTE: `qa_prep.clone()` is inside the loop because
        // `multi_miller_loop` consumes its argument.  The clone is a memcpy
        // of the precomputed G2 line coefficients and is charged to the
        // arkworks arm; it is small relative to the loop itself.
        a_miller = a_miller.min(round(N_PAIR, || {
            let _ = black_box(Bn254::multi_miller_loop(
                [black_box(pa_aff)], [qa_prep.clone()]));
        }));

        // ---- Full pairing ----
        o_pair = o_pair.min(round(N_PAIR, || {
            pairing(black_box(&mut out_pair), black_box(&p_x), black_box(&p_y),
                    black_box(&q_x), black_box(&q_y));
        }));
        a_pair = a_pair.min(round(N_PAIR, || {
            let _ = black_box(Bn254::pairing(black_box(pa), black_box(qa)));
        }));
    }

    // A 4x64 Montgomery multiply is 16 mul-class instructions plus the
    // reduction; nothing under ~10 cycles is achievable.
    for (n, m) in [("ours Fp mul", o_mul), ("ark Fq mul", a_mul),
                   ("ours Fp sqr", o_sqr), ("ark Fq sqr", a_sqr)] {
        assert_floor(n, m, 10.0);
    }
    // Fp2 is three Fp multiplies (Karatsuba); Fp12 is at least 18.
    assert_floor("ours Fp2 mul", o_mul2, 30.0);
    assert_floor("ark Fq2 mul", a_mul2, 30.0);
    assert_floor("ours Fp12 mul", o_mul12, 180.0);
    assert_floor("ark Fq12 mul", a_mul12, 180.0);
    for (n, m) in [("ours pairing", o_pair), ("ark pairing", a_pair)] {
        assert_floor(n, m, 100_000.0);
    }

    println!("{:<20} {:>13} {:>11} {:>13} {:>11} {:>9}",
             "operation", "ours (cyc)", "ours (ns)", "ark (cyc)", "ark (ns)", "ratio");
    println!("{:-<84}", "");
    let row = |name: &str, o: M, a: M| {
        println!("{:<20} {:>13.1} {:>11.1} {:>13.1} {:>11.1} {:>8.2}x",
                 name, o.cyc, o.ns, a.cyc, a.ns, o.cyc / a.cyc);
    };
    row("Fp mul", o_mul, a_mul);
    row("Fp sqr", o_sqr, a_sqr);
    row("Fp2 mul", o_mul2, a_mul2);
    row("Fp12 mul", o_mul12, a_mul12);
    row("Fp12 sqr", o_sqr12, a_sqr12);
    println!("{:-<84}", "");
    let row_big = |name: &str, o: M, a: M| {
        println!("{:<20} {:>13.0} {:>9.1} us {:>13.0} {:>9.1} us {:>8.2}x",
                 name, o.cyc, o.ns / 1000.0, a.cyc, a.ns / 1000.0, o.cyc / a.cyc);
    };
    row_big("Miller loop", o_miller, a_miller);
    row_big("Pairing (full)", o_pair, a_pair);

    println!();
    println!("ratio = ours / arkworks on CYCLES (higher = our gap).");
    println!("TSC reference rate here: {:.3} GHz (from the Fp mul row).",
             o_mul.cyc / o_mul.ns);
    println!();
    println!("Every field row is a serial latency chain with black_boxed operands,");
    println!("identically shaped on both arms.");
}
