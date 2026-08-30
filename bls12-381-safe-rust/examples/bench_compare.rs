//! Side-by-side BLS12-381 benchmark: us vs blst vs arkworks, same machine,
//! same process.
//!
//! Run pinned to one core for stability:
//!   taskset -c 2 cargo run --release --example bench_compare
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
//! All three arms run in ONE process and are INTERLEAVED round by round —
//! ours, then blst, then arkworks, then the next round — and per row the
//! round MINIMUM is reported.  A load spike therefore hits all three arms,
//! and the minimum discards the rounds it hit.  Before this file was
//! converted, each arm did one timing run in its own block, and the pairing
//! rows carried no cycle count at all.
//!
//! Every Fp-multiply timing loop is a serial latency chain — the output of
//! iteration `i` is an operand of iteration `i + 1`, with `black_box` on the
//! *operands* — so no arm can have its multiply hoisted out of its loop.
//! `black_box` on the result alone does not prevent that.  `assert_floor`
//! fails the run rather than printing a figure only an optimised-away loop
//! could produce.

use std::hint::black_box;
use std::time::Instant;

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

const ROUNDS: usize = 5;
const N_MUL: u64 = 500_000;
const N_PAIR: u64 = 30;

fn main() {
    println!("BLS12-381: this work vs blst 0.3 vs arkworks 0.5 — one process,");
    println!("{ROUNDS} interleaved rounds, per-row minimum.");
    println!();
    println!("cycles are invariant-TSC REFERENCE cycles (constant_tsc + nonstop_tsc),");
    println!("not retired core cycles.  Ratios are computed on cycles.");
    println!();
    // Leaf provenance for our arm:
    //   mul, square      CryptOpt assembly, SMT-validated against fiat-crypto
    //                    (generated/bls12_*_cryptopt.asm)
    //   add, sub, opp,   hand-written Rust CIOS in src/stubs.rs
    //   copy, select,
    //   from_word
    //   inv              hand-written Rust Bernstein-Yang divstep
    //                    (safegcd-rs), NOT extracted from Rocq; see
    //                    HAND_WRITTEN_AUDIT.md.  `--features fermat_inv`
    //                    swaps in the x^(p-2) ladder instead (~2x slower
    //                    pairing).
    //   tower, Miller    generated from the Qed'd bedrock2 programs
    //   loop, final exp  (generated/bls12_safe_tower.rs)
    println!("=== bls12-381-safe-rust (this work) ===");
    println!("    leaves: CryptOpt asm mul/square; Rust stubs add/sub/copy/select;");
    println!("    safegcd (hand-written Rust, not Rocq-extracted) Fp inversion;");
    println!("    tower + affine Miller loop + final exp from the bedrock2 extraction");
    println!();

    // ---------------- our arm's inputs ----------------
    use bls12_381::*;
    let p_x = Fp([6679831729115696150, 8653662730902241269, 1535610680227111361,
                  17342916647841752903, 17135755455211762752, 1297449291367578485]);
    let p_y = Fp([13451288730302620273, 10097742279870053774, 15949884091978425806,
                  5885175747529691540, 1016841820992199104, 845620083434234474]);
    let q_x = Fp2 {
        c0: Fp([17722385409647053328, 12967546844987299354, 11648722842835150208,
                10994581490347323113, 8027586497049998955, 396758299565931735]),
        c1: Fp([11937283898719073798, 12295044263989567683, 4301357764460312582,
                1953074377943790439, 14030662337566180679, 1266120665323335155]),
    };
    let q_y = Fp2 {
        c0: Fp([5508758831087832138, 6448303779119275098, 16710190169160573786,
                13542242618704742751, 563980702369916322, 37152010398653157]),
        c1: Fp([12520284671833321565, 1777275927576994268, 9704602344324656032,
                8739618045342622522, 16651875250601773805, 804950956836789234]),
    };
    let mut out = Fp12::zero();

    // ---------------- blst's inputs ----------------
    use blst::*;
    let mut p1 = blst_p1::default();
    let mut q1 = blst_p2::default();
    unsafe {
        blst_p1_from_affine(&mut p1, blst_p1_generator() as *const _);
        blst_p2_from_affine(&mut q1, blst_p2_generator() as *const _);
    }
    let mut p_aff = blst_p1_affine::default();
    let mut q_aff = blst_p2_affine::default();
    unsafe {
        blst_p1_to_affine(&mut p_aff, &p1);
        blst_p2_to_affine(&mut q_aff, &q1);
    }
    let bl_b = blst_fp { l: [7, 8, 9, 10, 11, 12] };
    let mut bl_out = blst_fp12::default();

    // ---------------- arkworks' inputs ----------------
    use ark_bls12_381::{Bls12_381, Fq, G1Affine, G2Affine};
    use ark_ec::pairing::Pairing;
    use ark_ec::AffineRepr;
    use ark_ff::UniformRand;
    use ark_std::rand::SeedableRng;

    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(0xdead);
    let ark_a: Fq = Fq::rand(&mut rng);
    let ark_b: Fq = Fq::rand(&mut rng);
    let ark_p = G1Affine::generator();
    let ark_q = G2Affine::generator();

    // ---------------- warm-up, all three arms ----------------
    {
        pairing(&mut out, &p_x, &p_y, &q_x, &q_y);
        unsafe {
            blst_miller_loop(&mut bl_out, &q_aff, &p_aff);
            blst_final_exp(&mut bl_out, &bl_out);
        }
        let _ = black_box(Bls12_381::pairing(ark_p, ark_q));

        let mut x = p_x;
        let mut c = Fp::zero();
        let mut ba = blst_fp { l: [1, 2, 3, 4, 5, 6] };
        let mut bc = blst_fp::default();
        let mut aa = ark_a;
        for _ in 0..N_MUL / 10 {
            fp_mul(&mut c, black_box(&x), black_box(&p_y));
            x = c;
            unsafe { blst_fp_mul(&mut bc, black_box(&ba), black_box(&bl_b)) };
            ba = bc;
            aa = *black_box(&aa) * *black_box(&ark_b);
        }
        black_box(&x);
        black_box(&ba);
        black_box(aa);
    }

    let (mut o_mul, mut b_mul, mut a_mul) = (M::worst(), M::worst(), M::worst());
    let (mut o_pair, mut b_pair, mut a_pair) = (M::worst(), M::worst(), M::worst());
    let mut o_miller = M::worst();
    let mut b_miller = M::worst();

    for _ in 0..ROUNDS {
        // ---- Fp multiply: serial latency chain, operands black_boxed ----
        let mut x = p_x;
        let mut c = Fp::zero();
        o_mul = o_mul.min(round(N_MUL, || {
            fp_mul(&mut c, black_box(&x), black_box(&p_y));
            x = c;
        }));
        black_box(&x);

        let mut ba = blst_fp { l: [1, 2, 3, 4, 5, 6] };
        let mut bc = blst_fp::default();
        b_mul = b_mul.min(round(N_MUL, || {
            unsafe { blst_fp_mul(&mut bc, black_box(&ba), black_box(&bl_b)) };
            ba = bc;
        }));
        black_box(&ba);

        let mut aa = ark_a;
        a_mul = a_mul.min(round(N_MUL, || {
            aa = *black_box(&aa) * *black_box(&ark_b);
        }));
        black_box(aa);

        // ---- Miller loop ----
        o_miller = o_miller.min(round(N_PAIR, || {
            miller_loop(black_box(&mut out), black_box(&p_x), black_box(&p_y),
                        black_box(&q_x), black_box(&q_y));
        }));
        b_miller = b_miller.min(round(N_PAIR, || {
            unsafe { blst_miller_loop(black_box(&mut bl_out), black_box(&q_aff),
                                      black_box(&p_aff)) };
        }));

        // ---- full pairing ----
        o_pair = o_pair.min(round(N_PAIR, || {
            pairing(black_box(&mut out), black_box(&p_x), black_box(&p_y),
                    black_box(&q_x), black_box(&q_y));
        }));
        b_pair = b_pair.min(round(N_PAIR, || {
            unsafe {
                blst_miller_loop(black_box(&mut bl_out), black_box(&q_aff),
                                 black_box(&p_aff));
                blst_final_exp(black_box(&mut bl_out), black_box(&bl_out));
            }
        }));
        a_pair = a_pair.min(round(N_PAIR, || {
            let _ = black_box(Bls12_381::pairing(black_box(ark_p), black_box(ark_q)));
        }));
    }

    // A 6x64 Montgomery multiply is 36 mul-class instructions plus the
    // reduction; nothing under ~15 cycles is achievable.
    assert_floor("ours Fp mul", o_mul, 15.0);
    assert_floor("blst Fp mul", b_mul, 15.0);
    assert_floor("arkworks Fq mul", a_mul, 15.0);
    // A BLS12-381 pairing runs thousands of field multiplies.
    for (n, m) in [("ours pairing", o_pair), ("blst pairing", b_pair),
                   ("arkworks pairing", a_pair)] {
        assert_floor(n, m, 200_000.0);
    }

    println!("=== per-arm figures ===");
    println!("{:<18} {:>13} {:>12} {:>13} {:>12} {:>13} {:>12}",
             "operation", "ours (cyc)", "ours (ns)", "blst (cyc)", "blst (ns)",
             "ark (cyc)", "ark (ns)");
    println!("{}", "-".repeat(100));
    println!("{:<18} {:>13.1} {:>12.1} {:>13.1} {:>12.1} {:>13.1} {:>12.1}",
             "Fp mul", o_mul.cyc, o_mul.ns, b_mul.cyc, b_mul.ns, a_mul.cyc, a_mul.ns);
    println!("{:<18} {:>13.0} {:>12.0} {:>13.0} {:>12.0} {:>13} {:>12}",
             "Miller loop", o_miller.cyc, o_miller.ns, b_miller.cyc, b_miller.ns,
             "-", "-");
    println!("{:<18} {:>13.0} {:>12.0} {:>13.0} {:>12.0} {:>13.0} {:>12.0}",
             "Pairing (full)", o_pair.cyc, o_pair.ns, b_pair.cyc, b_pair.ns,
             a_pair.cyc, a_pair.ns);

    println!();
    println!("=== ratios on cycles (ours / theirs; below 1.00 means we are faster) ===");
    println!("{:<18} {:>14} {:>14}", "operation", "vs blst", "vs arkworks");
    println!("{}", "-".repeat(48));
    println!("{:<18} {:>13.2}x {:>13.2}x", "Fp mul",
             o_mul.cyc / b_mul.cyc, o_mul.cyc / a_mul.cyc);
    println!("{:<18} {:>13.2}x {:>14}", "Miller loop",
             o_miller.cyc / b_miller.cyc, "-");
    println!("{:<18} {:>13.2}x {:>13.2}x", "Pairing (full)",
             o_pair.cyc / b_pair.cyc, o_pair.cyc / a_pair.cyc);

    println!();
    println!("Pairing in ms: ours {:.2}, blst {:.2}, arkworks {:.2}",
             o_pair.ns / 1e6, b_pair.ns / 1e6, a_pair.ns / 1e6);
    println!("TSC reference rate here: {:.3} GHz (from the Fp mul row).",
             o_mul.cyc / o_mul.ns);
    println!();
    println!("arkworks exposes no separate Miller-loop entry point in the shape the");
    println!("other two arms use here, so that cell is left empty rather than filled");
    println!("with a differently-shaped measurement.");
}
