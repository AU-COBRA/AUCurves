//! BN254 **instruction-count** benchmarks under callgrind (iai-callgrind).
//!
//! ## READ THIS BEFORE QUOTING A NUMBER
//!
//! **An instruction count is not a speed.**  Callgrind counts the
//! instructions a run retires; it says nothing about how many cycles those
//! instructions take.  It ignores cache behaviour, memory-level parallelism,
//! branch prediction and IPC entirely.  Two routines with identical
//! instruction counts can differ by 2x in cycles, and a routine that issues
//! *more* instructions can be *faster* if they schedule better.  This matters
//! most in the tower: an Fp12 multiply touches 12 x 32 bytes of operand and
//! is far more memory-bound than an Fp multiply, so its instruction ratio and
//! its cycle ratio need not agree — and on this workload they do not.
//!
//! What this harness is for: **load-immune regression detection.**  The
//! instruction count is deterministic — identical run to run, on an idle
//! machine or a loaded one.  The `_rdtsc` cycle harnesses in `examples/`
//! (`bench_breakdown`, `bench_vs_production`) are the performance
//! measurement; this file is the tripwire that tells you whether a diff
//! changed the work being done.  The two harnesses cover the same operations
//! on purpose, so a divergence between the instruction ratio and the cycle
//! ratio is itself a finding.
//!
//! ## MEASUREMENT DISCIPLINE
//!
//! Same rule as the cycle harnesses: `black_box` goes on the **operands**,
//! not (only) on the result.  A loop-invariant computation with only its
//! result black-boxed gets hoisted out of the loop by LLVM and you measure
//! an empty loop; that bug produced a published 16.5x ratio in this
//! workspace that was pure artifact.  The field loops below are serial
//! dependency chains — iteration `i + 1` consumes the result of iteration
//! `i` — with the operands inside `black_box`, and they end in an assertion
//! that the accumulator actually moved.  The Miller-loop and pairing arms
//! take `black_box(&mut out)` plus `black_box`ed inputs, which is what stops
//! LLVM from collapsing the repeated identical call.
//!
//! Operand construction is hoisted **out of the measured region** with
//! `#[bench::…(setup_fn())]`: iai-callgrind evaluates the attribute
//! expression before it starts collecting and passes the (already
//! black-boxed) value in.  This is not cosmetic here.  Built inside the
//! benchmark body, the two Fp12 operands cost two full pairings — about
//! 32M instructions against 16M for the 500 multiplies actually under test,
//! i.e. the reported figure would have been 3x the truth.
//!
//! Each benchmark runs `N` iterations and reports the **total** for the
//! loop; divide by `N` for the per-operation figure.  `loop_baseline_10k`
//! measures the bare loop-plus-`black_box` scaffolding at `N_FP`.
//!
//! ## COMPARABILITY (same caveats as `examples/bench_breakdown.rs`)
//!
//! Our `fp_mul` is an out-parameter API, `fp_mul(&mut out, &a, &b)`, and
//! writes through memory by construction; arkworks' `a * b` returns by value
//! and can stay in registers.  Passing the arkworks operands through
//! `black_box` **by value** moves them across the barrier and spills them,
//! adding a store-forward per iteration that our arm pays anyway.  The
//! arkworks arms here take the barrier **by reference**
//! (`*black_box(&x) * *black_box(&y)`), matching `bench_breakdown.rs`, which
//! is the discipline behind the 1.46x figure quoted in `benchmark.md`.
//!
//! `multi_miller_loop` consumes its `G2Prepared`, so the `clone()` is inside
//! the loop and charged to the arkworks arm; it is a memcpy of precomputed
//! line coefficients and small relative to the loop itself.  Note also that
//! arkworks' Miller loop runs against a *prepared* G2 point, so its line
//! coefficients are precomputed in the setup, outside the measured region,
//! while ours are computed inside it — the two Miller-loop arms are not
//! doing identical work, in instructions or in cycles.  The full-pairing row
//! is the like-for-like comparison.
//!
//! Our Fp12 operands are GT elements (outputs of the pairing); arkworks'
//! are `Fq12::rand`, uniform in the whole tower.  A Montgomery multiply is
//! data-independent in both, so this does not bias the count.
//!
//! Run:  `cargo bench -p bn254-safe-rust --bench iai_bn254`
//! Needs `valgrind` and `cargo install iai-callgrind-runner --version 0.16.1`.

use iai_callgrind::{library_benchmark, library_benchmark_group, main};
use std::hint::black_box;

use bn254::{fp12_mul, fp2_mul, fp_mul, miller_loop, pairing, Fp, Fp12, Fp2};

use ark_bn254::{Bn254, Fq, Fq12, Fq2, G1Affine, G1Projective, G2Affine, G2Projective};
use ark_ec::{bn::G2Prepared, pairing::Pairing, PrimeGroup};
use ark_ff::UniformRand;

/// Iterations per benchmark.  Chosen so the loop body dominates the
/// function prologue, while keeping the simulated instruction total inside
/// callgrind's comfortable range (~1e5..1e8).
const N_FP: u64 = 10_000;
const N_FP2: u64 = 5_000;
const N_FP12: u64 = 500;
const N_PAIR: u64 = 5;

// The G1/G2 point and the two Fp seeds are copied verbatim from
// `examples/bench_breakdown.rs` so the two harnesses measure the same work.
const P_X: Fp = Fp([0xd35d438dc58f0d9d, 0x0a78eb28f5c70b3d, 0x666ea36f7879462c, 0x0e0a77c19a07df2f]);
const P_Y: Fp = Fp([0xa6ba871b8b1e1b3a, 0x14f1d651eb8e167b, 0xccdd46def0f28c58, 0x1c14ef83340fbe5e]);
const Q_X: Fp2 = Fp2 {
    c0: Fp([0x8e83b5d102bc2026, 0xdceb1935497b0172, 0xfbb8264797811adf, 0x19573841af96503b]),
    c1: Fp([0xafb4737da84c6140, 0x6043dd5a5802d8c4, 0x09e950fc52a02f86, 0x14fef0833aea7b6b]),
};
const Q_Y: Fp2 = Fp2 {
    c0: Fp([0x619dfa9d886be9f6, 0xfe7fd297f59e9b78, 0xff9e1a62231b7dfe, 0x28fd7eebae9e4206]),
    c1: Fp([0x64095b56c71856ee, 0xdc57f922327d3cbb, 0x55f935be33351076, 0x0da4a0e693fd6482]),
};
const A: Fp = Fp([0x7a17caa950ad28d7, 0x1f6ac17ae15521b9, 0x334bea4e696bd284, 0x2a1f6744ce179d8e]);
const B: Fp = Fp([0xe4b1c5ae034e46ca, 0x9cdb2d3b64716da7, 0x47d8eb76d8dd067e, 0x15d0085520f5bbc3]);

const A2: Fp2 = Fp2 { c0: A, c1: B };
const B2: Fp2 = Fp2 { c0: B, c1: A };

// ─────────────────────────── setup (not measured) ────────────────────────

fn setup_fp() -> (Fp, Fp) {
    (A, B)
}

fn setup_fp2() -> (Fp2, Fp2) {
    (A2, B2)
}

/// Two GT elements: the pairing of the fixed G1/G2 point above, and its
/// square.  Genuine tower elements rather than structured values a multiply
/// could shortcut on.  Two full pairings — hence run in the setup.
fn setup_fp12() -> (Fp12, Fp12) {
    let mut a = Fp12::zero();
    pairing(&mut a, &P_X, &P_Y, &Q_X, &Q_Y);
    let mut b = Fp12::zero();
    fp12_mul(&mut b, &a, &a);
    (a, b)
}

fn setup_ark_fp() -> (Fq, Fq) {
    let mut rng = ark_std::test_rng();
    (Fq::rand(&mut rng), Fq::rand(&mut rng))
}

fn setup_ark_fp2() -> (Fq2, Fq2) {
    let mut rng = ark_std::test_rng();
    (Fq2::rand(&mut rng), Fq2::rand(&mut rng))
}

fn setup_ark_fp12() -> (Fq12, Fq12) {
    let mut rng = ark_std::test_rng();
    (Fq12::rand(&mut rng), Fq12::rand(&mut rng))
}

/// The G2 line coefficients arkworks precomputes.  Charged to the setup,
/// exactly as `bench_breakdown.rs` charges them outside its timing loop.
fn setup_ark_miller() -> (G1Affine, G2Prepared<ark_bn254::Config>) {
    let pa_aff: G1Affine = G1Projective::generator().into();
    let qa_aff: G2Affine = G2Projective::generator().into();
    (pa_aff, qa_aff.into())
}

fn setup_ark_pairing() -> (G1Projective, G2Projective) {
    (G1Projective::generator(), G2Projective::generator())
}

// ───────────────────────── loop scaffolding baseline ─────────────────────

// The bare loop plus `black_box` scaffolding at `N_FP` iterations, with no
// field work in it.  Reported rather than subtracted silently: both arms
// pay it, so it hardly moves any ratio.
// (Doc comments are rejected by `#[library_benchmark]`, hence `//`.)
#[library_benchmark]
fn loop_baseline_10k() -> u64 {
    let mut acc = 1u64;
    for _ in 0..N_FP {
        acc = black_box(acc).wrapping_add(black_box(3));
    }
    acc
}

// ───────────────────────────── Fp multiply ───────────────────────────────

#[library_benchmark]
#[bench::chain(setup_fp())]
fn ours_fp_mul(ab: (Fp, Fp)) -> Fp {
    let (a0, b) = ab;
    let mut acc = a0;
    let mut out = Fp::zero();
    for _ in 0..N_FP {
        fp_mul(&mut out, black_box(&acc), black_box(&b));
        acc = out;
    }
    assert_ne!(acc.0, a0.0, "fp_mul chain did not advance — loop optimised away");
    acc
}

#[library_benchmark]
#[bench::chain(setup_ark_fp())]
fn arkworks_fp_mul(ab: (Fq, Fq)) -> Fq {
    let (a0, b) = ab;
    let mut acc = a0;
    for _ in 0..N_FP {
        acc = *black_box(&acc) * *black_box(&b);
    }
    assert_ne!(acc, a0, "Fq mul chain did not advance — loop optimised away");
    acc
}

// ───────────────────────────── Fp2 multiply ──────────────────────────────

#[library_benchmark]
#[bench::chain(setup_fp2())]
fn ours_fp2_mul(ab: (Fp2, Fp2)) -> Fp2 {
    let (a0, b) = ab;
    let mut acc = a0;
    let mut out = Fp2::zero();
    for _ in 0..N_FP2 {
        fp2_mul(&mut out, black_box(&acc), black_box(&b));
        acc = out;
    }
    assert_ne!(acc.c0 .0, a0.c0 .0, "fp2_mul chain did not advance — loop optimised away");
    acc
}

#[library_benchmark]
#[bench::chain(setup_ark_fp2())]
fn arkworks_fp2_mul(ab: (Fq2, Fq2)) -> Fq2 {
    let (a0, b) = ab;
    let mut acc = a0;
    for _ in 0..N_FP2 {
        acc = *black_box(&acc) * *black_box(&b);
    }
    assert_ne!(acc, a0, "Fq2 mul chain did not advance — loop optimised away");
    acc
}

// ──────────────────────────── Fp12 multiply ──────────────────────────────

#[library_benchmark]
#[bench::chain(setup_fp12())]
fn ours_fp12_mul(ab: (Fp12, Fp12)) -> Fp12 {
    let (a0, b) = ab;
    let mut acc = a0;
    let mut out = Fp12::zero();
    for _ in 0..N_FP12 {
        fp12_mul(&mut out, black_box(&acc), black_box(&b));
        acc = out;
    }
    assert_ne!(acc.c0.c0.c0 .0, a0.c0.c0.c0 .0,
               "fp12_mul chain did not advance — loop optimised away");
    acc
}

#[library_benchmark]
#[bench::chain(setup_ark_fp12())]
fn arkworks_fp12_mul(ab: (Fq12, Fq12)) -> Fq12 {
    let (a0, b) = ab;
    let mut acc = a0;
    for _ in 0..N_FP12 {
        acc = *black_box(&acc) * *black_box(&b);
    }
    assert_ne!(acc, a0, "Fq12 mul chain did not advance — loop optimised away");
    acc
}

// ──────────────────────────── Miller loop ────────────────────────────────

#[library_benchmark]
fn ours_miller_loop() -> Fp12 {
    let mut out = Fp12::zero();
    for _ in 0..N_PAIR {
        miller_loop(black_box(&mut out), black_box(&P_X), black_box(&P_Y),
                    black_box(&Q_X), black_box(&Q_Y));
    }
    assert_ne!(out.c0.c0.c0 .0, [0u64; 4], "miller_loop produced zero — loop optimised away");
    out
}

#[library_benchmark]
#[bench::prepared(setup_ark_miller())]
fn arkworks_miller_loop(pq: (G1Affine, G2Prepared<ark_bn254::Config>)) {
    let (pa_aff, qa_prep) = pq;
    for _ in 0..N_PAIR {
        let _ = black_box(Bn254::multi_miller_loop(
            [black_box(pa_aff)],
            [qa_prep.clone()],
        ));
    }
}

// ───────────────────────────── full pairing ──────────────────────────────

#[library_benchmark]
fn ours_pairing() -> Fp12 {
    let mut out = Fp12::zero();
    for _ in 0..N_PAIR {
        pairing(black_box(&mut out), black_box(&P_X), black_box(&P_Y),
                black_box(&Q_X), black_box(&Q_Y));
    }
    assert_ne!(out.c0.c0.c0 .0, [0u64; 4], "pairing produced zero — loop optimised away");
    out
}

#[library_benchmark]
#[bench::generators(setup_ark_pairing())]
fn arkworks_pairing(pq: (G1Projective, G2Projective)) {
    let (pa, qa) = pq;
    for _ in 0..N_PAIR {
        let _ = black_box(Bn254::pairing(black_box(pa), black_box(qa)));
    }
}

library_benchmark_group!(
    name = bn254_iai;
    benchmarks =
        loop_baseline_10k,
        ours_fp_mul,
        arkworks_fp_mul,
        ours_fp2_mul,
        arkworks_fp2_mul,
        ours_fp12_mul,
        arkworks_fp12_mul,
        ours_miller_loop,
        arkworks_miller_loop,
        ours_pairing,
        arkworks_pairing
);

main!(library_benchmark_groups = bn254_iai);
