//! BW6-761 G1 **instruction-count** benchmarks under callgrind
//! (iai-callgrind).
//!
//! ## READ THIS BEFORE QUOTING A NUMBER
//!
//! **An instruction count is not a speed.**  Callgrind counts the
//! instructions a run retires; it says nothing about how many cycles those
//! instructions take.  It ignores cache behaviour, memory-level parallelism,
//! branch prediction and IPC entirely.  Two routines with identical
//! instruction counts can differ by 2x in cycles, and a routine that issues
//! *more* instructions can be *faster* if they schedule better.  A 761-bit
//! field is 12 saturated u64 limbs; at that width a multiply spills, so the
//! gap between instruction count and cycles is wider here than on a 4-limb
//! curve.
//!
//! What this harness is for: **load-immune regression detection.**  The
//! instruction count is deterministic — identical run to run, on an idle
//! machine or a loaded one.  The `_rdtsc` cycle harnesses in `examples/`
//! (`bench_g1`, `bench_double_a0`) are the performance measurement; this
//! file is the tripwire that tells you whether a diff changed the work being
//! done.  The two harnesses cover the same operations on purpose, so a
//! divergence between the instruction ratio and the cycle ratio is itself a
//! finding.
//!
//! There is **no comparison arm** on this curve.  `ark-bw6-761` implements
//! the field with a variable-time binary-extended-Euclid inverse (see the
//! "Libraries excluded as variable-time" section of `benchmark.md`), so it
//! is not a like-for-like reference for a constant-time inverse, and it is
//! not a dev-dependency of this crate.  The rows below are absolute
//! instruction counts for regression tracking, not ratios.
//!
//! ## MEASUREMENT DISCIPLINE
//!
//! `black_box` goes on the **operands**, not (only) on the result.  A
//! loop-invariant computation with only its result black-boxed gets hoisted
//! out of the loop by LLVM and you measure an empty loop; that bug produced
//! a published 16.5x ratio in this workspace that was pure artifact.  The
//! field loops are serial dependency chains — iteration `i + 1` consumes the
//! result of iteration `i` — and end in an assertion that the accumulator
//! actually moved.  The point-operation loops recompute from a black-boxed
//! operand each iteration, matching `examples/bench_g1.rs`, so the two
//! harnesses measure the same work.
//!
//! Operand construction is hoisted **out of the measured region** with
//! `#[bench::…(setup_fn())]`: iai-callgrind evaluates the attribute
//! expression before it starts collecting and passes the (already
//! black-boxed) value in.
//!
//! Each benchmark runs `N` iterations and reports the **total** for the
//! loop; divide by `N` for the per-operation figure.  `loop_baseline_10k`
//! measures the bare loop-plus-`black_box` scaffolding at `N_FP`.
//!
//! ## WHAT THE ROWS ARE
//!
//! * `g1_proj_double` — RCB 2015 **Algorithm 9**, the complete doubling for
//!   `a = 0`, emitted from the Rocq derivation in
//!   `src/Bedrock/Curve/CurveDoubleA0RustCmd.v`.  This is the shipped body.
//!   It packs its input into a 288-byte buffer and unpacks the result,
//!   because the emitted body has a byte ABI; that serialisation is inside
//!   the measurement, here and in the cycle harness alike.
//! * `g1_proj_add` — RCB 2015 **Algorithm 7**, the complete addition, over
//!   the same projective coordinates.
//! * `g1_scalar_mul` — the projective ladder, one inversion at the end
//!   rather than one per bit.
//! * `fp_mul` / `fp_inv` — the tower's field leaves.  `fp_inv` is the
//!   Bernstein-Yang (safegcd) divstep port, constant time.
//!
//! Run:  `cargo bench -p bw6-761-safe-rust --bench iai_bw6_761`
//! Needs `valgrind` and `cargo install iai-callgrind-runner --version 0.16.1`.

use iai_callgrind::{library_benchmark, library_benchmark_group, main};
use std::hint::black_box;

use bw6_761::g1_double_a0_extracted::g1_proj_double_extracted;
use bw6_761::group::{
    g1_proj_add, g1_scalar_mul, g1_three_b, g1_to_proj, G1Aff, G1Proj,
};
use bw6_761::tower::{self, bw6_761_inv, bw6_761_mul, Fp};

/// Iterations per benchmark.  Chosen so the loop body dominates the
/// function prologue, while keeping the simulated instruction total inside
/// callgrind's comfortable range (~1e5..1e8).
const N_FP: u64 = 10_000;
/// Odd on purpose.  The inverse chain `acc <- acc^-1` is a genuine serial
/// dependency — LLVM does not know the semantics of `bw6_761_inv` and cannot
/// fold `inv(inv(x))` back to `x` — but it is an involution, so after an even
/// number of iterations the accumulator is back at its starting value and the
/// "did the loop run" assertion below would fire on a perfectly good run.
const N_INV: u64 = 201;
const N_PROJ: u64 = 500;
const N_SMUL: u64 = 3;

// BW6-761 G1 generator, affine, Montgomery-form Fp limbs little-endian u64.
// Cross-checked against gnark-crypto v0.20.1; the same constants are used by
// `src/kat.rs` (which is `#[cfg(test)]`, hence the copy) and by
// `examples/bench_g1.rs`.
const G1_GEN_X: [u64; 12] = [
    0xd6e42d7614c2d770, 0x4bb886eddbc3fc21, 0x64648b044098b4d2, 0x1a585c895a422985,
    0xf1a9ac17cf8685c9, 0x352785830727aea5, 0xddf8cb12306266fe, 0x6913b4bfbc9e949a,
    0x3a4b78d67ba5f6ab, 0x0f481c06a8d02a04, 0x91d4e7365c43edac, 0x00f4d17cd48beca5,
];
const G1_GEN_Y: [u64; 12] = [
    0x97e805c4bd16411f, 0x870d844e1ee6dd08, 0x1eba7a37cb9eab4d, 0xd544c4df10b9889a,
    0x8fe37f21a33897be, 0xe9bf99a43a0885d2, 0xd7ee0c9e273de139, 0xaa6a9ec7a38dd791,
    0x8f95d3fcf765da8e, 0x42326e7db7357c99, 0xe217e407e218695f, 0x009d1eb23b7cf684,
];

// ─────────────────────────── setup (not measured) ────────────────────────

fn generator() -> G1Aff {
    G1Aff::pt(tower::Fp(G1_GEN_X), tower::Fp(G1_GEN_Y))
}

/// The generator's x-coordinate, used as the field operand.  It is a full
/// 761-bit Montgomery element, so the multiply and the divstep inverse both
/// run their worst case rather than a short-circuit on a small value.
fn setup_fp() -> Fp {
    tower::Fp(G1_GEN_X)
}

/// `(P, 2P, 3b)` in projective coordinates.  `g1_proj_add` needs two
/// *distinct* points to exercise the addition path rather than the
/// self-addition path, so `2P` is built here.
fn setup_proj() -> (G1Proj, G1Proj, Fp) {
    let g = generator();
    let gp = g1_to_proj(&g);
    let gp2 = g1_proj_double_extracted(&gp);
    (gp, gp2, g1_three_b())
}

/// The generator plus the scalar `examples/bench_g1.rs` multiplies by, so
/// the two harnesses run the same 48-byte scalar.
fn setup_scalar_mul() -> (G1Aff, [u8; 48]) {
    let mut k = [0u8; 48];
    for (i, byte) in k.iter_mut().enumerate() {
        *byte = (0x9du8).wrapping_mul(i as u8 + 1) | 1;
    }
    k[0] &= 0x1f;
    (generator(), k)
}

// ───────────────────────── loop scaffolding baseline ─────────────────────

// The bare loop plus `black_box` scaffolding at `N_FP` iterations, with no
// field work in it.  Subtract it from `fp_mul` for the multiply on its own.
// (Doc comments are rejected by `#[library_benchmark]`, hence `//`.)
#[library_benchmark]
fn loop_baseline_10k() -> u64 {
    let mut acc = 1u64;
    for _ in 0..N_FP {
        acc = black_box(acc).wrapping_add(black_box(3));
    }
    acc
}

// ───────────────────────────── field leaves ──────────────────────────────

#[library_benchmark]
#[bench::chain(setup_fp())]
fn fp_mul(x: Fp) -> Fp {
    let mut acc = x;
    let mut out = Fp::zero();
    for _ in 0..N_FP {
        bw6_761_mul(&mut out, black_box(&acc), black_box(&x));
        acc = out;
    }
    assert_ne!(acc.0, x.0, "fp_mul chain did not advance — loop optimised away");
    acc
}

#[library_benchmark]
#[bench::chain(setup_fp())]
fn fp_inv(x: Fp) -> Fp {
    let mut acc = x;
    let mut out = Fp::zero();
    for _ in 0..N_INV {
        bw6_761_inv(&mut out, black_box(&acc));
        acc = out;
    }
    assert_ne!(acc.0, x.0, "fp_inv chain did not advance — loop optimised away");
    acc
}

// ───────────────────────── projective point ops ──────────────────────────

#[library_benchmark]
#[bench::generator(setup_proj())]
fn g1_proj_double(pts: (G1Proj, G1Proj, Fp)) -> G1Proj {
    let (gp, _, _) = pts;
    let mut r = gp;
    for _ in 0..N_PROJ {
        r = g1_proj_double_extracted(black_box(&gp));
    }
    assert_ne!(r.x.0, gp.x.0, "g1_proj_double did not move the point");
    r
}

#[library_benchmark]
#[bench::generator(setup_proj())]
fn g1_proj_add_bench(pts: (G1Proj, G1Proj, Fp)) -> G1Proj {
    let (gp, gp2, b3) = pts;
    let mut r = gp;
    for _ in 0..N_PROJ {
        r = g1_proj_add(black_box(&gp), black_box(&gp2), black_box(&b3));
    }
    assert_ne!(r.x.0, gp.x.0, "g1_proj_add did not move the point");
    r
}

// ─────────────────────── projective scalar multiply ──────────────────────

#[library_benchmark]
#[bench::generator(setup_scalar_mul())]
fn g1_scalar_mul_bench(pk: (G1Aff, [u8; 48])) -> G1Aff {
    let (g, k) = pk;
    let mut r = g;
    for _ in 0..N_SMUL {
        r = g1_scalar_mul(black_box(&k), black_box(&g));
    }
    assert_ne!(r, G1Aff::Inf, "scalar mul returned the point at infinity");
    r
}

library_benchmark_group!(
    name = bw6_761_iai;
    benchmarks =
        loop_baseline_10k,
        fp_mul,
        fp_inv,
        g1_proj_double,
        g1_proj_add_bench,
        g1_scalar_mul_bench
);

main!(library_benchmark_groups = bw6_761_iai);
