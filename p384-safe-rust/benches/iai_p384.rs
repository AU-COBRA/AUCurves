//! P-384 **instruction-count** benchmarks under callgrind (iai-callgrind).
//!
//! ## READ THIS BEFORE QUOTING A NUMBER
//!
//! **An instruction count is not a speed.**  Callgrind counts the
//! instructions a run retires; it says nothing about how many cycles those
//! instructions take.  It ignores cache behaviour, memory-level parallelism,
//! branch prediction and IPC entirely.  Two routines with identical
//! instruction counts can differ by 2x in cycles, and a routine that issues
//! *more* instructions can be *faster* if they schedule better.
//!
//! What this harness is for: **load-immune regression detection.**  The
//! instruction count is deterministic — identical run to run, on an idle
//! machine or a loaded one.  The `_rdtsc` cycle harness in
//! `examples/bench_compare.rs` is the performance measurement; this file is
//! the tripwire that tells you whether a diff changed the work being done.
//! The two harnesses cover the same operations on purpose, so a divergence
//! between the instruction ratio and the cycle ratio is itself a finding: it
//! means the operation's cost is dominated by memory behaviour or IPC rather
//! than by instruction count.
//!
//! ## MEASUREMENT DISCIPLINE
//!
//! Same rule as the cycle harnesses: `black_box` goes on the **operands**,
//! not (only) on the result.  A loop-invariant computation with only its
//! result black-boxed gets hoisted out of the loop by LLVM and you measure
//! an empty loop; that bug produced a published 16.5x ratio in this
//! workspace that was pure artifact.  Every loop below is a serial
//! dependency chain — iteration `i + 1` consumes the result of iteration
//! `i` — with the operands inside `black_box`, and the chained benchmarks
//! end in an assertion that the accumulator actually moved.
//!
//! Operand construction is hoisted **out of the measured region** with
//! `#[bench::…(setup_fn())]`: iai-callgrind evaluates the attribute
//! expression before it starts collecting and passes the (already
//! black-boxed) value in.  Montgomery conversion, `from_repr` and the
//! generator doubling are therefore not charged to any row.
//!
//! Each benchmark runs `N` iterations and reports the **total** for the
//! loop; divide by `N` for the per-operation figure.  `loop_baseline_10k`
//! measures the bare loop-plus-`black_box` scaffolding at `N_FP`, so the
//! scaffolding overhead is visible and subtractable rather than folded
//! silently into the field numbers.
//!
//! ## COMPARABILITY (same caveats as `examples/bench_compare.rs`)
//!
//! * `g1_add` / `g1_double`: both arms use the `a = -3` RCB 2015
//!   specialisation (Algorithm 4 / Algorithm 6).
//! * `g1_scalar_mul`: both arms are variable-base, constant-time, 4-bit
//!   fixed window with a per-call table read by a full linear scan.
//! * `fp_mul`: ours is CryptOpt-superoptimized assembly when the build host
//!   has BMI2/ADX — the choice is a *build-time* `cfg`, set by `build.rs`,
//!   so the binary callgrind runs is the same binary the cycle harness
//!   times; valgrind's CPUID emulation cannot change the dispatch.  Set
//!   `P384_NO_CRYPTOPT=1` to force the fiat-crypto leaf.  RustCrypto's P-384
//!   field is plain fiat-crypto in 0.13.1.
//!
//! Run:  `cargo bench -p p384-safe-rust --bench iai_p384`
//! Needs `valgrind` and `cargo install iai-callgrind-runner --version 0.16.1`.

use iai_callgrind::{library_benchmark, library_benchmark_group, main};
use std::hint::black_box;

use p384::group::{g1_add, g1_double, g1_generator, g1_scalar_mul, G1};
use p384::{fp_mul, fp_to_montgomery, Fp, FpRaw};

use p384_rc::elliptic_curve::group::Group;
use p384_rc::elliptic_curve::ops::Reduce;
use p384_rc::elliptic_curve::PrimeField;
use p384_rc::{FieldBytes, FieldElement as RcFe, ProjectivePoint, Scalar, U384};

/// Iterations per benchmark.  Chosen so the loop body dominates the
/// function prologue and the operand setup, while keeping the simulated
/// instruction total inside callgrind's comfortable range (~1e5..1e7).
const N_FP: u64 = 10_000;
const N_GROUP: u64 = 2_000;
const N_MUL: u64 = 5;

/// The scalar both arms multiply by, as our 6x64 limbs.  Copied from
/// `examples/bench_compare.rs` so the two harnesses measure the same work.
const K_LIMBS: [u64; 6] = [
    0x0123_4567_89ab_cdef,
    0xfedc_ba98_7654_3210,
    0x0f1e_2d3c_4b5a_6978,
    0x1122_3344_5566_7788,
    0x99aa_bbcc_ddee_ff00,
    0x0a1b_2c3d_4e5f_6071,
];

/// `K_LIMBS` as 48 big-endian bytes, the form RustCrypto's `Scalar` takes.
fn scalar_be() -> [u8; 48] {
    let mut out = [0u8; 48];
    for (i, limb) in K_LIMBS.iter().enumerate() {
        let off = 40 - 8 * i;
        out[off..off + 8].copy_from_slice(&limb.to_be_bytes());
    }
    out
}

const SEED_A: [u64; 6] = [
    0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210, 0x1357_9bdf_0246_8ace,
    0x0f1e_2d3c_4b5a_6978, 0x1122_3344_5566_7788, 0x0055_6666_7777_8888,
];
const SEED_B: [u64; 6] = [
    0xdead_beef_cafe_babe, 0x0011_2233_4455_6677, 0x8899_aabb_ccdd_eeff,
    0x1029_3847_5647_3829, 0x7fff_ffff_ffff_fffd, 0x0033_1122_9988_7766,
];

fn ours_from(w: [u64; 6]) -> Fp {
    let mut o = Fp([0u64; 6]);
    fp_to_montgomery(&mut o, &FpRaw(w));
    o
}

fn theirs_from(w: [u64; 6]) -> RcFe {
    let mut be = [0u8; 48];
    for i in 0..6 {
        be[40 - 8 * i..48 - 8 * i].copy_from_slice(&w[i].to_be_bytes());
    }
    RcFe::from_repr(be.into()).unwrap()
}

// ─────────────────────────── setup (not measured) ────────────────────────

fn setup_fp_ours() -> (Fp, Fp) {
    (ours_from(SEED_A), ours_from(SEED_B))
}

fn setup_fp_theirs() -> (RcFe, RcFe) {
    (theirs_from(SEED_A), theirs_from(SEED_B))
}

/// `(G, 2G)`: the addend and the starting accumulator.
fn setup_g1_ours() -> (G1, G1) {
    let g = g1_generator();
    (g, g1_double(&g))
}

fn setup_g1_theirs() -> (ProjectivePoint, ProjectivePoint) {
    let rg = ProjectivePoint::GENERATOR;
    (rg, rg.double())
}

fn setup_smul_ours() -> G1 {
    g1_double(&g1_generator())
}

fn setup_smul_theirs() -> (Scalar, ProjectivePoint) {
    let k_be = scalar_be();
    let ks = <Scalar as Reduce<U384>>::reduce_bytes(FieldBytes::from_slice(&k_be));
    (ks, ProjectivePoint::GENERATOR.double())
}

// ───────────────────────── loop scaffolding baseline ─────────────────────

// The bare loop plus `black_box` scaffolding at `N_FP` iterations, with no
// field work in it.  Subtract this from `*_fp_mul` to get the field
// multiply on its own; it is reported rather than subtracted silently
// because both arms pay it and it therefore hardly moves any ratio.
// (Doc comments are rejected by `#[library_benchmark]`, hence `//`.)
#[library_benchmark]
fn loop_baseline_10k() -> u64 {
    let mut acc = 1u64;
    for _ in 0..N_FP {
        acc = black_box(acc).wrapping_add(black_box(3));
    }
    acc
}

// ───────────────────────────── field multiply ────────────────────────────

#[library_benchmark]
#[bench::chain(setup_fp_ours())]
fn ours_fp_mul(ab: (Fp, Fp)) -> Fp {
    let (a0, b) = ab;
    let mut acc = a0;
    let mut out = Fp([0u64; 6]);
    for _ in 0..N_FP {
        fp_mul(&mut out, black_box(&acc), black_box(&b));
        acc = out;
    }
    assert_ne!(acc.0, a0.0, "fp_mul chain did not advance — loop optimised away");
    acc
}

#[library_benchmark]
#[bench::chain(setup_fp_theirs())]
fn rustcrypto_fp_mul(ab: (RcFe, RcFe)) -> RcFe {
    let (a0, b) = ab;
    let mut acc = a0;
    for _ in 0..N_FP {
        acc = black_box(&acc).multiply(black_box(&b));
    }
    let (r0, r1): ([u8; 48], [u8; 48]) = (acc.to_repr().into(), a0.to_repr().into());
    assert_ne!(r0, r1, "fp_mul chain did not advance — loop optimised away");
    acc
}

// ─────────────────────────── group add / double ──────────────────────────

#[library_benchmark]
#[bench::generator(setup_g1_ours())]
fn ours_g1_add(pts: (G1, G1)) -> G1 {
    let (g, g2) = pts;
    let mut acc = g2;
    for _ in 0..N_GROUP {
        acc = g1_add(black_box(&acc), black_box(&g));
    }
    assert_ne!(acc.x.0, g2.x.0, "g1_add chain did not advance — loop optimised away");
    acc
}

#[library_benchmark]
#[bench::generator(setup_g1_theirs())]
fn rustcrypto_g1_add(pts: (ProjectivePoint, ProjectivePoint)) -> ProjectivePoint {
    let (rg, rg2) = pts;
    let mut acc = rg2;
    for _ in 0..N_GROUP {
        acc = black_box(&acc).add(black_box(&rg));
    }
    acc
}

#[library_benchmark]
#[bench::generator(setup_g1_ours())]
fn ours_g1_double(pts: (G1, G1)) -> G1 {
    let (_g, g2) = pts;
    let mut acc = g2;
    for _ in 0..N_GROUP {
        acc = g1_double(black_box(&acc));
    }
    assert_ne!(acc.x.0, g2.x.0, "g1_double chain did not advance — loop optimised away");
    acc
}

#[library_benchmark]
#[bench::generator(setup_g1_theirs())]
fn rustcrypto_g1_double(pts: (ProjectivePoint, ProjectivePoint)) -> ProjectivePoint {
    let (_rg, rg2) = pts;
    let mut acc = rg2;
    for _ in 0..N_GROUP {
        acc = black_box(&acc).double();
    }
    acc
}

// ───────────────────── variable-base scalar multiply ─────────────────────

#[library_benchmark]
#[bench::generator(setup_smul_ours())]
fn ours_g1_scalar_mul(g2: G1) -> G1 {
    let mut acc = g2;
    for _ in 0..N_MUL {
        acc = g1_scalar_mul(black_box(&K_LIMBS), black_box(&g2));
    }
    acc
}

#[library_benchmark]
#[bench::generator(setup_smul_theirs())]
fn rustcrypto_g1_scalar_mul(kp: (Scalar, ProjectivePoint)) -> ProjectivePoint {
    let (ks, rg2) = kp;
    let mut acc = rg2;
    for _ in 0..N_MUL {
        acc = black_box(rg2) * black_box(ks);
    }
    acc
}

library_benchmark_group!(
    name = p384_iai;
    benchmarks =
        loop_baseline_10k,
        ours_fp_mul,
        rustcrypto_fp_mul,
        ours_g1_add,
        rustcrypto_g1_add,
        ours_g1_double,
        rustcrypto_g1_double,
        ours_g1_scalar_mul,
        rustcrypto_g1_scalar_mul
);

main!(library_benchmark_groups = p384_iai);
