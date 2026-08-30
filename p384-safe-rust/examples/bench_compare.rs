//! Side-by-side P-384 group benchmark: this crate vs RustCrypto `p384`,
//! same machine, same process, same iteration counts, same `black_box`
//! discipline.
//!
//! Run pinned to one core for stability:
//!   taskset -c 2 cargo run --release --offline -p p384-safe-rust --example bench_compare
//!
//! ## MEASUREMENT (read before quoting a number)
//!
//! The primary column is **cycles**; nanoseconds are secondary.  Cycles are
//! read with `_rdtsc` fenced by `lfence` on both sides.  This host reports
//! `constant_tsc` + `nonstop_tsc`, so the counter ticks at a fixed reference
//! rate independent of the core's actual frequency.  These are therefore
//! *invariant-TSC reference cycles*, not retired core cycles; a true
//! core-cycle count needs `perf_event_open`, and `perf_event_paranoid` is 4
//! on this host, so it is unavailable without a root sysctl.  Reference
//! cycles are far more stable than wall-clock nanoseconds under background
//! load, which is why the ratios below are computed on cycles.
//!
//! Both arms run in ONE process and are INTERLEAVED round by round, and per
//! row the round MINIMUM is reported.  Interleaving means a load spike hits
//! both arms; the minimum discards the rounds it hit.  (Before this file was
//! converted it did a single untimed-repetition run per arm, which is the
//! measurement shape most vulnerable to background load on this machine.)
//!
//! Each timing loop is a serial dependency chain — iteration `i + 1` consumes
//! the result of iteration `i` — with the *operands* inside `black_box`.
//! `black_box` on the result alone does NOT stop LLVM hoisting a
//! loop-invariant computation out of the loop.  `assert_floor` fails the run
//! rather than printing a figure only an optimised-away loop could produce.
//!
//! ## WHAT IS AND IS NOT COMPARABLE
//!
//! * `g1_add` / `g1_double`.  Both arms use the `a = -3` Renes-Costello-Batina
//!   2015 specialisations, RCB **Algorithm 4** (add) and **Algorithm 6**
//!   (double).  Ours is the Rocq-derived body of `CurveAddA3.v` /
//!   `CurveDoubleA3.v`; `group::g1_add_general_a` keeps the 40-field-op
//!   **Algorithm 1** chain (complete addition for general `a`, transcribed
//!   from the Qed-proved bedrock2 body `P256_G1_add`) for reference.
//!
//! * `g1_scalar_mul`.  **Both arms are variable-base, and both are a 4-bit
//!   fixed window.**  Ours builds a 15-entry table of multiples of the input
//!   point per call, then runs 96 windows of 4 doublings and one complete
//!   addition, selecting the table entry by a full linear scan with
//!   `ct_eq_mask` / `ct_select_limbs_mask`.  RustCrypto
//!   (`primeorder::ProjectivePoint::mul`) builds a 16-entry table and does
//!   384 doublings plus 96 additions, reading the table by a constant-time
//!   linear scan with `conditional_assign` over all 16 entries.  The
//!   algorithms match; what remains is the formula difference.
//!   `group::g1_scalar_mul_width1` keeps the width-1 double-and-add-always
//!   ladder this arm used to run, as the differential-test reference.
//!
//! * Neither arm is a fixed-base benchmark.  `primeorder` 0.13.6 has no
//!   precomputed generator tables at all -- its `MulByGenerator` impl is
//!   literally `Self::generator() * scalar`, carrying a `TODO(tarcieri)` for
//!   the tables -- so there is no fixed-base path in this version to compare
//!   against, and the point fed to both arms below is the same non-generator
//!   point in any case.
//!
//! * Constant time.  **Both arms are constant time** with respect to the
//!   scalar and the point coordinates.  Ours: complete formulas, straight-line
//!   fiat-crypto field leaves, mask-based select, no secret-dependent branch or
//!   memory address.  RustCrypto: complete formulas, `subtle` conditional
//!   assignment, full-table linear scan.  Neither uses a variable-time ladder,
//!   so the ratios below are not paying for a timing-leak tradeoff in either
//!   direction.
//!
//! * Field layer.  Both arms run the *same* fiat-crypto word-by-word
//!   Montgomery output for P-384: ours from `fiat-crypto/fiat-rust`
//!   (`p384_64`), theirs from `p384/src/arithmetic/field/p384_64.rs`, whose
//!   header records the identical `word_by_word_montgomery --lang Rust
//!   --inline p384 64` invocation (postprocessed by `fiat-constify`).  The
//!   P-384 numbers below are therefore close to a pure point-layer comparison.

use std::hint::black_box;
use std::time::Instant;

const N_ADD: u64 = 300_000;
const N_DBL: u64 = 300_000;
const N_MUL: u64 = 100;

/// Number of interleaved rounds; the per-row minimum is reported.
const ROUNDS: usize = 7;

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

/// The one scalar both arms multiply by, as little-endian u64 limbs.
/// The top limb is small enough that the value is below the group order,
/// so RustCrypto's `reduce_bytes` is the identity on it and both arms see
/// the same integer.
const K_LIMBS: [u64; 6] = [
    0x0123_4567_89ab_cdef,
    0xfedc_ba98_7654_3210,
    0x0f1e_2d3c_4b5a_6978,
    0x1122_3344_5566_7788,
    0x99aa_bbcc_ddee_ff00,
    0x0a1b_2c3d_4e5f_6071,
];

/// The same integer as `K_LIMBS`, 48 bytes big-endian.
fn scalar_be() -> [u8; 48] {
    let mut out = [0u8; 48];
    for (i, limb) in K_LIMBS.iter().enumerate() {
        let off = 40 - 8 * i;
        out[off..off + 8].copy_from_slice(&limb.to_be_bytes());
    }
    out
}

fn main() {
    let k_be = scalar_be();

    println!("P-384 (secp384r1) group operations -- this work vs RustCrypto p384 0.13.1");
    println!();
    println!("cycles are invariant-TSC REFERENCE cycles (constant_tsc + nonstop_tsc),");
    println!("not retired core cycles.  Ratios are computed on cycles.");
    println!("Both arms in ONE process, {ROUNDS} interleaved rounds, per-row minimum.");
    println!();

    use p384::group::*;
    use p384_rc::elliptic_curve::group::Group;
    use p384_rc::elliptic_curve::ops::Reduce;
    use p384_rc::{FieldBytes, ProjectivePoint, Scalar, U384};

    let g = g1_generator();
    let g2 = g1_double(&g);

    let rg = ProjectivePoint::GENERATOR;
    let rg2 = rg.double();
    let ks = <Scalar as Reduce<U384>>::reduce_bytes(FieldBytes::from_slice(&k_be));

    // Warm up both arms before any timing.
    {
        let mut a = g2;
        let mut r = rg2;
        for _ in 0..N_ADD / 10 {
            a = g1_add(black_box(&a), black_box(&g));
            a = g1_double(black_box(&a));
            r = black_box(&r).add(black_box(&rg));
            r = black_box(&r).double();
        }
        black_box(&a);
        black_box(&r);
        for _ in 0..N_MUL / 5 + 1 {
            black_box(g1_scalar_mul(black_box(&K_LIMBS), black_box(&g2)));
            black_box(black_box(rg2) * black_box(ks));
        }
    }

    let (mut o_add, mut o_dbl, mut o_mul, mut o_mul_w1) =
        (M::worst(), M::worst(), M::worst(), M::worst());
    let (mut r_add, mut r_dbl, mut r_mul) = (M::worst(), M::worst(), M::worst());
    #[cfg(feature = "extracted")]
    let mut o_wnaf = M::worst();

    for _ in 0..ROUNDS {
        // --- add: ours, then theirs ---
        let mut acc = g2;
        o_add = o_add.min(round(N_ADD, || acc = g1_add(black_box(&acc), black_box(&g))));
        black_box(&acc);
        let mut racc = rg2;
        r_add = r_add.min(round(N_ADD, || racc = black_box(&racc).add(black_box(&rg))));
        black_box(&racc);

        // --- double ---
        let mut acc = g2;
        o_dbl = o_dbl.min(round(N_DBL, || acc = g1_double(black_box(&acc))));
        black_box(&acc);
        let mut racc = rg2;
        r_dbl = r_dbl.min(round(N_DBL, || racc = black_box(&racc).double()));
        black_box(&racc);

        // --- scalar mul (variable base) ---
        let mut acc = g2;
        o_mul = o_mul.min(round(N_MUL, || {
            acc = g1_scalar_mul(black_box(&K_LIMBS), black_box(&g2))
        }));
        black_box(&acc);
        let mut racc = rg2;
        r_mul = r_mul.min(round(N_MUL, || racc = black_box(rg2) * black_box(ks)));
        black_box(&racc);

        // --- the width-1 double-and-add-always ladder ours replaced ---
        let mut acc = g2;
        o_mul_w1 = o_mul_w1.min(round(N_MUL, || {
            acc = g1_scalar_mul_width1(black_box(&K_LIMBS), black_box(&g2))
        }));
        black_box(&acc);

        // The Rocq-emitted w = 4 wNAF driver, when it is compiled in.
        // VARIABLE TIME (branches on the digit, digit-indexed table read).
        #[cfg(feature = "extracted")]
        {
            use p384::wnaf::g1_scalar_mul_wnaf;
            let mut acc = g2;
            o_wnaf = o_wnaf.min(round(N_MUL, || {
                acc = g1_scalar_mul_wnaf(black_box(&K_LIMBS), black_box(&g2))
            }));
            black_box(&acc);
        }
    }

    // A complete addition is >= 10 6x64 Montgomery multiplies; a 384-bit
    // scalar multiplication is >= 384 doublings.
    for (n, m) in [("ours add", o_add), ("RustCrypto add", r_add),
                   ("ours double", o_dbl), ("RustCrypto double", r_dbl)] {
        assert_floor(n, m, 60.0);
    }
    for (n, m) in [("ours scalar_mul", o_mul), ("RustCrypto scalar_mul", r_mul),
                   ("ours scalar_mul width1", o_mul_w1)] {
        assert_floor(n, m, 10_000.0);
    }

    println!("=== per-arm figures ===");
    println!(
        "{:<26} {:>12} {:>10}   {:>12} {:>10}",
        "operation", "ours (cyc)", "ours (ns)", "RC (cyc)", "RC (ns)"
    );
    println!("{}", "-".repeat(78));
    let pair = |name: &str, a: M, b: M| {
        println!(
            "{:<26} {:>12.1} {:>10.1}   {:>12.1} {:>10.1}",
            name, a.cyc, a.ns, b.cyc, b.ns
        );
    };
    pair("add", o_add, r_add);
    pair("double", o_dbl, r_dbl);
    pair("scalar_mul (var-base)", o_mul, r_mul);
    println!(
        "{:<26} {:>12.1} {:>10.1}",
        "  ^ width-1, reference", o_mul_w1.cyc, o_mul_w1.ns
    );
    #[cfg(feature = "extracted")]
    println!(
        "{:<26} {:>12.1} {:>10.1}    (VARIABLE TIME)",
        "  ^ wNAF, Rocq-emitted", o_wnaf.cyc, o_wnaf.ns
    );

    println!();
    println!("=== comparison (cycles) ===");
    println!("{:<26} {:>14} {:>14} {:>12}", "operation", "ours (cyc)", "RustCrypto (cyc)", "ratio");
    println!("{}", "-".repeat(70));
    let row = |name: &str, ours: M, theirs: M| {
        println!(
            "{:<26} {:>14.1} {:>14.1} {:>11.2}x",
            name, ours.cyc, theirs.cyc, ours.cyc / theirs.cyc
        );
    };
    row("add", o_add, r_add);
    row("double", o_dbl, r_dbl);
    row("scalar_mul (var-base)", o_mul, r_mul);
    row("  ^ width-1, reference", o_mul_w1, r_mul);
    #[cfg(feature = "extracted")]
    row("  ^ wNAF, var-time", o_wnaf, r_mul);

    println!();
    println!("ratio = ours / RustCrypto on CYCLES; below 1.00 means this work is faster.");
    println!("TSC reference rate here: {:.3} GHz (from the add row).", o_add.cyc / o_add.ns);
    println!();
    println!("Caveats (full text at the head of this file):");
    println!("  - add/double: BOTH arms use the a = -3 specialisation (RCB Alg.4 / Alg.6).");
    println!("    Ours is the Rocq-derived body of CurveAddA3.v / CurveDoubleA3.v;");
    println!("    group::g1_add_general_a keeps the 40-op Alg.1 chain for reference.");
    println!("  - scalar_mul: BOTH arms are variable-base 4-bit fixed windows with a");
    println!("    per-call table of multiples of the input point, read by a full");
    println!("    constant-time linear scan.  Ours: 15 entries, 387 dbl + 102 add");
    println!("    (table build included).  Theirs: 16 entries, 384 dbl + 96 add.");
    println!("    primeorder 0.13.6 has no precomputed generator tables, so no");
    println!("    fixed-base path is being compared here.");
    println!("  - BOTH arms are constant time in the scalar and the coordinates -- EXCEPT");
    println!("    the `wNAF, var-time` row, which is the Rocq-emitted w=4 wNAF driver of");
    println!("    src/scalar_mul_extracted.rs.  That one branches on each digit and reads");
    println!("    its 4-entry table at a digit-derived index, so it is NOT constant time.");
    println!("  - Field layer: both arms use the SAME fiat-crypto p384_64 word-by-word");
    println!("    Montgomery output, so this is close to a pure point-layer comparison.");
}
