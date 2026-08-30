//! Side-by-side P-256 group benchmark: this crate vs RustCrypto `p256`,
//! same machine, same process, same iteration counts, same `black_box`
//! discipline.
//!
//! Run pinned to one core for stability:
//!   taskset -c 2 cargo run --release --offline -p p256-safe-rust --example bench_compare
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
//! Both arms run in ONE process and are INTERLEAVED round by round: within a
//! round, ours is timed, then RustCrypto's, then the next round starts.  Per
//! row the round MINIMUM is reported.  Interleaving means a load spike hits
//! both arms, and the minimum discards the rounds it hit.  A pair of
//! one-shot timing runs, one arm each, does neither.
//!
//! Each timing loop is a serial dependency chain — iteration `i + 1` consumes
//! the result of iteration `i` — with the *operands* inside `black_box`.
//! `black_box` on the result alone does NOT stop LLVM hoisting a
//! loop-invariant computation out of the loop.  `assert_floor` fails the run
//! rather than printing a figure only an optimised-away loop could produce.
//!
//! ## WHAT IS AND IS NOT COMPARABLE
//!
//! * `g1_add` / `g1_double`.  Ours is a line-by-line transcription of the
//!   Qed-proved bedrock2 body `P256_G1_add`
//!   (`src/Bedrock/Curve/P256_G1_Add_Spec.v`), which is Renes-Costello-Batina
//!   2015 **Algorithm 1**, the complete addition for *general* `a`, 40 field
//!   operations; doubling is self-addition through that same routine.
//!   RustCrypto dispatches on `EquationAIsMinusThree` and uses the
//!   `a = -3` specialisations, RCB **Algorithm 4** (add) and **Algorithm 6**
//!   (double).  P-256 has `a = -3`, so the specialised formulas are available
//!   to us too and are simply not what the proved body implements.  A slower
//!   number here is a formula-choice gap, not a field-arithmetic gap.
//!
//! * `g1_scalar_mul`.  **Both arms are variable-base, and both are now a
//!   4-bit fixed window.**  Ours builds a 15-entry table of multiples of the
//!   input point per call, then runs 64 windows of 4 doublings and one
//!   complete addition, selecting the table entry by a full linear scan with
//!   `ct_eq_mask` / limb-mask select.  RustCrypto
//!   (`primeorder::ProjectivePoint::mul`) builds a 16-entry table and does
//!   256 doublings plus 64 additions, reading the table by a constant-time
//!   linear scan with `conditional_assign` over all 16 entries.  The
//!   algorithms now match; what remains is the formula and field difference.
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
//!   fiat-crypto field leaves, limb-mask select, no secret-dependent branch or
//!   memory address.  RustCrypto: complete formulas, `subtle` conditional
//!   assignment, full-table linear scan.  Neither uses a variable-time ladder,
//!   so the ratios below are not paying for a timing-leak tradeoff in either
//!   direction.
//!
//! * Field layer.  Both sides are 4x64 saturated Montgomery, and neither is
//!   plain fiat-crypto.  RustCrypto's P-256 field is hand-written
//!   (`p256/src/arithmetic/field/field64.rs`), folding the P-256-specific
//!   reduction structure into `montgomery_reduce`.  Ours is fiat-crypto
//!   `p256_64` for add/sub/opp and CryptOpt-superoptimized assembly for
//!   mul/square (`generated/p256_*_cryptopt.asm`), which computes the same
//!   function as the fiat leaf it replaces -- see `tests/cryptopt_diff.rs`.
//!   Run `--example bench_field` for the per-operation field numbers, and
//!   build with `P256_NO_CRYPTOPT=1` to see the pure-fiat field layer.
//!   (For P-384 both sides are still plain fiat-crypto -- see the p384
//!   sibling of this file.)

use std::hint::black_box;
use std::time::Instant;

const N_ADD: u64 = 500_000;
const N_DBL: u64 = 500_000;
const N_MUL: u64 = 300;

/// Number of interleaved rounds; the per-row minimum is reported.  Every
/// source of error on a shared machine -- a competing process, a frequency
/// dip, a migration -- adds time and none subtracts it.
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

/// Refuse to report a figure that cannot be real.  Below the floor means the
/// timing loop was optimised away.
fn assert_floor(label: &str, m: M, floor: f64) {
    assert!(
        m.cyc >= floor,
        "{label}: {:.2} cycles/op is below the {floor} cycle floor — the timing \
         loop was optimised away.  Check that the operands are inside black_box \
         and that each iteration consumes the previous result.",
        m.cyc
    );
}

/// The one scalar both arms multiply by, 32 bytes big-endian.
/// Top byte 0x1a keeps it below the group order, so RustCrypto's
/// `reduce_bytes` is the identity on it and both arms see the same integer.
fn scalar_be() -> [u8; 32] {
    let mut k = [0u8; 32];
    k[0] = 0x1a;
    for (i, b) in k.iter_mut().enumerate().skip(1) {
        *b = (i as u8).wrapping_mul(37).wrapping_add(11);
    }
    k
}

fn main() {
    let k = scalar_be();

    println!("P-256 (secp256r1) group operations -- this work vs RustCrypto p256 0.13.2");
    println!();
    println!("cycles are invariant-TSC REFERENCE cycles (constant_tsc + nonstop_tsc),");
    println!("not retired core cycles.  Ratios are computed on cycles.");
    println!("Both arms in ONE process, {ROUNDS} interleaved rounds, per-row minimum.");
    println!();

    use p256::group::*;
    use p256_rc::elliptic_curve::group::Group;
    use p256_rc::elliptic_curve::ops::Reduce;
    use p256_rc::{FieldBytes, ProjectivePoint, Scalar, U256};

    // ---- ours ----
    let g = g1_generator();
    let g2 = g1_double(&g);

    // ---- RustCrypto ----
    let rg = ProjectivePoint::GENERATOR;
    let rg2 = rg.double();
    let ks = <Scalar as Reduce<U256>>::reduce_bytes(FieldBytes::from_slice(&k));

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
            black_box(g1_scalar_mul(black_box(&k), black_box(&g2)));
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
            acc = g1_scalar_mul(black_box(&k), black_box(&g2))
        }));
        black_box(&acc);
        let mut racc = rg2;
        r_mul = r_mul.min(round(N_MUL, || racc = black_box(rg2) * black_box(ks)));
        black_box(&racc);

        // --- the width-1 double-and-add-always ladder ours replaced ---
        let mut acc = g2;
        o_mul_w1 = o_mul_w1.min(round(N_MUL, || {
            acc = g1_scalar_mul_width1(black_box(&k), black_box(&g2))
        }));
        black_box(&acc);

        // The Rocq-emitted w = 4 wNAF driver, when it is compiled in.
        // VARIABLE TIME (branches on the digit, digit-indexed table read),
        // unlike every other arm in this file.
        #[cfg(feature = "extracted")]
        {
            use p256::wnaf::g1_scalar_mul_wnaf;
            let mut acc = g2;
            o_wnaf = o_wnaf.min(round(N_MUL, || {
                acc = g1_scalar_mul_wnaf(black_box(&k), black_box(&g2))
            }));
            black_box(&acc);
        }
    }

    // A complete addition is >= 10 4x64 Montgomery multiplies; a 256-bit
    // scalar multiplication is >= 256 doublings.
    for (n, m) in [("ours add", o_add), ("RustCrypto add", r_add),
                   ("ours double", o_dbl), ("RustCrypto double", r_dbl)] {
        assert_floor(n, m, 40.0);
    }
    for (n, m) in [("ours scalar_mul", o_mul), ("RustCrypto scalar_mul", r_mul),
                   ("ours scalar_mul width1", o_mul_w1)] {
        assert_floor(n, m, 5_000.0);
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
    println!("  - add/double: BOTH arms now use the a = -3 specialisation (RCB Alg.4 /");
    println!("    Alg.6).  Ours is the Rocq-derived body of CurveAddA3.v / CurveDoubleA3.v;");
    println!("    group::g1_add_general_a keeps the 40-op Alg.1 chain for reference.");
    println!("  - scalar_mul: BOTH arms are variable-base 4-bit fixed windows with a");
    println!("    per-call table of multiples of the input point, read by a full");
    println!("    constant-time linear scan.  Ours: 15 entries, 259 dbl + 70 add");
    println!("    (table build included).  Theirs: 16 entries, 256 dbl + 64 add.");
    println!("    primeorder 0.13.6 has no precomputed generator tables, so no");
    println!("    fixed-base path is being compared here.");
    println!("  - BOTH arms are constant time in the scalar and the coordinates -- EXCEPT");
    println!("    the `wNAF, var-time` row, which is the Rocq-emitted w=4 wNAF driver of");
    println!("    src/scalar_mul_extracted.rs.  That one branches on each digit and reads");
    println!("    its 4-entry table at a digit-derived index, so it is NOT constant time");
    println!("    and is not comparable to the others on a side-channel basis.");
    println!("  - Field layer: both sides are 4x64 Montgomery.  RustCrypto's is");
    println!("    hand-written; ours is fiat-crypto p256_64 for add/sub and CryptOpt");
    println!("    assembly for mul/square (P256_NO_CRYPTOPT=1 reverts to pure fiat).");
    println!(
        "    This build's mul/square leaves: {}",
        if p256::CRYPTOPT_ASM { "CryptOpt assembly" } else { "fiat-rust" }
    );
}
