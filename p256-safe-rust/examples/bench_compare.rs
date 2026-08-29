//! Side-by-side P-256 group benchmark: this crate vs RustCrypto `p256`,
//! same machine, same iteration counts, same `black_box` discipline.
//!
//! Run pinned to one core for stability:
//!   taskset -c 2 cargo run --release --offline -p p256-safe-rust --example bench_compare
//!
//! WHAT IS AND IS NOT COMPARABLE (read before quoting a ratio)
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
//! * `g1_scalar_mul`.  **Both arms are variable-base.**  Ours is a fixed-length
//!   MSB-first double-and-add-always over all 256 bits: 256 doublings plus 256
//!   additions, every one of them executed, the conditional accumulate done by
//!   a limb-mask `cmov`.  Width is 1; there is no windowing and no wNAF, and no
//!   table of any kind is precomputed.  RustCrypto is a **4-bit fixed window**
//!   (`primeorder::ProjectivePoint::mul`): it builds a 16-entry table of
//!   multiples of *the input point* on every call, then does 256 doublings plus
//!   64 additions, reading the table by a constant-time linear scan with
//!   `conditional_assign` over all 16 entries.  Roughly a 4x advantage in
//!   additions before any formula difference is counted.
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

const N_ADD: u64 = 2_000_000;
const N_DBL: u64 = 2_000_000;
const N_MUL: u64 = 2_000;

/// Number of timed repetitions per measurement; the minimum is reported.
/// The minimum is the right summary here because every source of error on a
/// shared machine -- a competing process, a frequency dip, a migration --
/// adds time and none subtracts it.
const REPS: usize = 7;

/// Warm up for `iters / 10` calls, then time `iters` calls `REPS` times and
/// return the smallest ns/op observed.
fn bench<F: FnMut()>(iters: u64, mut f: F) -> f64 {
    for _ in 0..(iters / 10 + 1) {
        f();
    }
    let mut best = f64::INFINITY;
    for _ in 0..REPS {
        let start = Instant::now();
        for _ in 0..iters {
            f();
        }
        let t = start.elapsed().as_nanos() as f64 / iters as f64;
        if t < best {
            best = t;
        }
    }
    best
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

    // ---------------------------------------------------------------
    // This work: proved RCB Algorithm 1 (general a) + width-1 CT ladder
    // ---------------------------------------------------------------
    println!("=== p256-safe-rust (this work: RCB Alg.4/Alg.6 a=-3, fiat-crypto leaves) ===");
    let (ours_add, ours_dbl, ours_mul) = {
        use p256::group::*;

        let g = g1_generator();
        let g2 = g1_double(&g);

        let mut acc = g2;
        let add = bench(N_ADD, || acc = g1_add(black_box(&acc), black_box(&g)));
        black_box(&acc);

        let mut acc = g2;
        let dbl = bench(N_DBL, || acc = g1_double(black_box(&acc)));
        black_box(&acc);

        let mut acc = g2;
        let mul = bench(N_MUL, || acc = g1_scalar_mul(black_box(&k), black_box(&g2)));
        black_box(&acc);

        println!("  g1_add:        {:>12.1} ns/op   ({} iters)", add, N_ADD);
        println!("  g1_double:     {:>12.1} ns/op   ({} iters)", dbl, N_DBL);
        println!("  g1_scalar_mul: {:>12.1} ns/op   ({} iters)", mul, N_MUL);
        (add, dbl, mul)
    };

    // The Rocq-emitted w = 4 wNAF driver, when it is compiled in.
    // VARIABLE TIME (branches on the digit, digit-indexed table read),
    // unlike every other arm in this file.
    #[cfg(feature = "extracted")]
    let ours_wnaf = {
        use p256::group::*;
        use p256::wnaf::g1_scalar_mul_wnaf;
        let g2 = g1_double(&g1_generator());
        let mut acc = g2;
        let mul = bench(N_MUL, || {
            acc = g1_scalar_mul_wnaf(black_box(&k), black_box(&g2))
        });
        black_box(&acc);
        println!(
            "  g1_scalar_mul wNAF (Rocq-emitted, VARIABLE TIME): {:>10.1} ns/op   ({} iters)",
            mul, N_MUL
        );
        Some(mul)
    };
    #[cfg(not(feature = "extracted"))]
    let ours_wnaf: Option<f64> = None;

    println!();

    // ---------------------------------------------------------------
    // RustCrypto: RCB a = -3 specialisations + 4-bit fixed window
    // ---------------------------------------------------------------
    println!("=== RustCrypto p256 0.13.2 (production Rust: RCB a=-3, 4-bit window) ===");
    let (rc_add, rc_dbl, rc_mul) = {
        use p256_rc::elliptic_curve::group::Group;
        use p256_rc::elliptic_curve::ops::Reduce;
        use p256_rc::{FieldBytes, ProjectivePoint, Scalar, U256};

        let g = ProjectivePoint::GENERATOR;
        let g2 = g.double();
        let ks = <Scalar as Reduce<U256>>::reduce_bytes(FieldBytes::from_slice(&k));

        let mut acc = g2;
        let add = bench(N_ADD, || acc = black_box(&acc).add(black_box(&g)));
        black_box(&acc);

        let mut acc = g2;
        let dbl = bench(N_DBL, || acc = black_box(&acc).double());
        black_box(&acc);

        let mut acc = g2;
        let mul = bench(N_MUL, || acc = black_box(g2) * black_box(ks));
        black_box(&acc);

        println!("  add:           {:>12.1} ns/op   ({} iters)", add, N_ADD);
        println!("  double:        {:>12.1} ns/op   ({} iters)", dbl, N_DBL);
        println!("  mul (var-base):{:>12.1} ns/op   ({} iters)", mul, N_MUL);
        (add, dbl, mul)
    };

    // ---------------------------------------------------------------
    println!();
    println!("=== comparison ===");
    println!(
        "{:<22} {:>14} {:>14} {:>12}",
        "operation", "ours (ns)", "RustCrypto (ns)", "ratio"
    );
    println!("{}", "-".repeat(66));
    let row = |name: &str, ours: f64, theirs: f64| {
        println!(
            "{:<22} {:>14.1} {:>14.1} {:>11.2}x",
            name,
            ours,
            theirs,
            ours / theirs
        );
    };
    row("add", ours_add, rc_add);
    row("double", ours_dbl, rc_dbl);
    row("scalar_mul (var-base)", ours_mul, rc_mul);
    if let Some(w) = ours_wnaf {
        row("  ^ wNAF, var-time", w, rc_mul);
    }
    println!();
    println!("ratio = ours / RustCrypto; below 1.00 means this work is faster.");
    println!();
    println!("Caveats (full text at the head of this file):");
    println!("  - add/double: BOTH arms now use the a = -3 specialisation (RCB Alg.4 /");
    println!("    Alg.6).  Ours is the Rocq-derived body of CurveAddA3.v / CurveDoubleA3.v;");
    println!("    group::g1_add_general_a keeps the 40-op Alg.1 chain for reference.");
    println!("  - scalar_mul: BOTH arms are variable-base.  Ours is width-1");
    println!("    double-and-add-always (256 dbl + 256 add).  Theirs is a 4-bit fixed");
    println!("    window with a per-call 16-entry table of the input point");
    println!("    (256 dbl + 64 add).  primeorder 0.13.6 has no precomputed generator");
    println!("    tables, so no fixed-base path is being compared here.");
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
