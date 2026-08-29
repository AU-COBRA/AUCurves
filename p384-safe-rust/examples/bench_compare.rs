//! Side-by-side P-384 group benchmark: this crate vs RustCrypto `p384`,
//! same machine, same iteration counts, same `black_box` discipline.
//!
//! Run pinned to one core for stability:
//!   taskset -c 2 cargo run --release --offline -p p384-safe-rust --example bench_compare
//!
//! WHAT IS AND IS NOT COMPARABLE (read before quoting a ratio)
//!
//! * `g1_add` / `g1_double`.  Ours is the 40-field-op Renes-Costello-Batina
//!   2015 **Algorithm 1** sequence -- the complete addition for *general* `a`
//!   -- transcribed from the Qed-proved bedrock2 body `P256_G1_add`
//!   (`src/Bedrock/Curve/P256_G1_Add_Spec.v`), which is curve-generic in `a`
//!   and `3b`; doubling is self-addition through that same routine.
//!   RustCrypto dispatches on `EquationAIsMinusThree` and uses the `a = -3`
//!   specialisations, RCB **Algorithm 4** (add) and **Algorithm 6** (double).
//!   P-384 has `a = -3`, so the specialised formulas are available to us too
//!   and are simply not what the proved body implements.  A slower number here
//!   is a formula-choice gap, not a field-arithmetic gap.
//!
//! * `g1_scalar_mul`.  **Both arms are variable-base.**  Ours is a fixed-length
//!   MSB-first double-and-add-always over all 384 bits: 384 doublings plus 384
//!   additions, every one of them executed, the conditional accumulate done by
//!   `ct_select_point`.  Width is 1; there is no windowing and no wNAF, and no
//!   table of any kind is precomputed.  RustCrypto is a **4-bit fixed window**
//!   (`primeorder::ProjectivePoint::mul`): it builds a 16-entry table of
//!   multiples of *the input point* on every call, then does 384 doublings plus
//!   96 additions, reading the table by a constant-time linear scan with
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

const N_ADD: u64 = 1_000_000;
const N_DBL: u64 = 1_000_000;
const N_MUL: u64 = 1_000;

/// Warm up for `iters / 10` calls, then time `iters` calls; return ns/op.
fn bench<F: FnMut()>(iters: u64, mut f: F) -> f64 {
    for _ in 0..(iters / 10 + 1) {
        f();
    }
    let start = Instant::now();
    for _ in 0..iters {
        f();
    }
    start.elapsed().as_nanos() as f64 / iters as f64
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

    // ---------------------------------------------------------------
    // This work: proved RCB Algorithm 1 (general a) + width-1 CT ladder
    // ---------------------------------------------------------------
    println!("=== p384-safe-rust (this work: RCB Alg.4/Alg.6 a=-3, fiat-crypto leaves) ===");
    let (ours_add, ours_dbl, ours_mul) = {
        use p384::group::*;

        let g = g1_generator();
        let g2 = g1_double(&g);

        let mut acc = g2;
        let add = bench(N_ADD, || acc = g1_add(black_box(&acc), black_box(&g)));
        black_box(&acc);

        let mut acc = g2;
        let dbl = bench(N_DBL, || acc = g1_double(black_box(&acc)));
        black_box(&acc);

        let mut acc = g2;
        let mul = bench(N_MUL, || {
            acc = g1_scalar_mul(black_box(&K_LIMBS), black_box(&g2))
        });
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
        use p384::group::*;
        use p384::wnaf::g1_scalar_mul_wnaf;
        let g2 = g1_double(&g1_generator());
        let mut acc = g2;
        let mul = bench(N_MUL, || {
            acc = g1_scalar_mul_wnaf(black_box(&K_LIMBS), black_box(&g2))
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
    println!("=== RustCrypto p384 0.13.1 (production Rust: RCB a=-3, 4-bit window) ===");
    let (rc_add, rc_dbl, rc_mul) = {
        use p384_rc::elliptic_curve::group::Group;
        use p384_rc::elliptic_curve::ops::Reduce;
        use p384_rc::{FieldBytes, ProjectivePoint, Scalar, U384};

        let g = ProjectivePoint::GENERATOR;
        let g2 = g.double();
        let ks = <Scalar as Reduce<U384>>::reduce_bytes(FieldBytes::from_slice(&k_be));

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
    println!("    double-and-add-always (384 dbl + 384 add).  Theirs is a 4-bit fixed");
    println!("    window with a per-call 16-entry table of the input point");
    println!("    (384 dbl + 96 add).  primeorder 0.13.6 has no precomputed generator");
    println!("    tables, so no fixed-base path is being compared here.");
    println!("  - BOTH arms are constant time in the scalar and the coordinates -- EXCEPT");
    println!("    the `wNAF, var-time` row, which is the Rocq-emitted w=4 wNAF driver of");
    println!("    src/scalar_mul_extracted.rs.  That one branches on each digit and reads");
    println!("    its 4-entry table at a digit-derived index, so it is NOT constant time.");
    println!("  - Field layer: both arms use the SAME fiat-crypto p384_64 word-by-word");
    println!("    Montgomery output, so this is close to a pure point-layer comparison.");
}
