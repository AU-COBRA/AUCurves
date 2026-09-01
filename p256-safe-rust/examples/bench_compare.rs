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
//! * `g1_add` / `g1_double`.  **Both arms use the `a = -3` specialisations**,
//!   Renes-Costello-Batina 2015 **Algorithm 4** (add) and **Algorithm 6**
//!   (double).  Ours is the Rocq-derived body of `CurveAddA3.v` /
//!   `CurveDoubleA3.v`, reached through `group::g1_add` / `g1_double`;
//!   `group::g1_add_general_a` keeps the 40-field-op **Algorithm 1** chain
//!   (complete addition for general `a`, transcribed from the Qed-proved
//!   bedrock2 body `P256_G1_add`) as the differential-test reference, and
//!   `CurveA3Equiv.v` proves the two agree as polynomial identities.
//!   RustCrypto dispatches on `EquationAIsMinusThree` to the same two
//!   formulas.  What remains between the arms is the field layer, not the
//!   formula.
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
//! * Against RustCrypto, neither arm is a fixed-base benchmark.
//!   `primeorder` 0.13.6 has no precomputed generator tables at all -- its
//!   `MulByGenerator` impl is literally `Self::generator() * scalar`,
//!   carrying a `TODO(tarcieri)` for the tables -- so there is no fixed-base
//!   path in that crate to compare against, and the point fed to both arms
//!   below is the same non-generator point in any case.  The libcrux arm
//!   described next does have one, and supplies the fixed-base comparison.
//!
//! ## THE LIBCRUX ARM (`--features libcrux_arm`)
//!
//! libcrux's P-256 is the closest peer this project has: another verified
//! pipeline emitting safe Rust for the same curve.  It is hacl-rs -- HACL* C,
//! verified in F* for memory safety, functional correctness and secret
//! independence, mechanically translated to safe Rust by the procedure of
//! "Compiling C to Safe Rust, Formalized" (arXiv:2412.15042).  The two rows
//! below are the only ones where a like-for-like comparison is possible, and
//! they are shaped by what libcrux exposes.
//!
//! * Granularity is forced.  `libcrux-p256` publishes no point addition,
//!   doubling, or bare scalar multiplication, even with `expose-hacl`.  Its
//!   public surface at this level is ECDH: `dh_initiator` (a scalar to a
//!   64-byte public key) and `dh_responder` (a 64-byte peer key and a scalar
//!   to a 64-byte shared secret).  So these two rows are **bytes in, bytes
//!   out**, and both arms pay the same deserialisation, inversion to affine,
//!   and serialisation.  They are NOT comparable to the `add`, `double` and
//!   `scalar_mul` rows above, which are in-memory projective operations.
//!
//! * `ecdh_keygen` is the fixed-base row, `k * G`.  Both arms use a
//!   precomputed table of multiples of the generator: ours is
//!   `group::g1_scalar_mul_base`, a 5-bit comb over the 2387-entry
//!   `G_TABLE` read by a full constant-time linear scan per window; libcrux's
//!   is `point_mul_g` over `p256_precomptable`.
//!
//! * `ecdh_shared` is the variable-base row, `k * P`.  Ours parses the peer
//!   point, checks it is on the curve, and runs the same 4-bit-window
//!   `g1_scalar_mul` as the row above.  libcrux's `dh_responder` parses with
//!   `load_point_vartime` -- **whose own name records that the parse and the
//!   on-curve check are variable time** -- then runs `point_mul`.  The
//!   validity check is over a public peer key in both arms, so this is not a
//!   secret-dependent difference, but the two are not doing identical work
//!   and the row should not be read to three significant figures.
//!
//! * Both arms are checked to agree byte-for-byte before any timing runs.  A
//!   benchmark of two functions computing different values is worthless, so
//!   `main` aborts rather than reporting a number if they diverge.
//!
//! * libcrux additionally range-checks the scalar
//!   (`bn_is_lt_order_and_gt_zero_mask4`) in both entry points; ours does
//!   not.  It is a four-limb comparison against the group order and is
//!   negligible against a scalar multiplication, but it is there.
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
//!   P-384 also routes its field multiply and square to CryptOpt
//!   assembly (p384-safe-rust/build.rs sets `p384_cryptopt_asm`); see
//!   the p384 sibling of this file.

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

// ---------------------------------------------------------------------------
// libcrux arm: byte-level ECDH helpers
// ---------------------------------------------------------------------------
//
// libcrux speaks 32-byte big-endian scalars and 64-byte big-endian raw points
// (x || y, affine, canonical -- not Montgomery).  fiat's `to_bytes` /
// `from_bytes` are little-endian, so each conversion reverses.

/// Montgomery `Fp` -> 32 canonical big-endian bytes.
#[cfg(feature = "libcrux_arm")]
fn fp_to_be32(x: &p256::Fp) -> [u8; 32] {
    use fiat_crypto::p256_64::{fiat_p256_from_montgomery, fiat_p256_to_bytes};
    let mut raw = p256::FpRaw([0u64; 4]);
    fiat_p256_from_montgomery(&mut raw, x);
    let mut b = [0u8; 32];
    fiat_p256_to_bytes(&mut b, &raw.0);
    b.reverse();
    b
}

/// 32 canonical big-endian bytes -> Montgomery `Fp`.
#[cfg(feature = "libcrux_arm")]
fn fp_from_be32(be: &[u8; 32]) -> p256::Fp {
    use fiat_crypto::p256_64::{fiat_p256_from_bytes, fiat_p256_to_montgomery};
    let mut le = *be;
    le.reverse();
    let mut limbs = [0u64; 4];
    fiat_p256_from_bytes(&mut limbs, &le);
    let mut m = p256::Fp([0u64; 4]);
    fiat_p256_to_montgomery(&mut m, &p256::FpRaw(limbs));
    m
}

/// Our `dh_initiator`: fixed-base `k * G`, serialised the way libcrux does.
///
/// Returns the identity encoding (all zero) for the scalar-zero case, which
/// is what `point_store` on the point at infinity produces on the other side.
#[cfg(feature = "libcrux_arm")]
fn ours_dh_initiator(k: &[u8; 32]) -> [u8; 64] {
    let p = p256::group::g1_scalar_mul_base(k);
    let mut out = [0u8; 64];
    if let Some((x, y)) = p256::group::g1_to_affine(&p) {
        out[..32].copy_from_slice(&fp_to_be32(&x));
        out[32..].copy_from_slice(&fp_to_be32(&y));
    }
    out
}

/// Our `dh_responder`: parse, validate, variable-base `k * P`, serialise.
#[cfg(feature = "libcrux_arm")]
fn ours_dh_responder(their_pk: &[u8; 64], k: &[u8; 32]) -> Option<[u8; 64]> {
    let mut xb = [0u8; 32];
    let mut yb = [0u8; 32];
    xb.copy_from_slice(&their_pk[..32]);
    yb.copy_from_slice(&their_pk[32..]);
    let x = fp_from_be32(&xb);
    let y = fp_from_be32(&yb);
    if !p256::group::g1_affine_on_curve(&x, &y) {
        return None;
    }
    let p = p256::group::g1_from_affine(&x, &y);
    let q = p256::group::g1_scalar_mul(k, &p);
    let mut out = [0u8; 64];
    if let Some((ax, ay)) = p256::group::g1_to_affine(&q) {
        out[..32].copy_from_slice(&fp_to_be32(&ax));
        out[32..].copy_from_slice(&fp_to_be32(&ay));
    }
    Some(out)
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

    // ---- libcrux arm: agreement check, then the two ECDH measurements ----
    #[cfg(feature = "libcrux_arm")]
    let (mut o_kg, mut l_kg, mut o_ss, mut l_ss) =
        (M::worst(), M::worst(), M::worst(), M::worst());
    #[cfg(feature = "libcrux_arm")]
    let peer_pk: [u8; 64];

    #[cfg(feature = "libcrux_arm")]
    {
        // A second scalar, for the peer's key.  Same construction as `k`, so
        // it is likewise below the group order and libcrux accepts it.
        let mut k2 = [0u8; 32];
        k2[0] = 0x0b;
        for (i, b) in k2.iter_mut().enumerate().skip(1) {
            *b = (i as u8).wrapping_mul(53).wrapping_add(7);
        }

        // Agreement, checked before anything is timed.  Comparing the speed
        // of two functions that compute different values would be
        // meaningless, so a mismatch aborts instead of printing a figure.
        let mine_pk = ours_dh_initiator(&k);
        let mut theirs_pk = [0u8; 64];
        assert!(
            libcrux_p256::dh_initiator(&mut theirs_pk, &k),
            "libcrux rejected the benchmark scalar"
        );
        assert_eq!(
            mine_pk, theirs_pk,
            "k*G disagrees between this crate and libcrux -- the benchmark \
             below would be comparing two different computations"
        );

        peer_pk = ours_dh_initiator(&k2);
        let mine_ss = ours_dh_responder(&peer_pk, &k)
            .expect("peer key generated by this crate must be on the curve");
        let mut theirs_ss = [0u8; 64];
        assert!(
            libcrux_p256::dh_responder(&mut theirs_ss, &peer_pk, &k),
            "libcrux rejected the peer key or the scalar"
        );
        assert_eq!(
            mine_ss, theirs_ss,
            "k*P disagrees between this crate and libcrux -- the benchmark \
             below would be comparing two different computations"
        );

        // Warm up both arms before any timing, as the other rows do.
        for _ in 0..N_MUL / 5 + 1 {
            black_box(ours_dh_initiator(black_box(&k)));
            let mut t = [0u8; 64];
            black_box(libcrux_p256::dh_initiator(&mut t, black_box(&k)));
            black_box(&t);
        }
    }

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

        // --- ECDH keygen (fixed base, k*G -> 64 bytes): ours, then libcrux ---
        #[cfg(feature = "libcrux_arm")]
        {
            let mut out = [0u8; 64];
            o_kg = o_kg.min(round(N_MUL, || out = ours_dh_initiator(black_box(&k))));
            black_box(&out);
            let mut lout = [0u8; 64];
            l_kg = l_kg.min(round(N_MUL, || {
                libcrux_p256::dh_initiator(&mut lout, black_box(&k));
            }));
            black_box(&lout);

            // --- ECDH shared secret (variable base, k*P -> 64 bytes) ---
            let mut sout = [0u8; 64];
            o_ss = o_ss.min(round(N_MUL, || {
                sout = ours_dh_responder(black_box(&peer_pk), black_box(&k)).unwrap()
            }));
            black_box(&sout);
            let mut lsout = [0u8; 64];
            l_ss = l_ss.min(round(N_MUL, || {
                libcrux_p256::dh_responder(&mut lsout, black_box(&peer_pk), black_box(&k));
            }));
            black_box(&lsout);
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

    #[cfg(feature = "libcrux_arm")]
    {
        // An ECDH operation is a scalar multiplication plus an inversion; it
        // cannot be cheaper than the bare scalar multiplication floor.
        for (n, m) in [("ours keygen", o_kg), ("libcrux keygen", l_kg),
                       ("ours shared", o_ss), ("libcrux shared", l_ss)] {
            assert_floor(n, m, 5_000.0);
        }
        println!();
        println!("=== vs libcrux (hacl-rs) 0.0.8 — ECDH, bytes in / bytes out ===");
        println!("{:<26} {:>14} {:>14} {:>12}", "operation", "ours (cyc)", "libcrux (cyc)", "ratio");
        println!("{}", "-".repeat(70));
        let lrow = |name: &str, ours: M, theirs: M| {
            println!(
                "{:<26} {:>14.1} {:>14.1} {:>11.2}x",
                name, ours.cyc, theirs.cyc, ours.cyc / theirs.cyc
            );
        };
        lrow("ecdh_keygen  (k*G)", o_kg, l_kg);
        lrow("ecdh_shared  (k*P)", o_ss, l_ss);
        println!();
        println!("Both arms verified to agree byte-for-byte before timing.");
        println!("These two rows include deserialisation, the inversion to affine and");
        println!("serialisation, so they are NOT comparable to the projective rows above.");
        println!("libcrux exposes no add/double/scalar-mul, so this is the finest");
        println!("granularity at which the two can be compared at all.");
        println!("k*G: both use a precomputed generator table (ours 5-bit comb over");
        println!("G_TABLE, constant-time scan; theirs point_mul_g over p256_precomptable).");
        println!("k*P: libcrux's load_point_vartime parses and curve-checks the PUBLIC");
        println!("peer key in variable time; ours checks it with the same field leaves");
        println!("as everything else.  Both scalar multiplications are constant time.");
    }
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
