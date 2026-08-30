//! Microbenchmarks for the P-224 field and group operations.
//!
//! Run with:
//!   cargo run --release --example bench -p p224-safe-rust
//!   cargo run --release --example bench -p p224-safe-rust --features extracted
//!
//! ## Measurement notes
//!
//! The primary column is **cycles**; nanoseconds are secondary.  The cycle
//! figure is read with `_rdtsc` fenced by `lfence` on both sides.  This host
//! reports `constant_tsc` + `nonstop_tsc`, so the counter ticks at a fixed
//! reference rate independent of the core's actual frequency.  These are
//! therefore *invariant-TSC reference cycles*, not retired core cycles; a
//! true core-cycle count needs `perf_event_open`, and `perf_event_paranoid`
//! is 4 on this host, so it is unavailable without a root sysctl.  Reference
//! cycles are far more stable than wall-clock nanoseconds when the machine is
//! busy, which it usually is.
//!
//! Every measurement runs in ONE process, INTERLEAVED across `ROUNDS`, and
//! the reported figure per row is the round MINIMUM.  Every error source on a
//! shared machine adds time and none subtracts it, so the minimum is the
//! right summary.
//!
//! Each field loop is a serial dependency chain: iteration `i + 1` consumes
//! the result of iteration `i`, and the *operands* pass through `black_box`.
//! `black_box` on the result alone does NOT stop LLVM hoisting a
//! loop-invariant computation out of the loop; only the operands do.
//! `assert_floor` below fails the run rather than printing a figure that an
//! optimised-away loop would produce.

use p224::group::*;
use p224::{fp_add, fp_inv, fp_mul, fp_square, fp_to_montgomery, Fp, FpRaw};
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

/// Refuse to report a figure that cannot be real.  A number below the floor
/// means the timing loop was optimised away.
fn assert_floor(label: &str, m: M, floor: f64) {
    assert!(
        m.cyc >= floor,
        "{label}: {:.2} cycles/op is below the {floor} cycle floor — the timing \
         loop was optimised away.  Check that the operands are inside black_box \
         and that each iteration consumes the previous result.",
        m.cyc
    );
}

fn to_mont(canon: [u64; 4]) -> Fp {
    let mut out = Fp([0u64; 4]);
    fp_to_montgomery(&mut out, &FpRaw(canon));
    out
}

const ROUNDS: usize = 5;
const N_FIELD: u64 = 2_000_000;
const N_INV: u64 = 20_000;
const N_GROUP: u64 = 200_000;
const N_SMUL: u64 = 200;
const N_SMUL_BASE: u64 = 2_000;

fn main() {
    println!("P-224 (secp224r1) — 4 x u64 Montgomery, R = 2^256");
    #[cfg(feature = "extracted")]
    println!("feature: extracted (Rocq-emitted g1_add compiled in)");
    #[cfg(not(feature = "extracted"))]
    println!("feature: default (hand-written g1_add only)");
    println!();
    println!("cycles are invariant-TSC REFERENCE cycles (constant_tsc + nonstop_tsc),");
    println!("not retired core cycles; read the cycle column, not the ns column.");
    println!("{ROUNDS} interleaved rounds in one process, per-round minimum reported.");
    println!();

    let x = to_mont(P224_GX);
    let y = to_mont(P224_GY);

    let g = g1_generator();
    let g2 = g1_double(&g);

    let k: [u64; 4] = [
        0x0f1e_2d3c_4b5a_6978,
        0x8796_a5b4_c3d2_e1f0,
        0x1a2b_3c4d_5e6f_7081,
        0x0000_0000_02a3_b4c5,
    ];

    #[cfg(feature = "extracted")]
    fn ser(pt: &G1) -> [u8; 96] {
        let mut out = [0u8; 96];
        for (i, w) in pt.x.0.iter().enumerate() {
            out[8 * i..8 * i + 8].copy_from_slice(&w.to_le_bytes());
        }
        for (i, w) in pt.y.0.iter().enumerate() {
            out[32 + 8 * i..32 + 8 * i + 8].copy_from_slice(&w.to_le_bytes());
        }
        for (i, w) in pt.z.0.iter().enumerate() {
            out[64 + 8 * i..64 + 8 * i + 8].copy_from_slice(&w.to_le_bytes());
        }
        out
    }

    // Warm up every body once before any timing.
    {
        let mut o = Fp([0u64; 4]);
        for _ in 0..N_FIELD / 10 {
            fp_mul(&mut o, black_box(&x), black_box(&y));
            fp_add(&mut o, black_box(&x), black_box(&y));
            fp_square(&mut o, black_box(&x));
        }
        for _ in 0..N_INV / 10 {
            fp_inv(&mut o, black_box(&x));
        }
        black_box(&o);
        let mut acc = g2;
        for _ in 0..N_GROUP / 10 {
            acc = g1_add(black_box(&acc), black_box(&g));
            acc = g1_double(black_box(&acc));
        }
        black_box(&acc);
    }

    let (mut m_add, mut m_mul, mut m_sqr, mut m_inv) =
        (M::worst(), M::worst(), M::worst(), M::worst());
    let (mut g_add, mut g_dbl, mut g_add_ga, mut g_dbl_ga) =
        (M::worst(), M::worst(), M::worst(), M::worst());
    let (mut s_mul, mut s_base) = (M::worst(), M::worst());
    #[cfg(feature = "extracted")]
    let (mut e_add, mut e_add_a3, mut e_dbl_a3, mut s_wnaf) =
        (M::worst(), M::worst(), M::worst(), M::worst());

    for _ in 0..ROUNDS {
        // ---------------- field ----------------
        // Serial chains: the accumulator is an operand of the next iteration.
        let mut acc = x;
        let mut o = Fp([0u64; 4]);
        m_add = m_add.min(round(N_FIELD, || {
            fp_add(&mut o, black_box(&acc), black_box(&y));
            acc = o;
        }));
        black_box(&acc);

        let mut acc = x;
        let mut o = Fp([0u64; 4]);
        m_mul = m_mul.min(round(N_FIELD, || {
            fp_mul(&mut o, black_box(&acc), black_box(&y));
            acc = o;
        }));
        black_box(&acc);

        let mut acc = x;
        let mut o = Fp([0u64; 4]);
        m_sqr = m_sqr.min(round(N_FIELD, || {
            fp_square(&mut o, black_box(&acc));
            acc = o;
        }));
        black_box(&acc);

        let mut acc = x;
        let mut o = Fp([0u64; 4]);
        m_inv = m_inv.min(round(N_INV, || {
            fp_inv(&mut o, black_box(&acc));
            // Feed the inverse back in: still a serial chain, and the value
            // stays a non-zero field element throughout.
            acc = o;
            fp_mul(&mut o, black_box(&acc), black_box(&y));
            acc = o;
        }));
        black_box(&acc);

        // ---------------- group ----------------
        let mut acc = g2;
        g_add = g_add.min(round(N_GROUP, || {
            acc = g1_add(black_box(&acc), black_box(&g));
        }));
        black_box(&acc);

        let mut acc = g2;
        g_dbl = g_dbl.min(round(N_GROUP, || {
            acc = g1_double(black_box(&acc));
        }));
        black_box(&acc);

        let mut acc = g2;
        g_add_ga = g_add_ga.min(round(N_GROUP, || {
            acc = g1_add_general_a(black_box(&acc), black_box(&g));
        }));
        black_box(&acc);

        let mut acc = g2;
        g_dbl_ga = g_dbl_ga.min(round(N_GROUP, || {
            acc = g1_double_general_a(black_box(&acc));
        }));
        black_box(&acc);

        let mut acc = g2;
        s_mul = s_mul.min(round(N_SMUL, || {
            acc = g1_scalar_mul(black_box(&k), black_box(&g));
        }));
        black_box(&acc);

        let mut acc = g2;
        s_base = s_base.min(round(N_SMUL_BASE, || {
            acc = g1_scalar_mul_base(black_box(&k));
        }));
        black_box(&acc);

        // ------------- extracted -------------
        #[cfg(feature = "extracted")]
        {
            use p224::g1_a3_extracted::{p224_g1_add_a3_extracted, p224_g1_double_a3_extracted};
            use p224::g1_extracted::p224_g1_add_extracted;

            let mut a = ser(&g2);
            let mut b = ser(&g);
            let mut o = [0u8; 96];
            e_add = e_add.min(round(N_GROUP, || {
                p224_g1_add_extracted(black_box(&mut o), black_box(&mut a), black_box(&mut b));
            }));
            e_add_a3 = e_add_a3.min(round(N_GROUP, || {
                p224_g1_add_a3_extracted(black_box(&mut o), black_box(&mut a), black_box(&mut b));
            }));
            e_dbl_a3 = e_dbl_a3.min(round(N_GROUP, || {
                p224_g1_double_a3_extracted(black_box(&mut o), black_box(&mut a));
            }));
            black_box(&o);

            use p224::wnaf::g1_scalar_mul_wnaf;
            let mut acc = g2;
            s_wnaf = s_wnaf.min(round(N_SMUL, || {
                acc = g1_scalar_mul_wnaf(black_box(&k), black_box(&g));
            }));
            black_box(&acc);
        }
    }

    // A 4x64 Montgomery multiply is 16 mul-class instructions plus the
    // reduction; nothing under ~10 cycles is achievable.
    assert_floor("fp_mul", m_mul, 10.0);
    assert_floor("fp_square", m_sqr, 10.0);
    assert_floor("fp_add", m_add, 2.0);
    assert_floor("fp_inv", m_inv, 100.0);
    // A complete addition is >= 10 field multiplies.
    assert_floor("g1_add", g_add, 40.0);
    assert_floor("g1_double", g_dbl, 40.0);
    // 224 doublings plus additions.
    assert_floor("g1_scalar_mul", s_mul, 5_000.0);

    println!("{:<34} {:>12} {:>12}   iters", "operation", "cycles", "ns");
    println!("{}", "-".repeat(74));
    let row = |name: &str, m: M, iters: u64| {
        println!("{:<34} {:>12.1} {:>12.1}   {}", name, m.cyc, m.ns, iters);
    };
    row("fp_add", m_add, N_FIELD);
    row("fp_mul", m_mul, N_FIELD);
    row("fp_square", m_sqr, N_FIELD);
    row("fp_inv (divstep) + 1 fp_mul", m_inv, N_INV);
    println!();
    row("g1_add", g_add, N_GROUP);
    row("g1_double", g_dbl, N_GROUP);
    row("g1_add (general a)", g_add_ga, N_GROUP);
    row("g1_double (general a)", g_dbl_ga, N_GROUP);
    row("g1_scalar_mul (224-bit)", s_mul, N_SMUL);
    row("g1_scalar_mul_base (224-bit)", s_base, N_SMUL_BASE);
    println!(
        "    (fixed-base table: W={}, {} windows x {} entries = {} bytes of .rodata)",
        BASE_W, BASE_WINDOWS, BASE_TSIZE, BASE_TABLE_BYTES
    );

    #[cfg(feature = "extracted")]
    {
        println!();
        row("g1_add (extracted)", e_add, N_GROUP);
        row("g1_add (extracted, a=-3)", e_add_a3, N_GROUP);
        row("g1_double (extracted, a=-3)", e_dbl_a3, N_GROUP);
        row("g1_scalar_mul wNAF (extr)", s_wnaf, N_SMUL);
        println!();
        println!("  a=-3 extracted vs hand-written:");
        println!("    add    {:.3}x   double {:.3}x",
                 g_add.cyc / e_add_a3.cyc, g_dbl.cyc / e_dbl_a3.cyc);
        println!("  wNAF (VARIABLE TIME) vs constant-time window: {:.3}x",
                 s_mul.cyc / s_wnaf.cyc);
    }

    println!();
    println!("fp_inv / fp_mul = {:.1}x", (m_inv.cyc - m_mul.cyc) / m_mul.cyc);
}
