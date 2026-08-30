//! What fraction of the BN254 Miller loop is `fp2_inv`?
//!
//!   cargo run --release --example bench_inv_cost
//!
//! The affine Miller loop does one `fp2_inv` per doubling/addition step
//! (~70 doublings + ~10 additions for BN254 with loop parameter 6u+2).  If
//! `fp2_inv` dominates, switching to projective is worth the refactor cost;
//! if it does not, the gap is elsewhere.
//!
//! It does not dominate.  With `_bn254_inv` as the Fermat ladder over the
//! local Rust `mont_mul`, `fp2_inv` cost ~20 us and was 57-68% of the Miller
//! loop.  Against safegcd it costs a small fraction of that.  Read the
//! "projective ceiling" printed below with that in mind: it is computed from
//! the measured inversion cost, and the affine loop already runs faster than
//! the ceiling the 20 us figure produced.  See `HAND_WRITTEN_AUDIT.md`,
//! `_bn254_inv`.
//!
//! ## Measurement notes
//!
//! The primary column is **cycles**; nanoseconds are secondary.  Cycles come
//! from `_rdtsc` fenced by `lfence` on both sides.  This host reports
//! `constant_tsc` + `nonstop_tsc`, so the counter ticks at a fixed reference
//! rate independent of the core's actual frequency.  These are *invariant-TSC
//! reference cycles*, not retired core cycles; a true core-cycle count needs
//! `perf_event_open`, and `perf_event_paranoid` is 4 on this host, so it is
//! unavailable without a root sysctl.
//!
//! The share printed at the bottom is a ratio of two measurements, so the two
//! must be measured under the same conditions or the share is meaningless.
//! Both run in ONE process, INTERLEAVED round by round, and each reports its
//! round MINIMUM.  A load spike therefore hits both, and the minimum discards
//! the rounds it hit.  Before this file was converted, `fp2_inv` and the
//! Miller loop were each timed once, in sequence, and their quotient was
//! taken across two differently-loaded intervals.
//!
//! The `fp2_inv` loop is a serial dependency chain: the inverse of iteration
//! `i` is the input of iteration `i + 1`, with the operand inside
//! `black_box`.  (`fp2_inv` is an involution, so the input alternates between
//! `x` and `x^-1`; both are non-zero and cost the same.)
use bn254::*;
use std::hint::black_box;
use std::time::Instant;

const ROUNDS: usize = 5;
const N_INV: u64 = 20_000;
const N_MILLER: u64 = 30;

/// The affine BN254 Miller loop: ~70 doubling steps plus ~10 addition steps,
/// one `fp2_inv` each.
const MILLER_STEPS: f64 = 70.0 + 10.0;

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
         loop was optimised away.  Check that the operand is inside black_box \
         and that each iteration consumes the previous result.",
        m.cyc
    );
}

fn main() {
    // A non-trivial Fp2 to invert repeatedly.
    let a = Fp([0x7a17caa950ad28d7, 0x1f6ac17ae15521b9, 0x334bea4e696bd284, 0x2a1f6744ce179d8e]);
    let b = Fp([0xe4b1c5ae034e46ca, 0x9cdb2d3b64716da7, 0x47d8eb76d8dd067e, 0x15d0085520f5bbc3]);
    let x = Fp2 { c0: a, c1: b };

    let p_x = Fp([0xd35d438dc58f0d9d, 0x0a78eb28f5c70b3d, 0x666ea36f7879462c, 0x0e0a77c19a07df2f]);
    let p_y = Fp([0xa6ba871b8b1e1b3a, 0x14f1d651eb8e167b, 0xccdd46def0f28c58, 0x1c14ef83340fbe5e]);
    let q_x = Fp2 { c0: Fp([0x8e83b5d102bc2026,0xdceb1935497b0172,0xfbb8264797811adf,0x19573841af96503b]),
                    c1: Fp([0xafb4737da84c6140,0x6043dd5a5802d8c4,0x09e950fc52a02f86,0x14fef0833aea7b6b]) };
    let q_y = Fp2 { c0: Fp([0x619dfa9d886be9f6,0xfe7fd297f59e9b78,0xff9e1a62231b7dfe,0x28fd7eebae9e4206]),
                    c1: Fp([0x64095b56c71856ee,0xdc57f922327d3cbb,0x55f935be33351076,0x0da4a0e693fd6482]) };
    let mut out12 = Fp12::zero();

    // Warm-up, both bodies.
    {
        let mut o = Fp2::zero();
        for _ in 0..N_INV / 10 {
            fp2_inv(&mut o, black_box(&x));
        }
        black_box(&o);
        for _ in 0..3 {
            miller_loop(&mut out12, &p_x, &p_y, &q_x, &q_y);
        }
    }

    let (mut m_inv, mut m_miller) = (M::worst(), M::worst());
    for _ in 0..ROUNDS {
        // Serial chain: the inverse feeds the next inversion.
        let mut acc = x;
        let mut o = Fp2::zero();
        m_inv = m_inv.min(round(N_INV, || {
            fp2_inv(&mut o, black_box(&acc));
            acc = o;
        }));
        black_box(&acc);

        m_miller = m_miller.min(round(N_MILLER, || {
            miller_loop(black_box(&mut out12), black_box(&p_x), black_box(&p_y),
                        black_box(&q_x), black_box(&q_y));
        }));
    }

    // An Fp2 inversion is a norm (2 squarings), an Fp inversion and 2
    // multiplies; the Fp inversion alone is hundreds of cycles.
    assert_floor("fp2_inv", m_inv, 200.0);
    assert_floor("miller_loop", m_miller, 100_000.0);

    println!("BN254 affine Miller loop: the fp2_inv share");
    println!();
    println!("cycles are invariant-TSC REFERENCE cycles (constant_tsc + nonstop_tsc),");
    println!("not retired core cycles.  Both rows measured in one process,");
    println!("{ROUNDS} interleaved rounds, per-row minimum.");
    println!();
    println!("{:<34} {:>12} {:>12}   iters", "", "cycles", "ns");
    println!("{}", "-".repeat(74));
    println!("{:<34} {:>12.1} {:>12.1}   {}", "fp2_inv", m_inv.cyc, m_inv.ns, N_INV);
    println!("{:<34} {:>12.0} {:>12.0}   {}", "miller_loop", m_miller.cyc, m_miller.ns,
             N_MILLER);

    let inv_budget_cyc = MILLER_STEPS * m_inv.cyc;
    let inv_budget_ns = MILLER_STEPS * m_inv.ns;
    println!("{:<34} {:>12.0} {:>12.0}   ({:.0} steps x fp2_inv)",
             "fp2_inv budget per Miller loop", inv_budget_cyc, inv_budget_ns,
             MILLER_STEPS);

    println!();
    println!("fp2_inv share of the Miller loop: {:.1}%  ({:.0} of {:.0} cycles)",
             100.0 * inv_budget_cyc / m_miller.cyc, inv_budget_cyc, m_miller.cyc);
    println!("Projective ceiling (all fp2_invs removed, nothing else changed): {:.0} cycles \
              ({:.1} us)",
             m_miller.cyc - inv_budget_cyc,
             (m_miller.ns - inv_budget_ns) / 1000.0);
    println!();
    println!("The ceiling is an upper bound on what removing the inversions could buy,");
    println!("and it assumes the projective formulas add nothing, which they do.");
}
