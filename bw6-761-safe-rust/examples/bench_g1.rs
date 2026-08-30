//! BW6-761 G1 group-operation benchmark: affine (one field inversion
//! per group operation) against homogeneous projective RCB, and inside
//! the projective chain, the dedicated doubling (Algorithm 9) against
//! the complete addition applied to a repeated argument (Algorithm 7).
//!
//!   cargo run --release --example bench_g1
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
//! Every arm runs in ONE process and all arms are INTERLEAVED round by
//! round; per row the round MINIMUM is reported.  A load spike therefore
//! hits every arm, and the minimum discards the rounds it hit.  This matters
//! on this machine: a single loaded wall-clock run once inverted the
//! `fp_mul` / `fp_square` ordering here.
//!
//! Each field loop is a serial dependency chain — iteration `i + 1` consumes
//! the result of iteration `i` — with the *operands* inside `black_box`.
//! `black_box` on the result alone does NOT stop LLVM hoisting a
//! loop-invariant computation out of the loop.

use std::hint::black_box;
use std::time::Instant;

use bw6_761::g1_double_a0_extracted::g1_proj_double_extracted;
use bw6_761::group::*;
use bw6_761::tower::{self, bw6_761_inv, bw6_761_mul, bw6_761_square, Fp};

// BW6-761 G1 generator, Montgomery limbs (same constants as src/kat.rs).
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

fn round<F: FnMut()>(iters: u32, mut f: F) -> M {
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

const ROUNDS: usize = 5;
const N_FP: u32 = 100_000;
const N_INV: u32 = 3_000;
const N_PROJ: u32 = 30_000;
const N_AFF: u32 = 3_000;
const N_SMUL_PROJ: u32 = 30;
const N_SMUL_AFF: u32 = 10;

fn main() {
    let g = G1Aff::pt(tower::Fp(G1_GEN_X), tower::Fp(G1_GEN_Y));
    let gp = g1_to_proj(&g);
    let gp2 = g1_proj_double_extracted(&gp);
    let g_dbl = g1_double(&g);
    let b3 = g1_three_b();
    let x = tower::Fp(G1_GEN_X);

    let mut k = [0u8; 48];
    for (i, byte) in k.iter_mut().enumerate() {
        *byte = (0x9du8).wrapping_mul(i as u8 + 1) | 1;
    }
    k[0] &= 0x1f;

    println!("BW6-761 (761-bit p, 12 x u64) G1 — one process, {ROUNDS} interleaved rounds,");
    println!("per-row minimum.  Cycles are invariant-TSC REFERENCE cycles");
    println!("(constant_tsc + nonstop_tsc), not retired core cycles; read the cycle");
    println!("column, not the ns column.\n");

    // Warm-up: every body once, before any timing.
    {
        let mut o = Fp::zero();
        for _ in 0..N_FP / 10 {
            bw6_761_mul(&mut o, black_box(&x), black_box(&x));
            bw6_761_square(&mut o, black_box(&x));
        }
        for _ in 0..N_INV / 10 {
            bw6_761_inv(&mut o, black_box(&x));
        }
        black_box(&o);
        for _ in 0..N_PROJ / 10 {
            black_box(g1_proj_double_extracted(black_box(&gp)));
            black_box(g1_proj_add(black_box(&gp), black_box(&gp), &b3));
        }
        for _ in 0..N_AFF / 10 {
            black_box(g1_double(black_box(&g)));
            black_box(g1_add(black_box(&g), black_box(&g_dbl)));
        }
    }

    let (mut t_mul, mut t_sq, mut t_inv) = (M::worst(), M::worst(), M::worst());
    let (mut d_aff, mut d_a7, mut d_a9) = (M::worst(), M::worst(), M::worst());
    let (mut a_aff, mut a_prj) = (M::worst(), M::worst());
    let (mut s_aff, mut s_prj, mut s_prj_selfadd) = (M::worst(), M::worst(), M::worst());

    for _ in 0..ROUNDS {
        // ---------------- field leaves ----------------
        // Serial chains: the accumulator is an operand of the next iteration.
        let mut acc = x;
        let mut o = Fp::zero();
        t_mul = t_mul.min(round(N_FP, || {
            bw6_761_mul(&mut o, black_box(&acc), black_box(&x));
            acc = o;
        }));
        black_box(&acc);

        let mut acc = x;
        let mut o = Fp::zero();
        t_sq = t_sq.min(round(N_FP, || {
            bw6_761_square(&mut o, black_box(&acc));
            acc = o;
        }));
        black_box(&acc);

        let mut acc = x;
        let mut o = Fp::zero();
        t_inv = t_inv.min(round(N_INV, || {
            bw6_761_inv(&mut o, black_box(&acc));
            acc = o;
        }));
        black_box(&acc);

        // ---------------- doubling ----------------
        d_aff = d_aff.min(round(N_AFF, || {
            black_box(g1_double(black_box(&g)));
        }));
        d_a7 = d_a7.min(round(N_PROJ, || {
            black_box(g1_proj_add(black_box(&gp), black_box(&gp), &b3));
        }));
        d_a9 = d_a9.min(round(N_PROJ, || {
            black_box(g1_proj_double_extracted(black_box(&gp)));
        }));

        // ---------------- addition ----------------
        a_aff = a_aff.min(round(N_AFF, || {
            black_box(g1_add(black_box(&g), black_box(&g_dbl)));
        }));
        a_prj = a_prj.min(round(N_PROJ, || {
            black_box(g1_proj_add(black_box(&gp), black_box(&gp2), &b3));
        }));

        // ---------------- scalar multiplication ----------------
        s_aff = s_aff.min(round(N_SMUL_AFF, || {
            black_box(g1_scalar_mul_affine(black_box(&k), black_box(&g)));
        }));
        s_prj = s_prj.min(round(N_SMUL_PROJ, || {
            black_box(g1_scalar_mul(black_box(&k), black_box(&g)));
        }));
        // Projective chain with the dedicated doubling replaced by the
        // complete addition applied twice to the same point: isolates the
        // Algorithm 9 contribution from the affine -> projective one.
        s_prj_selfadd = s_prj_selfadd.min(round(N_SMUL_PROJ, || {
            let pp = g1_to_proj(black_box(&g));
            let mut acc = g1_proj_inf();
            for &byte in k.iter() {
                for i in 0..8 {
                    let bit = (byte >> (7 - i)) & 1;
                    acc = g1_proj_add(&acc, &acc, &b3);
                    if bit == 1 {
                        acc = g1_proj_add(&acc, &pp, &b3);
                    }
                }
            }
            black_box(g1_from_proj(&acc));
        }));
    }

    // A 12x64 Montgomery multiply is >= 144 mul-class instructions plus the
    // reduction; nothing under ~100 cycles is achievable.
    assert_floor("fp_mul", t_mul, 100.0);
    assert_floor("fp_square", t_sq, 100.0);
    assert_floor("fp_inv", t_inv, 2_000.0);
    // A projective group operation is >= 9 such multiplies.
    assert_floor("Alg 9 doubling", d_a9, 500.0);
    assert_floor("Alg 7 addition", a_prj, 500.0);
    // 377-bit scalar multiplication is >= 377 doublings.
    assert_floor("projective scalar mul", s_prj, 100_000.0);

    let row = |name: &str, m: M| {
        println!("{name:<44} {:>12.1} {:>12.1}", m.cyc, m.ns);
    };
    println!("{:<44} {:>12} {:>12}", "field leaves", "cycles", "ns");
    println!("{}", "-".repeat(70));
    row("fp_mul", t_mul);
    row("fp_square", t_sq);
    row("fp_inv  (Bernstein-Yang divstep)", t_inv);
    println!("\n  fp_inv / fp_mul   = {:.1}x", t_inv.cyc / t_mul.cyc);
    println!("  fp_square / fp_mul = {:.3}x\n", t_sq.cyc / t_mul.cyc);

    println!("{:<44} {:>12} {:>12}", "G1 point doubling", "cycles", "ns");
    println!("{}", "-".repeat(70));
    row("affine    lambda = 3x^2/2y  (1 inversion)", d_aff);
    row("projective Alg 7 self-add   (33 ops, 14 M)", d_a7);
    row("projective Alg 9 emitted    (18 ops,  9 M)", d_a9);
    println!("\n  Alg 9 vs Alg 7 self-add : {:+.1}%  ({:.3}x)",
             100.0 * (d_a9.cyc / d_a7.cyc - 1.0), d_a7.cyc / d_a9.cyc);
    println!("  Alg 9 vs affine         : {:.1}x faster\n", d_aff.cyc / d_a9.cyc);

    println!("{:<44} {:>12} {:>12}", "G1 point addition", "cycles", "ns");
    println!("{}", "-".repeat(70));
    row("affine    chord            (1 inversion)", a_aff);
    row("projective Alg 7           (33 ops, 14 M)", a_prj);
    println!("\n  Alg 7 vs affine : {:.1}x faster\n", a_aff.cyc / a_prj.cyc);

    println!("{:<44} {:>12} {:>12}",
             "G1 scalar mul, 377-bit scalar (48 bytes)", "cycles", "ns");
    println!("{}", "-".repeat(70));
    row("affine     (~565 inversions)", s_aff);
    row("projective (1 inversion, Alg 7 + Alg 9)", s_prj);
    row("projective, Alg 7 self-add for doubling", s_prj_selfadd);

    println!();
    println!("  projective vs affine                      : {:.1}x faster",
             s_aff.cyc / s_prj.cyc);
    println!("  Alg 9 vs Alg 7 self-add, within projective : {:+.1}%",
             100.0 * (s_prj.cyc / s_prj_selfadd.cyc - 1.0));

    // Sanity: all three agree.
    assert_eq!(g1_scalar_mul(&k, &g), g1_scalar_mul_affine(&k, &g));
    println!("\n  (results cross-checked against the affine chain)");
}
