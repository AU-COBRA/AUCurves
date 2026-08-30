//! BW6-761 G1: the Rocq-EMITTED RCB Algorithm 9 doubling against the
//! hand-written one and against `g1_proj_add(P, P)`.
//!
//!   cargo run --release --example bench_double_a0
//!
//! All arms run in ONE process and are INTERLEAVED across rounds, and
//! the reported figure per arm is the round MINIMUM.  Absolute ns on
//! this machine drift badly under background load; the minimum over
//! interleaved rounds and the ratios between arms are stable, so the
//! ratios lead.  Cycles come from `_rdtsc` with `lfence` on both
//! sides (the pattern of `bn254-safe-rust/examples/bench_vs_production.rs`).

use std::hint::black_box;
use std::time::Instant;

use bw6_761::g1_double_a0_extracted::g1_proj_double_extracted;
use bw6_761::group::*;
use bw6_761::tower;

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

/// BENCHMARK BASELINE ONLY — the hand transcription of
/// `rcb_double_a0_gallina` that this crate shipped as
/// `group::g1_proj_double` before the emitted body replaced it.  It is
/// carried here (and, as a test oracle, in `src/kat.rs`) so that the
/// comparison the removal rests on stays runnable; the library itself
/// does not contain it.
fn g1_proj_double_handwritten(p: &G1Proj, b3: &tower::Fp) -> G1Proj {
    use tower::{bw6_761_add as fp_add_t, bw6_761_mul as fp_mul_t,
                bw6_761_sub as fp_sub_t, Fp as TFp};
    let (x, y, z) = (p.x, p.y, p.z);
    let mut u = TFp::zero();
    let mut t0 = TFp::zero(); fp_mul_t(&mut t0, &y, &y);     // 1
    let mut z3 = TFp::zero(); fp_add_t(&mut z3, &t0, &t0);   // 2
    fp_add_t(&mut u, &z3, &z3); z3 = u;                      // 3
    fp_add_t(&mut u, &z3, &z3); z3 = u;                      // 4
    let mut t1 = TFp::zero(); fp_mul_t(&mut t1, &y, &z);     // 5
    let mut t2 = TFp::zero(); fp_mul_t(&mut t2, &z, &z);     // 6
    fp_mul_t(&mut u, b3, &t2); t2 = u;                       // 7
    let mut x3 = TFp::zero(); fp_mul_t(&mut x3, &t2, &z3);   // 8
    let mut y3 = TFp::zero(); fp_add_t(&mut y3, &t0, &t2);   // 9
    fp_mul_t(&mut u, &t1, &z3); z3 = u;                      // 10
    fp_add_t(&mut u, &t2, &t2); t1 = u;                      // 11
    fp_add_t(&mut u, &t1, &t2); t2 = u;                      // 12
    fp_sub_t(&mut u, &t0, &t2); t0 = u;                      // 13
    fp_mul_t(&mut u, &t0, &y3); y3 = u;                      // 14
    fp_add_t(&mut u, &x3, &y3); y3 = u;                      // 15
    fp_mul_t(&mut u, &x, &y); t1 = u;                        // 16
    fp_mul_t(&mut u, &t0, &t1); x3 = u;                      // 17
    fp_add_t(&mut u, &x3, &x3); x3 = u;                      // 18
    G1Proj { x: x3, y: y3, z: z3 }
}

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
        if o.cyc < self.cyc { o } else { self }
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

fn main() {
    let g = G1Aff::pt(tower::Fp(G1_GEN_X), tower::Fp(G1_GEN_Y));
    let gp = g1_to_proj(&g);
    let b3 = g1_three_b();

    // Correctness gate before any timing: the two bodies must agree as
    // projective triples, or the numbers below mean nothing.
    assert_eq!(g1_proj_double_extracted(&gp), g1_proj_double_handwritten(&gp, &b3));
    let mut q = gp;
    for _ in 0..8 {
        assert_eq!(g1_proj_double_extracted(&q), g1_proj_double_handwritten(&q, &b3));
        q = g1_proj_double_handwritten(&q, &b3);
    }

    const ITERS: u32 = 100_000;
    const ROUNDS: u32 = 9;

    // Warm-up.
    for _ in 0..ITERS / 5 {
        black_box(g1_proj_double_extracted(black_box(&gp)));
        black_box(g1_proj_double_handwritten(black_box(&gp), &b3));
        black_box(g1_proj_add(black_box(&gp), black_box(&gp), &b3));
    }

    let (mut emit, mut hand, mut selfadd) = (M::worst(), M::worst(), M::worst());
    for _ in 0..ROUNDS {
        emit = emit.min(round(ITERS, || {
            black_box(g1_proj_double_extracted(black_box(&gp)));
        }));
        hand = hand.min(round(ITERS, || {
            black_box(g1_proj_double_handwritten(black_box(&gp), &b3));
        }));
        selfadd = selfadd.min(round(ITERS, || {
            black_box(g1_proj_add(black_box(&gp), black_box(&gp), &b3));
        }));
    }

    println!("BW6-761 G1 complete doubling — one process, {ROUNDS} interleaved rounds");
    println!("of {ITERS} iterations each, per-round minimum reported.\n");
    println!("  emitted Alg 9  vs  hand-written Alg 9 : {:.3}x  ({:+.1}%)",
             hand.cyc / emit.cyc, 100.0 * (emit.cyc / hand.cyc - 1.0));
    println!("  emitted Alg 9  vs  Alg 7 self-add     : {:.3}x  ({:+.1}%)",
             selfadd.cyc / emit.cyc, 100.0 * (emit.cyc / selfadd.cyc - 1.0));
    println!("  hand-written   vs  Alg 7 self-add     : {:.3}x  ({:+.1}%)\n",
             selfadd.cyc / hand.cyc, 100.0 * (hand.cyc / selfadd.cyc - 1.0));

    println!("  {:<40} {:>10} {:>12}", "", "cycles", "ns");
    for (n, m) in [
        ("Alg 9, Rocq-emitted (18 ops,  9 M)", emit),
        ("Alg 9, hand-written (18 ops,  9 M)", hand),
        ("Alg 7 self-add      (33 ops, 14 M)", selfadd),
    ] {
        println!("  {n:<40} {:>10.1} {:>12.1}", m.cyc, m.ns);
    }

    // Scalar-multiplication level: the doubling is ~377 of the ~565
    // group operations, so a per-doubling delta shows up diluted here.
    let mut k = [0u8; 48];
    for (i, byte) in k.iter_mut().enumerate() {
        *byte = (0x9du8).wrapping_mul(i as u8 + 1) | 1;
    }
    k[0] &= 0x1f;

    let smul = |dbl: fn(&G1Proj, &TFpAlias) -> G1Proj, b3: &TFpAlias| {
        let pp = g1_to_proj(&g);
        let mut acc = g1_proj_inf();
        for &byte in k.iter() {
            for i in 0..8 {
                let bit = (byte >> (7 - i)) & 1;
                acc = dbl(&acc, b3);
                if bit == 1 {
                    acc = g1_proj_add(&acc, &pp, b3);
                }
            }
        }
        g1_from_proj(&acc)
    };
    fn dbl_hand(p: &G1Proj, b3: &TFpAlias) -> G1Proj { g1_proj_double_handwritten(p, b3) }
    fn dbl_emit(p: &G1Proj, _b3: &TFpAlias) -> G1Proj { g1_proj_double_extracted(p) }

    assert_eq!(smul(dbl_emit, &b3), smul(dbl_hand, &b3));

    const SITERS: u32 = 200;
    let (mut se, mut sh) = (M::worst(), M::worst());
    for _ in 0..5 {
        se = se.min(round(SITERS, || { black_box(smul(dbl_emit, black_box(&b3))); }));
        sh = sh.min(round(SITERS, || { black_box(smul(dbl_hand, black_box(&b3))); }));
    }
    println!("\n377-bit scalar multiplication (double-and-add, 1 inversion)\n");
    println!("  emitted doubling vs hand-written : {:.3}x  ({:+.1}%)\n",
             sh.cyc / se.cyc, 100.0 * (se.cyc / sh.cyc - 1.0));
    println!("  {:<40} {:>10} {:>12}", "", "cycles", "ns");
    println!("  {:<40} {:>10.0} {:>12.0}", "scalar mul, emitted doubling", se.cyc, se.ns);
    println!("  {:<40} {:>10.0} {:>12.0}", "scalar mul, hand-written doubling", sh.cyc, sh.ns);
}

type TFpAlias = tower::Fp;
