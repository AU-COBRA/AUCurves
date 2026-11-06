//! G1 scalar multiplication and MSM: hand-written vs Rocq-emitted vs blst.
//!
//!   cargo run --release --example bench_group [REPS]
//!
//! * hand-written: `group::handwritten` (Jacobian EFD formulas, double-and-add;
//!   for MSM a naive Σ of scalar multiplications — there is no hand-written
//!   Pippenger in the crate).
//! * emitted: `group::g1_scalar_mul` (emitted bedrock2 double-and-add),
//!   `group::g1_scalar_mul_loop` (hand-written loop over the emitted complete
//!   add/double) and `group::g1_msm` (emitted bedrock2 Pippenger).
//! * blst: `blst_p1_mult` and `p1_affines::mult` (Pippenger).
//!
//! Operands go through `black_box`; each measurement is repeated REPS times
//! (default 5) and the median and the minimum are printed.

use std::hint::black_box;
use std::time::Instant;

use blst::*;
use bls12_381::group::*;
use bls12_381::group::handwritten::*;

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }
    fn scalar(&mut self) -> [u64; 4] { [self.next(), self.next(), self.next(), self.next()] }
}

fn le_bytes(k: &[u64; 4]) -> [u8; 32] {
    let mut b = [0u8; 32];
    for (i, w) in k.iter().enumerate() {
        b[8 * i..8 * i + 8].copy_from_slice(&w.to_le_bytes());
    }
    b
}

/// Median and minimum seconds per call of `f` over `reps` repetitions of
/// `iters` calls.
fn measure<F: FnMut()>(reps: usize, iters: usize, mut f: F) -> (f64, f64) {
    f(); // warm-up
    let mut v: Vec<f64> = (0..reps)
        .map(|_| {
            let t = Instant::now();
            for _ in 0..iters { f(); }
            t.elapsed().as_secs_f64() / iters as f64
        })
        .collect();
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    (v[v.len() / 2], v[0])
}

fn fmt(s: f64) -> String {
    if s < 1e-3 { format!("{:9.2} us", s * 1e6) } else { format!("{:9.3} ms", s * 1e3) }
}

fn row(label: &str, (med, min): (f64, f64)) {
    println!("  {:<44} median {}   min {}", label, fmt(med), fmt(min));
}

fn main() {
    let reps: usize = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(5);
    let mut rng = Rng(2026);
    println!("reps = {}", reps);

    // ---- scalar multiplication ----
    println!("G1 scalar multiplication (256-bit scalar):");
    let k = rng.scalar();
    let g_aff = g1_generator();
    let g_proj = G1Projective::from_affine(&g_aff);
    let g_jac = G1Jacobian::from_affine(&g_aff);
    row("hand-written (Jacobian, double-and-add)", measure(reps, 50, || {
        let mut r = G1Jacobian::identity();
        g1j_scalar_mul(&mut r, black_box(&k), black_box(&g_jac));
        black_box(r);
    }));
    row("emitted add/double (hand-written loop)", measure(reps, 50, || {
        let mut r = G1Projective::identity();
        g1_scalar_mul_loop(&mut r, black_box(&k), black_box(&g_proj));
        black_box(r);
    }));
    row("emitted g1_scalar_mul (proved bedrock2)", measure(reps, 50, || {
        let mut r = G1Projective::identity();
        g1_scalar_mul(&mut r, black_box(&k), black_box(&g_proj));
        black_box(r);
    }));
    row("emitted MSM with n = 1", measure(reps, 5, || {
        let mut r = G1Projective::identity();
        g1_msm(&mut r, black_box(&[g_proj]), black_box(&[k]));
        black_box(r);
    }));
    let kb = le_bytes(&k);
    row("blst_p1_mult", measure(reps, 200, || {
        let mut p = blst_p1::default();
        unsafe { blst_p1_mult(&mut p, blst_p1_generator(), black_box(kb.as_ptr()), 256) };
        black_box(p);
    }));

    // ---- MSM ----
    for &n in &[16usize, 256, 4096] {
        println!("G1 MSM, n = {}:", n);
        let blst_pts: Vec<blst_p1> = (0..n)
            .map(|_| {
                let mut p = blst_p1::default();
                unsafe { blst_p1_mult(&mut p, blst_p1_generator(), le_bytes(&rng.scalar()).as_ptr(), 256) };
                p
            })
            .collect();
        let scalars: Vec<[u64; 4]> = (0..n).map(|_| rng.scalar()).collect();
        let affs: Vec<G1Affine> = blst_pts
            .iter()
            .map(|p| {
                let mut a = blst_p1_affine::default();
                unsafe { blst_p1_to_affine(&mut a, p) };
                G1Affine { x: bls12_381::Fp(a.x.l), y: bls12_381::Fp(a.y.l) }
            })
            .collect();
        let projs: Vec<G1Projective> = affs.iter().map(G1Projective::from_affine).collect();
        let jacs: Vec<G1Jacobian> = affs.iter().map(G1Jacobian::from_affine).collect();
        let iters = if n >= 4096 { 1 } else if n >= 256 { 2 } else { 10 };

        row("hand-written naive Σ kᵢPᵢ (Jacobian)", measure(reps, iters, || {
            let mut acc = G1Jacobian::identity();
            for (p, k) in black_box(&jacs).iter().zip(black_box(&scalars)) {
                let mut t = G1Jacobian::identity();
                g1j_scalar_mul(&mut t, k, p);
                let a = acc;
                g1j_add(&mut acc, &a, &t);
            }
            black_box(acc);
        }));
        row("emitted Pippenger g1_msm (c = 9)", measure(reps, iters, || {
            let mut r = G1Projective::identity();
            g1_msm(&mut r, black_box(&projs), black_box(&scalars));
            black_box(r);
        }));
        let ps = p1_affines::from(&blst_pts);
        let sb: Vec<u8> = scalars.iter().flat_map(le_bytes).collect();
        row("blst p1_affines::mult (Pippenger)", measure(reps, iters * 10, || {
            black_box(black_box(&ps).mult(black_box(&sb), 256));
        }));
    }
}
