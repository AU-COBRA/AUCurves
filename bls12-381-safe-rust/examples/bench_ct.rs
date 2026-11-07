//! Constant-time vs variable-time scalar multiplication vs blst (G1 and G2).
//!
//!   cargo run --release --example bench_ct [REPS]
//!
//! * ct: `group::g1_scalar_mul_ct` / `g2_scalar_mul_ct` (bedrock2
//!   `g1_scalar_mul_ct` / `g2_scalar_mul_ct`: double, unconditional add,
//!   `ct_cswap` on every bit);
//! * variable time: `group::g1_scalar_mul` / `g2_scalar_mul` (branch on the bit);
//! * blst: `blst_p1_mult` / `blst_p2_mult` (256-bit scalar).
//! Random 256-bit scalar and point, operands through `black_box`; each
//! measurement repeated REPS times (default 7), median and minimum printed.

use std::hint::black_box;
use std::time::Instant;

use blst::*;
use bls12_381::group::*;
use bls12_381::{Fp, Fp2};

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

fn measure<F: FnMut()>(reps: usize, iters: usize, mut f: F) -> (f64, f64) {
    f();
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

fn fp2_of(x: &blst_fp2) -> Fp2 { Fp2 { c0: Fp(x.fp[0].l), c1: Fp(x.fp[1].l) } }

fn main() {
    let reps: usize = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(7);
    let mut rng = Rng(77);
    println!("reps = {}", reps);
    let (k1, k2) = (rng.scalar(), rng.scalar());

    // G1
    let (mut bp1, mut a1) = (blst_p1::default(), blst_p1_affine::default());
    unsafe {
        blst_p1_mult(&mut bp1, blst_p1_generator(), le_bytes(&k1).as_ptr(), 256);
        blst_p1_to_affine(&mut a1, &bp1);
    }
    let p1 = G1Projective::from_affine(&G1Affine { x: Fp(a1.x.l), y: Fp(a1.y.l) });
    let k = rng.scalar();
    println!("G1 k*P:");
    row("ct g1_scalar_mul_ct (PROVED, constant time)", measure(reps, 20, || {
        let mut r = G1Projective::identity();
        g1_scalar_mul_ct(&mut r, black_box(&k), black_box(&p1));
        black_box(r);
    }));
    row("variable time g1_scalar_mul (PROVED)", measure(reps, 20, || {
        let mut r = G1Projective::identity();
        g1_scalar_mul(&mut r, black_box(&k), black_box(&p1));
        black_box(r);
    }));
    row("blst_p1_mult", measure(reps, 20, || {
        let mut r = blst_p1::default();
        unsafe { blst_p1_mult(&mut r, black_box(&bp1), le_bytes(black_box(&k)).as_ptr(), 256) };
        black_box(r);
    }));

    // G2
    let (mut bp2, mut a2) = (blst_p2::default(), blst_p2_affine::default());
    unsafe {
        blst_p2_mult(&mut bp2, blst_p2_generator(), le_bytes(&k2).as_ptr(), 256);
        blst_p2_to_affine(&mut a2, &bp2);
    }
    let p2 = G2Projective::from_affine(&G2Affine { x: fp2_of(&a2.x), y: fp2_of(&a2.y) });
    println!("G2 k*P:");
    row("ct g2_scalar_mul_ct (PROVED, constant time)", measure(reps, 10, || {
        let mut r = G2Projective::identity();
        g2_scalar_mul_ct(&mut r, black_box(&k), black_box(&p2));
        black_box(r);
    }));
    row("variable time g2_scalar_mul (PROVED)", measure(reps, 10, || {
        let mut r = G2Projective::identity();
        g2_scalar_mul(&mut r, black_box(&k), black_box(&p2));
        black_box(r);
    }));
    row("blst_p2_mult", measure(reps, 10, || {
        let mut r = blst_p2::default();
        unsafe { blst_p2_mult(&mut r, black_box(&bp2), le_bytes(black_box(&k)).as_ptr(), 256) };
        black_box(r);
    }));
}
