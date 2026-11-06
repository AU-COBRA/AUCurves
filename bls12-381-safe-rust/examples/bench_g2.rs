//! G2 group law and scalar multiplication: Rocq-emitted vs hand-written vs blst.
//!
//!   cargo run --release --example bench_g2 [REPS]
//!
//! * emitted: `group::g2_add` / `g2_double` (bedrock2 `g2_curve_add` /
//!   `g2_curve_double`, RCB 2015 Alg. 7 / 9 over Fp2, homogeneous), and the
//!   scalar multiplications `group::g2_scalar_mul` and `g2_scalar_mul_loop`.
//!   Each call of `g2_add` / `g2_double` includes the copy of the operands
//!   into a fresh `Mem` and of the result out of it.
//! * hand-written: `group::handwritten::g2j_*` (Jacobian EFD add-2007-bl /
//!   dbl-2009-l, double-and-add), the previous G2 code of the crate.
//! * blst: `blst_p2_add_or_double`, `blst_p2_double`, `blst_p2_mult`.
//!
//! Operands go through `black_box`; each measurement is repeated REPS times
//! (default 5) and the median and the minimum are printed.

use std::hint::black_box;
use std::time::Instant;

use blst::*;
use bls12_381::group::*;
use bls12_381::group::handwritten::*;
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
    println!("  {:<48} median {}   min {}", label, fmt(med), fmt(min));
}

fn fp2_of(x: &blst_fp2) -> Fp2 { Fp2 { c0: Fp(x.fp[0].l), c1: Fp(x.fp[1].l) } }

fn point(k: &[u64; 4]) -> (blst_p2, G2Affine) {
    let (mut p, mut a) = (blst_p2::default(), blst_p2_affine::default());
    unsafe {
        blst_p2_mult(&mut p, blst_p2_generator(), le_bytes(k).as_ptr(), 256);
        blst_p2_to_affine(&mut a, &p);
    }
    (p, G2Affine { x: fp2_of(&a.x), y: fp2_of(&a.y) })
}

fn main() {
    let reps: usize = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(5);
    let mut rng = Rng(2026);
    println!("reps = {}", reps);
    let (bp, pa) = point(&rng.scalar());
    let (bq, qa) = point(&rng.scalar());
    let (p, q) = (G2Projective::from_affine(&pa), G2Projective::from_affine(&qa));
    let (pj, qj) = (G2Jacobian::from_affine(&pa), G2Jacobian::from_affine(&qa));

    println!("G2 addition P + Q:");
    row("emitted g2_add (incl. Mem copy in/out)", measure(reps, 2000, || {
        let mut r = G2Projective::identity();
        g2_add(&mut r, black_box(&p), black_box(&q));
        black_box(r);
    }));
    row("hand-written Jacobian g2j_add", measure(reps, 2000, || {
        let mut r = G2Jacobian::identity();
        g2j_add(&mut r, black_box(&pj), black_box(&qj));
        black_box(r);
    }));
    row("blst_p2_add_or_double", measure(reps, 2000, || {
        let mut r = blst_p2::default();
        unsafe { blst_p2_add_or_double(&mut r, black_box(&bp), black_box(&bq)) };
        black_box(r);
    }));

    println!("G2 doubling 2P:");
    row("emitted g2_double (incl. Mem copy in/out)", measure(reps, 2000, || {
        let mut r = G2Projective::identity();
        g2_double(&mut r, black_box(&p));
        black_box(r);
    }));
    row("hand-written Jacobian g2j_double", measure(reps, 2000, || {
        let mut r = G2Jacobian::identity();
        g2j_double(&mut r, black_box(&pj));
        black_box(r);
    }));
    row("blst_p2_double", measure(reps, 2000, || {
        let mut r = blst_p2::default();
        unsafe { blst_p2_double(&mut r, black_box(&bp)) };
        black_box(r);
    }));

    println!("G2 scalar multiplication (256-bit scalar):");
    let k = rng.scalar();
    row("g2_scalar_mul", measure(reps, 20, || {
        let mut r = G2Projective::identity();
        g2_scalar_mul(&mut r, black_box(&k), black_box(&p));
        black_box(r);
    }));
    row("g2_scalar_mul_loop (hand loop, emitted add/dbl)", measure(reps, 20, || {
        let mut r = G2Projective::identity();
        g2_scalar_mul_loop(&mut r, black_box(&k), black_box(&p));
        black_box(r);
    }));
    row("hand-written Jacobian g2j_scalar_mul", measure(reps, 20, || {
        let mut r = G2Jacobian::identity();
        g2j_scalar_mul(&mut r, black_box(&k), black_box(&pj));
        black_box(r);
    }));
    row("blst_p2_mult", measure(reps, 20, || {
        let mut r = blst_p2::default();
        unsafe { blst_p2_mult(&mut r, black_box(&bp), le_bytes(black_box(&k)).as_ptr(), 256) };
        black_box(r);
    }));
}
