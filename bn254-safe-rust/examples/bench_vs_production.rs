//! Benchmark our bn254-safe-rust (extracted from verified bedrock2) against
//! arkworks-rs/ark-bn254 (production Rust implementation).
//!
//! Run with:
//!   cargo run --release --example bench_vs_production
//!
//! Requires `ark-bn254` + `ark-ec` + `ark-ff` in [dev-dependencies].
use bn254::*;
use std::time::Instant;

// Arkworks imports
use ark_bn254::{Bn254, Fr as ArkFr, G1Projective, G2Projective};
use ark_ec::{pairing::Pairing, PrimeGroup};
use ark_ff::UniformRand;

const N_PAIRING: usize = 100;
const N_FP_MUL: usize = 1_000_000;

fn bench_ours() -> (f64, f64) {
    let p_x = Fp([0xd35d438dc58f0d9d, 0x0a78eb28f5c70b3d, 0x666ea36f7879462c, 0x0e0a77c19a07df2f]);
    let p_y = Fp([0xa6ba871b8b1e1b3a, 0x14f1d651eb8e167b, 0xccdd46def0f28c58, 0x1c14ef83340fbe5e]);
    let q_x = Fp2 {
        c0: Fp([0x8e83b5d102bc2026, 0xdceb1935497b0172, 0xfbb8264797811adf, 0x19573841af96503b]),
        c1: Fp([0xafb4737da84c6140, 0x6043dd5a5802d8c4, 0x09e950fc52a02f86, 0x14fef0833aea7b6b]),
    };
    let q_y = Fp2 {
        c0: Fp([0x619dfa9d886be9f6, 0xfe7fd297f59e9b78, 0xff9e1a62231b7dfe, 0x28fd7eebae9e4206]),
        c1: Fp([0x64095b56c71856ee, 0xdc57f922327d3cbb, 0x55f935be33351076, 0x0da4a0e693fd6482]),
    };

    // Warmup
    let mut out = Fp12::zero();
    pairing(&mut out, &p_x, &p_y, &q_x, &q_y);

    let a = Fp([0x7a17caa950ad28d7, 0x1f6ac17ae15521b9, 0x334bea4e696bd284, 0x2a1f6744ce179d8e]);
    let b = Fp([0xe4b1c5ae034e46ca, 0x9cdb2d3b64716da7, 0x47d8eb76d8dd067e, 0x15d0085520f5bbc3]);
    let mut c = Fp::zero();

    let start = Instant::now();
    for _ in 0..N_FP_MUL { fp_mul(&mut c, &a, &b); }
    let fp_mul_ns = start.elapsed().as_nanos() as f64 / N_FP_MUL as f64;

    let start = Instant::now();
    for _ in 0..N_PAIRING { pairing(&mut out, &p_x, &p_y, &q_x, &q_y); }
    let pairing_us = start.elapsed().as_micros() as f64 / N_PAIRING as f64;

    (fp_mul_ns, pairing_us)
}

fn bench_arkworks() -> (f64, f64) {
    let mut rng = ark_std::test_rng();
    let p = G1Projective::generator();
    let q = G2Projective::generator();

    // Warmup
    let _ = Bn254::pairing(p, q);

    // Fp mul (ark_bn254::Fq)
    use ark_bn254::Fq;
    let a = Fq::rand(&mut rng);
    let b = Fq::rand(&mut rng);

    let start = Instant::now();
    for _ in 0..N_FP_MUL {
        let _ = std::hint::black_box(a * b);
    }
    let fp_mul_ns = start.elapsed().as_nanos() as f64 / N_FP_MUL as f64;

    let start = Instant::now();
    for _ in 0..N_PAIRING {
        let _ = std::hint::black_box(Bn254::pairing(p, q));
    }
    let pairing_us = start.elapsed().as_micros() as f64 / N_PAIRING as f64;

    (fp_mul_ns, pairing_us)
}

fn main() {
    println!("BN254 benchmark: our extraction vs. arkworks\n");
    println!("{:<24} {:>14} {:>14} {:>12}", "op", "ours", "arkworks", "ratio");
    println!("{:-<66}", "");

    let (ours_mul, ours_pair) = bench_ours();
    let (ark_mul, ark_pair) = bench_arkworks();

    println!("{:<24} {:>11.1} ns {:>11.1} ns {:>11.2}x",
             "Fp mul", ours_mul, ark_mul, ours_mul / ark_mul);
    println!("{:<24} {:>11.1} us {:>11.1} us {:>11.2}x",
             "Pairing (full)", ours_pair, ark_pair, ours_pair / ark_pair);
    println!("\n(ratio = how many times slower ours is vs. arkworks)");
}
