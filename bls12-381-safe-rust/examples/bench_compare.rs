//! Side-by-side BLS12-381 pairing benchmark: us vs blst vs arkworks, same machine.
//!
//! Run pinned to one core for stability:
//!   taskset -c 2 cargo run --release --example bench_compare
//!
//! Every Fp-multiply timing loop below is a serial latency chain — the output
//! of iteration i is an operand of iteration i+1, with `black_box` on the
//! operands — so no arm can have its multiply hoisted out of its loop.
//! Cycles are reported alongside ns because ns is distorted by background
//! load and by frequency scaling.

use std::hint::black_box;
use std::time::Instant;

#[inline(always)]
fn rdtsc() -> u64 {
    #[cfg(target_arch = "x86_64")]
    unsafe { core::arch::x86_64::_rdtsc() }
    #[cfg(not(target_arch = "x86_64"))]
    { 0 }
}

fn report_mul(ns: f64, cycles: f64, label: &str) {
    println!("  {label} {ns:.1} ns  ({cycles:.0} cyc)");
}

fn main() {
    let n_mul = 1_000_000;
    let n_pair = 100;

    // Leaf provenance for the arm below:
    //   mul, square      CryptOpt assembly, SMT-validated against fiat-crypto
    //                    (generated/bls12_*_cryptopt.asm)
    //   add, sub, opp,   hand-written Rust CIOS in src/stubs.rs
    //   copy, select,
    //   from_word
    //   inv              hand-written Rust Bernstein-Yang divstep
    //                    (safegcd-rs), NOT extracted from Rocq; see
    //                    HAND_WRITTEN_AUDIT.md.  `--features fermat_inv`
    //                    swaps in the x^(p-2) ladder instead (~2x slower
    //                    pairing).
    //   tower, Miller    generated from the Qed'd bedrock2 programs
    //   loop, final exp  (generated/bls12_safe_tower.rs)
    println!("=== bls12-381-safe-rust (this work) ===");
    println!("    leaves: CryptOpt asm mul/square; Rust stubs add/sub/copy/select;");
    println!("    safegcd (hand-written Rust, not Rocq-extracted) Fp inversion;");
    println!("    tower + affine Miller loop + final exp from the bedrock2 extraction");
    {
        use bls12_381::*;
        let p_x = Fp([6679831729115696150, 8653662730902241269, 1535610680227111361,
                      17342916647841752903, 17135755455211762752, 1297449291367578485]);
        let p_y = Fp([13451288730302620273, 10097742279870053774, 15949884091978425806,
                      5885175747529691540, 1016841820992199104, 845620083434234474]);
        let q_x = Fp2 {
            c0: Fp([17722385409647053328, 12967546844987299354, 11648722842835150208,
                    10994581490347323113, 8027586497049998955, 396758299565931735]),
            c1: Fp([11937283898719073798, 12295044263989567683, 4301357764460312582,
                    1953074377943790439, 14030662337566180679, 1266120665323335155]),
        };
        let q_y = Fp2 {
            c0: Fp([5508758831087832138, 6448303779119275098, 16710190169160573786,
                    13542242618704742751, 563980702369916322, 37152010398653157]),
            c1: Fp([12520284671833321565, 1777275927576994268, 9704602344324656032,
                    8739618045342622522, 16651875250601773805, 804950956836789234]),
        };

        let mut out = Fp12::zero();
        pairing(&mut out, &p_x, &p_y, &q_x, &q_y);

        // Serial latency chain: x <- x * p_y.
        let mut x = p_x;
        let mut c = Fp::zero();
        let c0 = rdtsc();
        let t = Instant::now();
        for _ in 0..n_mul { fp_mul(&mut c, black_box(&x), black_box(&p_y)); x = c; }
        let mul_ns = t.elapsed().as_nanos() as f64 / n_mul as f64;
        let mul_cyc = (rdtsc() - c0) as f64 / n_mul as f64;
        black_box(&x);
        report_mul(mul_ns, mul_cyc, "Fp mul:");

        let t = Instant::now();
        for _ in 0..n_pair { pairing(&mut out, &p_x, &p_y, &q_x, &q_y); }
        let pair_us = t.elapsed().as_micros() as f64 / n_pair as f64;
        println!("  Pairing: {:.0} us  ({:.2} ms)", pair_us, pair_us / 1000.0);
    }

    println!();
    println!("=== blst 0.3 (production C+asm, hand-optimised) ===");
    {
        use blst::*;
        let mut p1 = blst_p1::default();
        let mut q1 = blst_p2::default();
        unsafe {
            blst_p1_from_affine(&mut p1, blst_p1_generator() as *const _);
            blst_p2_from_affine(&mut q1, blst_p2_generator() as *const _);
        }
        let mut p_aff = blst_p1_affine::default();
        let mut q_aff = blst_p2_affine::default();
        unsafe {
            blst_p1_to_affine(&mut p_aff, &p1);
            blst_p2_to_affine(&mut q_aff, &q1);
        }

        // Serial latency chain: a <- a * b.
        let mut a = blst_fp { l: [1, 2, 3, 4, 5, 6] };
        let b = blst_fp { l: [7, 8, 9, 10, 11, 12] };
        let mut c = blst_fp::default();
        let c0 = rdtsc();
        let t = Instant::now();
        for _ in 0..n_mul {
            unsafe { blst_fp_mul(&mut c, black_box(&a), black_box(&b)); }
            a = c;
        }
        let mul_ns = t.elapsed().as_nanos() as f64 / n_mul as f64;
        let mul_cyc = (rdtsc() - c0) as f64 / n_mul as f64;
        black_box(&a);
        report_mul(mul_ns, mul_cyc, "Fp mul:");

        let mut out = blst_fp12::default();
        let t = Instant::now();
        for _ in 0..n_pair {
            unsafe { blst_miller_loop(&mut out, &q_aff, &p_aff); blst_final_exp(&mut out, &out); }
        }
        let pair_us = t.elapsed().as_micros() as f64 / n_pair as f64;
        println!("  Pairing: {:.0} us  ({:.2} ms)", pair_us, pair_us / 1000.0);
    }

    println!();
    println!("=== arkworks ark-bls12-381 0.5 (production Rust, unverified) ===");
    {
        use ark_bls12_381::{Bls12_381, Fq, G1Affine, G2Affine};
        use ark_ec::pairing::Pairing;
        use ark_ec::AffineRepr;
        use ark_ff::UniformRand;
        use ark_std::rand::SeedableRng;

        let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(0xdead);
        let mut acc: Fq = Fq::rand(&mut rng);
        let b: Fq = Fq::rand(&mut rng);
        // Serial latency chain: acc <- acc * b, operands through black_box so
        // the multiply cannot be hoisted out of the loop.
        let c0 = rdtsc();
        let t = Instant::now();
        for _ in 0..n_mul {
            acc = *black_box(&acc) * *black_box(&b);
        }
        let mul_ns = t.elapsed().as_nanos() as f64 / n_mul as f64;
        let mul_cyc = (rdtsc() - c0) as f64 / n_mul as f64;
        black_box(acc);
        report_mul(mul_ns, mul_cyc, "Fq mul:");

        let p = G1Affine::generator();
        let q = G2Affine::generator();
        let mut acc = None;
        let t = Instant::now();
        for _ in 0..n_pair { acc = Some(Bls12_381::pairing(p, q)); }
        std::hint::black_box(acc);
        let pair_us = t.elapsed().as_micros() as f64 / n_pair as f64;
        println!("  Pairing: {:.0} us  ({:.2} ms)", pair_us, pair_us / 1000.0);
    }
}
