//! Side-by-side BLS12-381 pairing benchmark: us vs blst vs arkworks, same machine.
//!
//! Run pinned to one core for stability:
//!   taskset -c 2 cargo run --release --example bench_compare

use std::time::Instant;

fn main() {
    let n_mul = 1_000_000;
    let n_pair = 100;

    println!("=== bls12-381-safe-rust (this work, CryptOpt mul + stub other leaves) ===");
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

        let mut c = Fp::zero();
        let t = Instant::now();
        for _ in 0..n_mul { fp_mul(&mut c, &p_x, &p_y); }
        let mul_ns = t.elapsed().as_nanos() as f64 / n_mul as f64;
        println!("  Fp mul:  {:.1} ns", mul_ns);

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

        let a = blst_fp { l: [1, 2, 3, 4, 5, 6] };
        let b = blst_fp { l: [7, 8, 9, 10, 11, 12] };
        let mut c = blst_fp::default();
        let t = Instant::now();
        for _ in 0..n_mul { unsafe { blst_fp_mul(&mut c, &a, &b); } }
        let mul_ns = t.elapsed().as_nanos() as f64 / n_mul as f64;
        println!("  Fp mul:  {:.1} ns", mul_ns);

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
        use ark_ff::{Field, UniformRand};
        use ark_std::rand::SeedableRng;

        let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(0xdead);
        let a: Fq = Fq::rand(&mut rng);
        let b: Fq = Fq::rand(&mut rng);
        let a_p: *const Fq = &a;
        let b_p: *const Fq = &b;
        let mut acc = Fq::ONE;
        let t = Instant::now();
        for _ in 0..n_mul {
            let av = unsafe { std::ptr::read_volatile(a_p) };
            let bv = unsafe { std::ptr::read_volatile(b_p) };
            acc = av * bv;
        }
        std::hint::black_box(acc);
        let mul_ns = t.elapsed().as_nanos() as f64 / n_mul as f64;
        println!("  Fq mul:  {:.1} ns", mul_ns);

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
