//! Side-by-side BN254 pairing benchmark: us vs arkworks, same machine.
//!
//! Measures Fp multiplication and the full optimal-ate pairing on the
//! BN254 generator pair. Run pinned to one core for stability:
//!   taskset -c 2 cargo run --release --example bench_compare

use std::time::Instant;

fn main() {
    let n_mul = 1_000_000;
    let n_pair = 200;

    println!("=== bn254-safe-rust (this work, pure-Rust stub leaves) ===");
    {
        use bn254::*;
        let p_x = Fp([3010205953636678181, 16660003904792317819,
                      9416043620196899128, 1701617664632108776]);
        let p_y = Fp([10743797247944923858, 1573659247316127088,
                      11424947345088411797, 553131571301810253]);
        let q_x = Fp2 {
            c0: Fp([12044280144466466770, 1183395637354907828,
                    13029987837960057068, 2156018249977681552]),
            c1: Fp([12476014551097379519, 1869321500543886820,
                    1144664739908881049, 1547066415325078580]),
        };
        let q_y = Fp2 {
            c0: Fp([10920762005193907700, 8867974930247989672,
                    13830807366020128571, 2032937451700869816]),
            c1: Fp([1660519944620902552, 8400000128929148196,
                    13225706902731049404, 491829149345229816]),
        };

        // Warm up
        let mut out = Fp12::zero();
        pairing(&mut out, &p_x, &p_y, &q_x, &q_y);

        let a = p_x; let b = p_y;
        let mut c = Fp::zero();
        let t = Instant::now();
        for _ in 0..n_mul { fp_mul(&mut c, &a, &b); }
        let mul_ns = t.elapsed().as_nanos() as f64 / n_mul as f64;
        println!("  Fp mul:  {:.1} ns", mul_ns);

        let t = Instant::now();
        for _ in 0..n_pair { pairing(&mut out, &p_x, &p_y, &q_x, &q_y); }
        let pair_us = t.elapsed().as_micros() as f64 / n_pair as f64;
        println!("  Pairing: {:.0} us  ({:.2} ms)", pair_us, pair_us / 1000.0);
    }

    println!();
    println!("=== arkworks ark-bn254 0.5 (production Rust, unverified) ===");
    {
        use ark_bn254::{Bn254, Fq, G1Affine, G2Affine};
        use ark_ec::pairing::Pairing;
        use ark_ec::AffineRepr;
        use ark_ff::{Field, UniformRand};
        use ark_std::rand::SeedableRng;

        let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(0xdead);
        let a: Fq = Fq::rand(&mut rng);
        let b: Fq = Fq::rand(&mut rng);

        // Defeat constant folding inside the loop.
        let a_p: *const Fq = &a;
        let b_p: *const Fq = &b;

        let t = Instant::now();
        let mut acc = Fq::ONE;
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

        let t = Instant::now();
        let mut acc = None;
        for _ in 0..n_pair {
            acc = Some(Bn254::pairing(p, q));
        }
        std::hint::black_box(acc);
        let pair_us = t.elapsed().as_micros() as f64 / n_pair as f64;
        println!("  Pairing: {:.0} us  ({:.2} ms)", pair_us, pair_us / 1000.0);
    }
}
