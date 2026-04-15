//! Per-stage breakdown: where does the 4.87x BN254 gap come from?
//!
//! Compares each tower level (Fp, Fp2, Fp12) and pairing stages
//! (Miller, final exp) against arkworks. Helps pinpoint whether the
//! gap is concentrated in the base field, the Fp12 layer, or pairing
//! plumbing.
use bn254::*;
use std::time::Instant;

use ark_bn254::{Bn254, Fq, Fq2, Fq12, G1Affine, G2Affine, G1Projective, G2Projective};
use ark_ec::{pairing::Pairing, bn::G2Prepared, PrimeGroup};
use ark_ff::{UniformRand, Field};

const N: usize = 100_000;
const N_PAIR: usize = 100;

fn time_ns<F: FnMut()>(mut f: F, n: usize) -> f64 {
    let start = Instant::now();
    for _ in 0..n { f(); }
    start.elapsed().as_nanos() as f64 / n as f64
}

fn time_us<F: FnMut()>(mut f: F, n: usize) -> f64 {
    let start = Instant::now();
    for _ in 0..n { f(); }
    start.elapsed().as_micros() as f64 / n as f64
}

fn main() {
    println!("BN254 per-stage benchmark: ours vs ark-bn254\n");
    println!("{:<28} {:>14} {:>14} {:>10}", "operation", "ours", "arkworks", "ratio");
    println!("{:-<70}", "");

    // ---- Setup: ours ----
    let p_x = Fp([0xd35d438dc58f0d9d, 0x0a78eb28f5c70b3d, 0x666ea36f7879462c, 0x0e0a77c19a07df2f]);
    let p_y = Fp([0xa6ba871b8b1e1b3a, 0x14f1d651eb8e167b, 0xccdd46def0f28c58, 0x1c14ef83340fbe5e]);
    let q_x = Fp2 { c0: Fp([0x8e83b5d102bc2026,0xdceb1935497b0172,0xfbb8264797811adf,0x19573841af96503b]),
                    c1: Fp([0xafb4737da84c6140,0x6043dd5a5802d8c4,0x09e950fc52a02f86,0x14fef0833aea7b6b]) };
    let q_y = Fp2 { c0: Fp([0x619dfa9d886be9f6,0xfe7fd297f59e9b78,0xff9e1a62231b7dfe,0x28fd7eebae9e4206]),
                    c1: Fp([0x64095b56c71856ee,0xdc57f922327d3cbb,0x55f935be33351076,0x0da4a0e693fd6482]) };

    let a = Fp([0x7a17caa950ad28d7, 0x1f6ac17ae15521b9, 0x334bea4e696bd284, 0x2a1f6744ce179d8e]);
    let b = Fp([0xe4b1c5ae034e46ca, 0x9cdb2d3b64716da7, 0x47d8eb76d8dd067e, 0x15d0085520f5bbc3]);
    let mut c = Fp::zero();

    let a2 = Fp2 { c0: a, c1: b };
    let b2 = Fp2 { c0: b, c1: a };
    let mut c2 = Fp2::zero();

    let mut a12 = Fp12::zero();
    pairing(&mut a12, &p_x, &p_y, &q_x, &q_y);
    let mut b12 = Fp12::zero();
    pairing(&mut b12, &p_x, &p_y, &q_x, &q_y);
    let mut c12 = Fp12::zero();

    let mut out_pair = Fp12::zero();
    pairing(&mut out_pair, &p_x, &p_y, &q_x, &q_y); // warmup

    // ---- Setup: ark ----
    let mut rng = ark_std::test_rng();
    let pa = G1Projective::generator();
    let qa = G2Projective::generator();
    let pa_aff: G1Affine = pa.into();
    let qa_aff: G2Affine = qa.into();
    let qa_prep: G2Prepared<ark_bn254::Config> = qa_aff.into();
    let _ = Bn254::pairing(pa, qa); // warmup
    let aa = Fq::rand(&mut rng);
    let bb = Fq::rand(&mut rng);
    let aa2 = Fq2::rand(&mut rng);
    let bb2 = Fq2::rand(&mut rng);
    let mut aa12 = Fq12::rand(&mut rng);
    let bb12 = Fq12::rand(&mut rng);

    // Use std::ptr::read_volatile to defeat constant folding.
    let read = |x: &Fq| unsafe { std::ptr::read_volatile(x) };
    let read2 = |x: &Fq2| unsafe { std::ptr::read_volatile(x) };
    let read12 = |x: &Fq12| unsafe { std::ptr::read_volatile(x) };

    // ---- Fp mul ----
    let ours = time_ns(|| fp_mul(&mut c, &a, &b), N);
    let ark = time_ns(|| { let _ = std::hint::black_box(read(&aa) * read(&bb)); }, N);
    println!("{:<28} {:>11.1} ns {:>11.1} ns {:>9.2}x", "Fp mul", ours, ark, ours/ark);

    // ---- Fp square ----
    let ours = time_ns(|| fp_square(&mut c, &a), N);
    let ark = time_ns(|| { let _ = std::hint::black_box(read(&aa).square()); }, N);
    println!("{:<28} {:>11.1} ns {:>11.1} ns {:>9.2}x", "Fp sqr", ours, ark, ours/ark);

    // ---- Fp2 mul ----
    let ours = time_ns(|| fp2_mul(&mut c2, &a2, &b2), N);
    let ark = time_ns(|| { let _ = std::hint::black_box(read2(&aa2) * read2(&bb2)); }, N);
    println!("{:<28} {:>11.1} ns {:>11.1} ns {:>9.2}x", "Fp2 mul", ours, ark, ours/ark);

    // ---- Fp12 mul ----
    let ours = time_ns(|| fp12_mul(&mut c12, &a12, &b12), 10_000);
    let ark = time_ns(|| { let _ = std::hint::black_box(read12(&aa12) * read12(&bb12)); }, 10_000);
    println!("{:<28} {:>11.1} ns {:>11.1} ns {:>9.2}x", "Fp12 mul", ours, ark, ours/ark);

    // ---- Fp12 sqr ----
    let ours = time_ns(|| fp12_square(&mut c12, &a12), 10_000);
    let ark = time_ns(|| { let _ = std::hint::black_box(read12(&aa12).square()); }, 10_000);
    println!("{:<28} {:>11.1} ns {:>11.1} ns {:>9.2}x", "Fp12 sqr", ours, ark, ours/ark);

    // ---- Miller loop ----
    let ours = time_us(|| miller_loop(&mut out_pair, &p_x, &p_y, &q_x, &q_y), N_PAIR);
    let ark = time_us(|| { let _ = std::hint::black_box(Bn254::multi_miller_loop([pa_aff], [qa_prep.clone()])); }, N_PAIR);
    println!("{:<28} {:>11.1} us {:>11.1} us {:>9.2}x", "Miller loop", ours, ark, ours/ark);

    // ---- Full pairing ----
    let ours = time_us(|| pairing(&mut out_pair, &p_x, &p_y, &q_x, &q_y), N_PAIR);
    let ark = time_us(|| { let _ = std::hint::black_box(Bn254::pairing(pa, qa)); }, N_PAIR);
    println!("{:<28} {:>11.1} us {:>11.1} us {:>9.2}x", "Pairing (full)", ours, ark, ours/ark);

    println!("\nratio = ours / arkworks (higher = our gap)");
    println!("read_volatile defeats constant folding.");
}
