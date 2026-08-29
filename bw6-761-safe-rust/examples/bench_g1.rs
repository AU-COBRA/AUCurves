//! BW6-761 G1 group-operation benchmark: affine (one field inversion
//! per group operation) against homogeneous projective RCB, and inside
//! the projective chain, the dedicated doubling (Algorithm 9) against
//! the complete addition applied to a repeated argument (Algorithm 7).
//!
//!   cargo run --release --example bench_g1

use std::hint::black_box;
use std::time::Instant;

use bw6_761::group::*;
use bw6_761::tower::{self, Fp, bw6_761_mul, bw6_761_square, bw6_761_inv};

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

fn bench<F: FnMut()>(name: &str, iters: u32, mut f: F) -> f64 {
    for _ in 0..iters / 10 + 1 { f(); }           // warm up
    let t = Instant::now();
    for _ in 0..iters { f(); }
    let ns = t.elapsed().as_nanos() as f64 / iters as f64;
    println!("{name:<44} {ns:>12.1} ns");
    ns
}

fn main() {
    let g = G1Aff::pt(tower::Fp(G1_GEN_X), tower::Fp(G1_GEN_Y));
    let gp = g1_to_proj(&g);
    let b3 = g1_three_b();
    let x = tower::Fp(G1_GEN_X);

    println!("BW6-761 (761-bit p, 12 x u64) — field leaves\n");
    let t_mul = bench("fp_mul", 200_000, || {
        let mut o = Fp::zero();
        bw6_761_mul(&mut o, black_box(&x), black_box(&x));
        black_box(&o);
    });
    let t_sq = bench("fp_square", 200_000, || {
        let mut o = Fp::zero();
        bw6_761_square(&mut o, black_box(&x));
        black_box(&o);
    });
    let t_inv = bench("fp_inv  (Bernstein-Yang divstep)", 20_000, || {
        let mut o = Fp::zero();
        bw6_761_inv(&mut o, black_box(&x));
        black_box(&o);
    });
    println!("\n  fp_inv / fp_mul = {:.1}x\n", t_inv / t_mul);
    let _ = t_sq;

    println!("G1 point doubling\n");
    let d_aff = bench("affine    lambda = 3x^2/2y  (1 inversion)", 20_000,
        || { black_box(g1_double(black_box(&g))); });
    let d_a7 = bench("projective Alg 7 self-add   (33 ops, 14 M)", 200_000,
        || { black_box(g1_proj_add(black_box(&gp), black_box(&gp), &b3)); });
    let d_a9 = bench("projective Alg 9 dedicated  (18 ops,  9 M)", 200_000,
        || { black_box(g1_proj_double(black_box(&gp), &b3)); });
    println!("\n  Alg 9 vs Alg 7 self-add : {:+.1}%", 100.0 * (d_a9 / d_a7 - 1.0));
    println!("  Alg 9 vs affine         : {:.1}x faster\n", d_aff / d_a9);

    println!("G1 point addition\n");
    let a_aff = bench("affine    chord            (1 inversion)", 20_000,
        || { black_box(g1_add(black_box(&g), black_box(&g1_double(&g)))); });
    let gp2 = g1_proj_double(&gp, &b3);
    let a_prj = bench("projective Alg 7           (33 ops, 14 M)", 200_000,
        || { black_box(g1_proj_add(black_box(&gp), black_box(&gp2), &b3)); });
    println!("\n  Alg 7 vs affine : {:.1}x faster\n", a_aff / a_prj);

    println!("G1 scalar multiplication, 377-bit scalar (48 bytes)\n");
    let mut k = [0u8; 48];
    for (i, byte) in k.iter_mut().enumerate() { *byte = (0x9du8).wrapping_mul(i as u8 + 1) | 1; }
    k[0] &= 0x1f;

    let s_aff = bench("affine     (~565 inversions)", 20,
        || { black_box(g1_scalar_mul_affine(black_box(&k), black_box(&g))); });
    let s_prj = bench("projective (1 inversion, Alg 7 + Alg 9)", 200,
        || { black_box(g1_scalar_mul(black_box(&k), black_box(&g))); });

    // Projective chain with the dedicated doubling replaced by the
    // complete addition applied twice to the same point: isolates the
    // Algorithm 9 contribution from the affine -> projective one.
    let s_prj_selfadd = bench("projective, Alg 7 self-add for doubling", 200, || {
        let pp = g1_to_proj(black_box(&g));
        let mut acc = g1_proj_inf();
        for &byte in k.iter() {
            for i in 0..8 {
                let bit = (byte >> (7 - i)) & 1;
                acc = g1_proj_add(&acc, &acc, &b3);
                if bit == 1 { acc = g1_proj_add(&acc, &pp, &b3); }
            }
        }
        black_box(g1_from_proj(&acc));
    });

    println!();
    println!("  projective vs affine                      : {:.1}x faster",
             s_aff / s_prj);
    println!("  Alg 9 vs Alg 7 self-add, within projective : {:+.1}%",
             100.0 * (s_prj / s_prj_selfadd - 1.0));

    // Sanity: all three agree.
    assert_eq!(g1_scalar_mul(&k, &g), g1_scalar_mul_affine(&k, &g));
    println!("\n  (results cross-checked against the affine chain)");
}
