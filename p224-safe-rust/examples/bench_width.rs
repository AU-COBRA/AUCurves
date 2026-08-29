//! Window-width measurement for the variable-base constant-time scalar
//! multiplication.
//!
//! Both arms run in ONE process, interleaved, and the width-1 ladder
//! `g1_scalar_mul_width1` is timed alongside as a fixed reference so
//! separate builds can be compared through their ratios rather than
//! their absolute numbers (this machine carries background load, which
//! moves absolutes but not ratios).
//!
//! To compare window widths, set `group::VAR_W` to 4, run, set it to 5,
//! run again, and compare the `windowed / width-1` column.
//!
//!   taskset -c 2 cargo run --release --offline -p p224-safe-rust \
//!       --example bench_width

use std::hint::black_box;
use std::time::Instant;

use p224::group::*;

const N_MUL: u64 = 2_000;
const REPS: usize = 7;

/// Warm up, then time `iters` calls `REPS` times and return the smallest
/// ns/op observed: every source of error on a shared machine adds time.
fn bench<F: FnMut()>(iters: u64, mut f: F) -> f64 {
    for _ in 0..(iters / 10 + 1) {
        f();
    }
    let mut best = f64::INFINITY;
    for _ in 0..REPS {
        let start = Instant::now();
        for _ in 0..iters {
            f();
        }
        let t = start.elapsed().as_nanos() as f64 / iters as f64;
        if t < best {
            best = t;
        }
    }
    best
}

/// The scalar `examples/bench.rs` uses.
const K: [u64; 4] = [
    0x0f1e_2d3c_4b5a_6978,
    0x8796_a5b4_c3d2_e1f0,
    0x1a2b_3c4d_5e6f_7081,
    0x0000_0000_02a3_b4c5,
];

fn main() {
    let g = g1_generator();

    // Interleave the two arms so a frequency excursion hits both.
    let mut acc = g;
    let w1 = bench(N_MUL, || {
        acc = g1_scalar_mul_width1(black_box(&K), black_box(&g))
    });
    black_box(&acc);

    let mut acc = g;
    let win = bench(N_MUL, || acc = g1_scalar_mul(black_box(&K), black_box(&g)));
    black_box(&acc);

    let mut acc = g;
    let w1b = bench(N_MUL, || {
        acc = g1_scalar_mul_width1(black_box(&K), black_box(&g))
    });
    black_box(&acc);

    let w1 = w1.min(w1b);

    println!("P-224 variable-base scalar multiplication, VAR_W = {VAR_W}");
    println!("  windows {VAR_WINDOWS}, table entries {VAR_TSIZE}");
    println!("  width-1 ladder : {w1:>12.1} ns/op");
    println!("  windowed       : {win:>12.1} ns/op");
    println!("  windowed / width-1 = {:.4}", win / w1);

    // Agreement check, so a mis-set VAR_W cannot produce a fast wrong
    // answer.  The two chains reach the same point through different
    // additions, so the projective triples differ; compare in affine.
    let a = g1_to_affine(&g1_scalar_mul(&K, &g));
    let b = g1_to_affine(&g1_scalar_mul_width1(&K, &g));
    match (a, b) {
        (Some((ax, ay)), Some((bx, by))) => assert_eq!((ax, ay), (bx, by), "arms disagree"),
        (None, None) => {}
        _ => panic!("arms disagree on identity"),
    }
}
