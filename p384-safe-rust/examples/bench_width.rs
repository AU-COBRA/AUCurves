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
//!   taskset -c 2 cargo run --release --offline -p p384-safe-rust \
//!       --example bench_width

use std::hint::black_box;
use std::time::Instant;

use p384::group::*;

const N_MUL: u64 = 1_000;
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

/// The scalar `examples/bench_compare.rs` uses.
const K_LIMBS: [u64; 6] = [
    0x0123_4567_89ab_cdef,
    0xfedc_ba98_7654_3210,
    0x0f1e_2d3c_4b5a_6978,
    0x1122_3344_5566_7788,
    0x99aa_bbcc_ddee_ff00,
    0x0a1b_2c3d_4e5f_6071,
];

fn main() {
    let g2 = g1_double(&g1_generator());

    // Interleave the two arms so a frequency excursion hits both.
    let mut acc = g2;
    let w1 = bench(N_MUL, || {
        acc = g1_scalar_mul_width1(black_box(&K_LIMBS), black_box(&g2))
    });
    black_box(&acc);

    let mut acc = g2;
    let win = bench(N_MUL, || {
        acc = g1_scalar_mul(black_box(&K_LIMBS), black_box(&g2))
    });
    black_box(&acc);

    let mut acc = g2;
    let w1b = bench(N_MUL, || {
        acc = g1_scalar_mul_width1(black_box(&K_LIMBS), black_box(&g2))
    });
    black_box(&acc);

    let w1 = w1.min(w1b);

    println!("P-384 variable-base scalar multiplication, VAR_W = {VAR_W}");
    println!("  windows {VAR_WINDOWS}, table entries {VAR_TSIZE}");
    println!("  width-1 ladder : {w1:>12.1} ns/op");
    println!("  windowed       : {win:>12.1} ns/op");
    println!("  windowed / width-1 = {:.4}", win / w1);

    // Agreement check, so a mis-set VAR_W cannot produce a fast wrong
    // answer.  The two chains reach the same point through different
    // additions, so the projective triples differ; compare in affine.
    let a = g1_to_affine(&g1_scalar_mul(&K_LIMBS, &g2));
    let b = g1_to_affine(&g1_scalar_mul_width1(&K_LIMBS, &g2));
    match (a, b) {
        (Some((ax, ay)), Some((bx, by))) => {
            assert_eq!((ax.0, ay.0), (bx.0, by.0), "arms disagree")
        }
        (None, None) => {}
        _ => panic!("arms disagree on identity"),
    }
}
