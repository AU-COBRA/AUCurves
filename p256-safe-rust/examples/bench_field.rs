//! P-256 FIELD-layer benchmark: fiat-crypto `p256_64` (this crate) against
//! the hand-written 4x64 Montgomery backend of RustCrypto `p256` 0.13.2
//! (`p256/src/arithmetic/field/field64.rs`), same machine, same iteration
//! counts, same `black_box` discipline.
//!
//! Run pinned to one core:
//!   taskset -c 2 cargo run --release --offline -p p256-safe-rust --example bench_field
//!
//! Two regimes are reported for every operation.
//!
//! * LATENCY -- a single dependency chain `x = op(x, c)`.  Each iteration
//!   waits for the previous one, so this is the critical-path cost.  Point
//!   formulas are not fully serial, so this is the pessimistic end.
//!
//! * THROUGHPUT -- four independent chains interleaved, so the out-of-order
//!   engine can overlap them.  Point formulas have roughly this much
//!   instruction-level parallelism available, so this is the optimistic end.
//!
//! An empty-body loop is timed with the same harness and printed as
//! `loop overhead`, to show what part of a small number is the harness.

use std::hint::black_box;
use std::time::Instant;

use p256::{fp_add, fp_mul, fp_square, fp_sub, fp_to_montgomery, Fp, FpRaw};

use p256_rc::elliptic_curve::PrimeField;
use p256_rc::FieldElement as RcFe;

const N: u64 = 5_000_000;

/// Timed repetitions per measurement; the minimum is reported.  Every source
/// of error on a shared machine adds time and none subtracts it, so the
/// minimum is the robust summary.
const REPS: usize = 7;

fn bench<F: FnMut()>(iters: u64, mut f: F) -> f64 {
    for _ in 0..(iters / 20 + 1) {
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

/// Our Fp from four little-endian u64 limbs (non-Montgomery), reduced by
/// construction because the caller passes values below the modulus.
fn ours_from(w: [u64; 4]) -> Fp {
    let mut o = Fp([0u64; 4]);
    fp_to_montgomery(&mut o, &FpRaw(w));
    o
}

/// RustCrypto FieldElement from the same four limbs.
fn theirs_from(w: [u64; 4]) -> RcFe {
    let mut be = [0u8; 32];
    for i in 0..4 {
        be[24 - 8 * i..32 - 8 * i].copy_from_slice(&w[i].to_be_bytes());
    }
    RcFe::from_repr(be.into()).unwrap()
}

/// Four distinct field-sized values, well below p, used as the operands.
const SEEDS: [[u64; 4]; 4] = [
    [0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210, 0x1357_9bdf_0246_8ace, 0x0f1e_2d3c_4b5a_6978],
    [0xdead_beef_cafe_babe, 0x0011_2233_4455_6677, 0x8899_aabb_ccdd_eeff, 0x1029_3847_5647_3829],
    [0x7fff_ffff_ffff_fffd, 0x0000_0000_0000_0003, 0x1111_2222_3333_4444, 0x0555_6666_7777_8888],
    [0x0000_0000_0000_0002, 0xffff_ffff_0000_0001, 0x0abc_def0_1234_5678, 0x2222_3333_4444_5555],
];

struct Row {
    name: &'static str,
    ours_lat: f64,
    theirs_lat: f64,
    ours_thr: f64,
    theirs_thr: f64,
}

fn main() {
    let a: Vec<Fp> = SEEDS.iter().map(|s| ours_from(*s)).collect();
    let b: Vec<RcFe> = SEEDS.iter().map(|s| theirs_from(*s)).collect();

    // Sanity: the two backends agree on mul of the first two seeds, so the
    // numbers below are for the same computation.
    {
        let mut o = Fp([0u64; 4]);
        fp_mul(&mut o, &a[0], &a[1]);
        let mut raw = FpRaw([0u64; 4]);
        p256::fp_from_montgomery(&mut raw, &o);
        let t = b[0].multiply(&b[1]);
        let t_be: [u8; 32] = t.to_repr().into();
        let mut ours_be = [0u8; 32];
        for i in 0..4 {
            ours_be[24 - 8 * i..32 - 8 * i].copy_from_slice(&raw.0[i].to_be_bytes());
        }
        assert_eq!(
            ours_be, t_be,
            "field backends disagree -- benchmark is not comparing the same function"
        );
    }

    let overhead = bench(N, || {
        black_box(0u64);
    });

    let mut rows: Vec<Row> = Vec::new();

    // ------------------------------------------------------------------
    // mul
    // ------------------------------------------------------------------
    let ours_mul_lat = {
        let (mut x, c) = (a[0], a[1]);
        let t = bench(N, || {
            let mut o = Fp([0u64; 4]);
            fp_mul(&mut o, &x, &c);
            x = o;
        });
        black_box(x);
        t
    };
    let theirs_mul_lat = {
        let (mut x, c) = (b[0], b[1]);
        let t = bench(N, || x = x.multiply(&c));
        black_box(x);
        t
    };
    let ours_mul_thr = {
        let mut x = [a[0], a[1], a[2], a[3]];
        let c = a[1];
        let t = bench(N, || {
            for i in 0..4 {
                let mut o = Fp([0u64; 4]);
                fp_mul(&mut o, &x[i], &c);
                x[i] = o;
            }
        }) / 4.0;
        black_box(x);
        t
    };
    let theirs_mul_thr = {
        let mut x = [b[0], b[1], b[2], b[3]];
        let c = b[1];
        let t = bench(N, || {
            for i in 0..4 {
                x[i] = x[i].multiply(&c);
            }
        }) / 4.0;
        black_box(x);
        t
    };
    rows.push(Row {
        name: "mul",
        ours_lat: ours_mul_lat,
        theirs_lat: theirs_mul_lat,
        ours_thr: ours_mul_thr,
        theirs_thr: theirs_mul_thr,
    });

    // ------------------------------------------------------------------
    // square (dedicated where available)
    // ------------------------------------------------------------------
    let ours_sq_lat = {
        let mut x = a[0];
        let t = bench(N, || {
            let mut o = Fp([0u64; 4]);
            fp_square(&mut o, &x);
            x = o;
        });
        black_box(x);
        t
    };
    let theirs_sq_lat = {
        let mut x = b[0];
        let t = bench(N, || x = x.square());
        black_box(x);
        t
    };
    let ours_sq_thr = {
        let mut x = [a[0], a[1], a[2], a[3]];
        let t = bench(N, || {
            for i in 0..4 {
                let mut o = Fp([0u64; 4]);
                fp_square(&mut o, &x[i]);
                x[i] = o;
            }
        }) / 4.0;
        black_box(x);
        t
    };
    let theirs_sq_thr = {
        let mut x = [b[0], b[1], b[2], b[3]];
        let t = bench(N, || {
            for i in 0..4 {
                x[i] = x[i].square();
            }
        }) / 4.0;
        black_box(x);
        t
    };
    rows.push(Row {
        name: "square",
        ours_lat: ours_sq_lat,
        theirs_lat: theirs_sq_lat,
        ours_thr: ours_sq_thr,
        theirs_thr: theirs_sq_thr,
    });

    // ------------------------------------------------------------------
    // mul(x, x) -- what a formula pays if it calls mul where a square would do
    // ------------------------------------------------------------------
    let ours_mulxx_lat = {
        let mut x = a[0];
        let t = bench(N, || {
            let mut o = Fp([0u64; 4]);
            fp_mul(&mut o, &x, &x);
            x = o;
        });
        black_box(x);
        t
    };
    let theirs_mulxx_lat = {
        let mut x = b[0];
        let t = bench(N, || x = x.multiply(&x));
        black_box(x);
        t
    };
    rows.push(Row {
        name: "mul(x,x)",
        ours_lat: ours_mulxx_lat,
        theirs_lat: theirs_mulxx_lat,
        ours_thr: f64::NAN,
        theirs_thr: f64::NAN,
    });

    // ------------------------------------------------------------------
    // add
    // ------------------------------------------------------------------
    let ours_add_lat = {
        let (mut x, c) = (a[0], a[1]);
        let t = bench(N, || {
            let mut o = Fp([0u64; 4]);
            fp_add(&mut o, &x, &c);
            x = o;
        });
        black_box(x);
        t
    };
    let theirs_add_lat = {
        let (mut x, c) = (b[0], b[1]);
        let t = bench(N, || x = x.add(&c));
        black_box(x);
        t
    };
    let ours_add_thr = {
        let mut x = [a[0], a[1], a[2], a[3]];
        let c = a[1];
        let t = bench(N, || {
            for i in 0..4 {
                let mut o = Fp([0u64; 4]);
                fp_add(&mut o, &x[i], &c);
                x[i] = o;
            }
        }) / 4.0;
        black_box(x);
        t
    };
    let theirs_add_thr = {
        let mut x = [b[0], b[1], b[2], b[3]];
        let c = b[1];
        let t = bench(N, || {
            for i in 0..4 {
                x[i] = x[i].add(&c);
            }
        }) / 4.0;
        black_box(x);
        t
    };
    rows.push(Row {
        name: "add",
        ours_lat: ours_add_lat,
        theirs_lat: theirs_add_lat,
        ours_thr: ours_add_thr,
        theirs_thr: theirs_add_thr,
    });

    // ------------------------------------------------------------------
    // sub
    // ------------------------------------------------------------------
    let ours_sub_lat = {
        let (mut x, c) = (a[0], a[1]);
        let t = bench(N, || {
            let mut o = Fp([0u64; 4]);
            fp_sub(&mut o, &x, &c);
            x = o;
        });
        black_box(x);
        t
    };
    let theirs_sub_lat = {
        let (mut x, c) = (b[0], b[1]);
        let t = bench(N, || x = x.sub(&c));
        black_box(x);
        t
    };
    let ours_sub_thr = {
        let mut x = [a[0], a[1], a[2], a[3]];
        let c = a[1];
        let t = bench(N, || {
            for i in 0..4 {
                let mut o = Fp([0u64; 4]);
                fp_sub(&mut o, &x[i], &c);
                x[i] = o;
            }
        }) / 4.0;
        black_box(x);
        t
    };
    let theirs_sub_thr = {
        let mut x = [b[0], b[1], b[2], b[3]];
        let c = b[1];
        let t = bench(N, || {
            for i in 0..4 {
                x[i] = x[i].sub(&c);
            }
        }) / 4.0;
        black_box(x);
        t
    };
    rows.push(Row {
        name: "sub",
        ours_lat: ours_sub_lat,
        theirs_lat: theirs_sub_lat,
        ours_thr: ours_sub_thr,
        theirs_thr: theirs_sub_thr,
    });

    // ------------------------------------------------------------------
    println!("P-256 field layer -- fiat-crypto p256_64 vs RustCrypto p256 0.13.2 hand-written 4x64");
    println!("iterations per measurement: {}", N);
    println!("empty-loop overhead: {:.3} ns/iter", overhead);
    println!();
    println!(
        "{:<10} {:>10} {:>10} {:>8}   {:>10} {:>10} {:>8}",
        "op", "ours(lat)", "rc(lat)", "ratio", "ours(thr)", "rc(thr)", "ratio"
    );
    println!("{}", "-".repeat(76));
    for r in &rows {
        if r.ours_thr.is_nan() {
            println!(
                "{:<10} {:>10.3} {:>10.3} {:>7.2}x   {:>10} {:>10} {:>8}",
                r.name,
                r.ours_lat,
                r.theirs_lat,
                r.ours_lat / r.theirs_lat,
                "-",
                "-",
                "-"
            );
        } else {
            println!(
                "{:<10} {:>10.3} {:>10.3} {:>7.2}x   {:>10.3} {:>10.3} {:>7.2}x",
                r.name,
                r.ours_lat,
                r.theirs_lat,
                r.ours_lat / r.theirs_lat,
                r.ours_thr,
                r.theirs_thr,
                r.ours_thr / r.theirs_thr
            );
        }
    }
    println!();
    println!("ns/op; ratio = ours / RustCrypto; below 1.00 means this work is faster.");
}
