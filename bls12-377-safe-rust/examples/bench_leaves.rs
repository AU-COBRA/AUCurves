//! Micro-benchmark for the Fp leaves.
//!
//! Compares the `_bls377_*` C-ABI extern symbols (resolved either to
//! the Jasmin-emitted .s files when `--features jasmin_leaves` is
//! set, or to the Rust extern_shim otherwise) against the in-crate
//! `fp_*` baseline (fiat-rust direct, with no extern boundary).
//!
//! Run both:
//!   cargo run --release --example bench_leaves
//!   cargo run --release --features jasmin_leaves --example bench_leaves
use bls12_377::{Fp, FpRaw, fp_add, fp_sub, fp_to_montgomery};
use std::hint::black_box;
use std::time::Instant;

// Re-import the C-ABI extern symbols.  When `jasmin_leaves` is on,
// these resolve to the assembled .s files; otherwise to the Rust
// extern_shim defined in src/lib.rs.
unsafe extern "C" {
    fn _bls377_add(o: *mut u64, x: *const u64, y: *const u64);
    fn _bls377_sub(o: *mut u64, x: *const u64, y: *const u64);
    fn _bls377_select_znz(o: *mut u64, c: u64, x: *const u64, y: *const u64);
}

fn one_mont() -> Fp {
    let raw = FpRaw({ let mut a = [0u64; 6]; a[0] = 1; a });
    let mut out = Fp([0u64; 6]);
    fp_to_montgomery(&mut out, &raw);
    out
}

const ITERS: u64 = 5_000_000;

fn bench<F: FnMut()>(label: &str, mut f: F) {
    for _ in 0..10_000 { f(); }
    let t0 = Instant::now();
    for _ in 0..ITERS { f(); }
    let elapsed = t0.elapsed();
    let ns_per_iter = elapsed.as_nanos() as f64 / ITERS as f64;
    println!("  {:36} {:>8.2} ns/op  ({} iters in {:.2?})",
             label, ns_per_iter, ITERS, elapsed);
}

fn main() {
    println!("BLS12-377 Fp leaf microbench");
    println!("  jasmin_leaves feature: {}",
             if cfg!(feature = "jasmin_leaves") { "ON  (Jasmin .s)" }
             else { "off (fiat-rust shim)" });
    println!();

    let a = one_mont();
    let b = one_mont();
    let a_arr: [u64; 6] = a.0;
    let b_arr: [u64; 6] = b.0;
    let mut out_arr: [u64; 6] = [0u64; 6];

    println!("=== add ===");
    bench("_bls377_add (extern: jasmin/shim)", || unsafe {
        _bls377_add(black_box(out_arr.as_mut_ptr()),
                    black_box(a_arr.as_ptr()),
                    black_box(b_arr.as_ptr()));
    });
    {
        let mut out = Fp([0u64; 6]);
        bench("fp_add (fiat-rust direct, inlined)", || {
            fp_add(black_box(&mut out), black_box(&a), black_box(&b));
        });
    }

    println!("=== sub ===");
    bench("_bls377_sub (extern: jasmin/shim)", || unsafe {
        _bls377_sub(black_box(out_arr.as_mut_ptr()),
                    black_box(a_arr.as_ptr()),
                    black_box(b_arr.as_ptr()));
    });
    {
        let mut out = Fp([0u64; 6]);
        bench("fp_sub (fiat-rust direct, inlined)", || {
            fp_sub(black_box(&mut out), black_box(&a), black_box(&b));
        });
    }

    println!("=== select_znz ===");
    bench("_bls377_select_znz c=0", || unsafe {
        _bls377_select_znz(black_box(out_arr.as_mut_ptr()), 0,
                           black_box(a_arr.as_ptr()),
                           black_box(b_arr.as_ptr()));
    });
    bench("_bls377_select_znz c=1", || unsafe {
        _bls377_select_znz(black_box(out_arr.as_mut_ptr()), 1,
                           black_box(a_arr.as_ptr()),
                           black_box(b_arr.as_ptr()));
    });
}
