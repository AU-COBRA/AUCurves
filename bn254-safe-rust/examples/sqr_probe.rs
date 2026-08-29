//! Probe: is `fp_square(x)` really slower than `fp_mul(x, x)`?
//!
//! `stubs.rs::_bn254_square` is literally `mont_mul(xv, xv)`, the same body
//! as `_bn254_mul`, so the two should cost the same.  `bench_breakdown`
//! reports Fp sqr at ~160 ns against Fp mul at ~22 ns, which cannot be a
//! property of that code.  This probe times them side by side in one
//! process, as serial dependency chains, and reports invariant-TSC cycles.

use bn254::*;
use std::hint::black_box;

#[inline]
fn rdtsc() -> u64 {
    unsafe {
        use core::arch::x86_64::{_mm_lfence, _rdtsc};
        _mm_lfence();
        let t = _rdtsc();
        _mm_lfence();
        t
    }
}

const N: usize = 2_000_000;

fn main() {
    let a = Fp([
        0x7a17caa950ad28d7,
        0x1f6ac17ae15521b9,
        0x334bea4e696bd284,
        0x2a1f6744ce179d8e,
    ]);

    // warm up
    let mut c = Fp::zero();
    for _ in 0..1000 {
        fp_mul(&mut c, &a, &a);
        fp_square(&mut c, &a);
    }

    let mut acc = a;
    let t0 = rdtsc();
    for _ in 0..N {
        fp_mul(&mut c, black_box(&acc), black_box(&acc));
        acc = c;
    }
    let mul_cyc = (rdtsc() - t0) as f64 / N as f64;
    black_box(&acc);

    let mut acc = a;
    let t0 = rdtsc();
    for _ in 0..N {
        fp_square(&mut c, black_box(&acc));
        acc = c;
    }
    let sqr_cyc = (rdtsc() - t0) as f64 / N as f64;
    black_box(&acc);

    // Agreement check: the two must compute the same function.
    let mut m = Fp::zero();
    let mut s = Fp::zero();
    fp_mul(&mut m, &a, &a);
    fp_square(&mut s, &a);

    println!("fp_mul(x, x) : {mul_cyc:8.1} cycles");
    println!("fp_square(x) : {sqr_cyc:8.1} cycles");
    println!("ratio sqr/mul: {:8.2}x", sqr_cyc / mul_cyc);
    println!("same result  : {}", m.0 == s.0);
}
