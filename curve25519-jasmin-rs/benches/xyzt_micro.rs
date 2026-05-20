//! Per-leaf microbench to isolate where Ed25519 sign/verify time is
//! spent in `wnaf_comb_leaves + tfp25519_limbs`.  Compare each layer
//! against its dalek counterpart.
//!
//! Layers measured:
//!   (1) `xyzt_add_decomposed`     — one Edwards add (18 field ops).
//!   (2) `xyzt_double_decomposed`  — one Edwards double (~11 field ops).
//!   (3) `comb_scalarmult_base`    — sign hot path (64 adds, 0 doubles).
//!   (4) `wnaf_scalarmult`         — verify hot path (52 adds, 260 doubles).
//!   (5) dalek `EdwardsPoint + EdwardsPoint`, `.double()`,
//!       `&Scalar * &BASEPOINT_TABLE`, `&Scalar * &EdwardsPoint`.

#![cfg(all(feature = "wnaf_comb_leaves", feature = "tfp25519_limbs"))]

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use curve25519_dalek::{
    constants::ED25519_BASEPOINT_TABLE,
    edwards::EdwardsPoint,
    scalar::Scalar,
    traits::Identity,
};
// Pull in the lib's Rust-level entry so the linker keeps the
// no_mangle xyzt_*_decomposed / comb_table_lookup / etc. symbols
// alive under --gc-sections (the bench's extern decls alone aren't
// enough to anchor them).
#[allow(unused_imports)]
use curve25519_jasmin::ed25519_rustcmd::sign as _force_link_anchor;

extern "C" {
    fn xyzt_add_decomposed(out: *mut u8, a: *const u8, b: *const u8);
    fn xyzt_double_decomposed(out: *mut u8, a: *const u8);
    fn comb_scalarmult_base(out: *mut u8, scalar: *const u8);
    fn wnaf_scalarmult(out: *mut u8, digits: *const u8, point: *const u8);
    fn comb_table_lookup(dest: *mut u8, win_idx: u64, digit: u64);
}

fn bench(c: &mut Criterion) {
    let mut g = c.benchmark_group("xyzt_micro");

    // --- Set up two valid 200-byte XYZT slots via the comb table. ---
    let mut p1 = [0u8; 200];
    let mut p2 = [0u8; 200];
    unsafe {
        comb_table_lookup(p1.as_mut_ptr(), 0, 5);
        comb_table_lookup(p2.as_mut_ptr(), 10, 7);
    }
    let mut p_out = [0u8; 200];

    // (1) xyzt_add — one Edwards add (18 field ops).
    g.bench_function("framework_xyzt_add", |b| {
        b.iter(|| unsafe {
            xyzt_add_decomposed(p_out.as_mut_ptr(),
                                black_box(p1.as_ptr()),
                                black_box(p2.as_ptr()));
            black_box(&p_out);
        });
    });

    // (2) xyzt_double — one Edwards double (~11 field ops).
    g.bench_function("framework_xyzt_double", |b| {
        b.iter(|| unsafe {
            xyzt_double_decomposed(p_out.as_mut_ptr(),
                                   black_box(p1.as_ptr()));
            black_box(&p_out);
        });
    });

    // (3) comb scalarmult_base — sign hot path, 64 adds.
    let scalar32 = [
        0x9d, 0x61, 0xb1, 0x9d, 0xef, 0xfd, 0x5a, 0x60,
        0xba, 0x84, 0x4a, 0xf4, 0x92, 0xec, 0x2c, 0xc4,
        0x44, 0x49, 0xc5, 0x69, 0x7b, 0x32, 0x69, 0x19,
        0x70, 0x3b, 0xac, 0x03, 0x1c, 0xae, 0x7f, 0x60,
    ];
    g.bench_function("framework_comb_scalarmult_base", |b| {
        b.iter(|| unsafe {
            comb_scalarmult_base(p_out.as_mut_ptr(), black_box(scalar32.as_ptr()));
            black_box(&p_out);
        });
    });

    // (4) wnaf scalarmult — verify hot path, 52 adds + 260 doubles.
    // Requires 64-byte digits input (the wnaf-encoded scalar).  We
    // pretend the same 32-byte scalar is the digit stream — this isn't
    // semantically valid but exercises the bench timing.
    let mut digits = [0u8; 64];
    digits[..32].copy_from_slice(&scalar32);
    g.bench_function("framework_wnaf_scalarmult", |b| {
        b.iter(|| unsafe {
            wnaf_scalarmult(p_out.as_mut_ptr(),
                            black_box(digits.as_ptr()),
                            black_box(p1.as_ptr()));
            black_box(&p_out);
        });
    });

    // --- Dalek counterparts ---
    let s = Scalar::from_bytes_mod_order(scalar32);
    let pt1 = EdwardsPoint::mul_base(&s);
    let pt2 = EdwardsPoint::mul_base(&Scalar::from_bytes_mod_order([
        7u8; 32
    ]));

    g.bench_function("dalek_edwards_add", |b| {
        b.iter(|| {
            let r = black_box(&pt1) + black_box(&pt2);
            black_box(r);
        });
    });

    // Dalek's pub-API doubling: 2 * P via scalar multiplication is
    // overkill; closest exposed form is P + P (which the impl
    // shortcircuits to point doubling internally).
    g.bench_function("dalek_edwards_double", |b| {
        b.iter(|| {
            let r = black_box(&pt1) + black_box(&pt1);
            black_box(r);
        });
    });

    g.bench_function("dalek_scalarmult_base", |b| {
        b.iter(|| {
            let r = EdwardsPoint::mul_base(black_box(&s));
            black_box(r);
        });
    });

    g.bench_function("dalek_scalarmult", |b| {
        b.iter(|| {
            let r = black_box(&s) * black_box(&pt1);
            black_box(r);
        });
    });

    let _ = (EdwardsPoint::identity(), ED25519_BASEPOINT_TABLE);  // silence unused

    g.finish();
}

criterion_group!(benches, bench);
criterion_main!(benches);
