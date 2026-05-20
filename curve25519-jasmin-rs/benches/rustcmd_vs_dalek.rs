//! Benchmark: framework's extracted `rust_cmd_ed` Ed25519 sign/verify
//! vs. upstream `ed25519-dalek`.
//!
//! The framework path is the verified Rust emission of the
//! `rust_cmd_ed` AST (see `src/ed25519_rustcmd/{sign,verify}.rs`),
//! linked against the same FFI leaves used in production
//! (curve25519-dalek for the heavy curve ops, `sha2` for SHA-512,
//! Jasmin asm for `clamp_64`).  This bench answers: what is the
//! steady-state overhead of going through the extracted body vs.
//! a hand-written, optimized Ed25519 impl?
//!
//! Build:
//!   JASMINC=$(which jasminc) \
//!     cargo bench --features ed25519_rustcmd --bench rustcmd_vs_dalek

#![cfg(feature = "ed25519_rustcmd")]

use criterion::{black_box, criterion_group, criterion_main, Criterion, Throughput};
use ed25519_dalek::{Signer, SigningKey, Verifier};

// RFC 8032 §7.1 TEST 2 — 1-byte message.  Used as default work-load.
const SEED: [u8; 32] = [
    0x4c, 0xcd, 0x08, 0x9b, 0x28, 0xff, 0x96, 0xda,
    0x9d, 0xb6, 0xc3, 0x46, 0xec, 0x11, 0x4e, 0x0f,
    0x5b, 0x8a, 0x31, 0x9f, 0x35, 0xab, 0xa6, 0x24,
    0xda, 0x8c, 0xf6, 0xed, 0x4f, 0xb8, 0xa6, 0xfb,
];
const PK: [u8; 32] = [
    0x3d, 0x40, 0x17, 0xc3, 0xe8, 0x43, 0x89, 0x5a,
    0x92, 0xb7, 0x0a, 0xa7, 0x4d, 0x1b, 0x7e, 0xbc,
    0x9c, 0x98, 0x2c, 0xcf, 0x2e, 0xc4, 0x96, 0x8c,
    0xc0, 0xcd, 0x55, 0xf1, 0x2a, 0xf4, 0x66, 0x0c,
];
const MSG: [u8; 1] = [0x72];
const SIG: [u8; 64] = [
    0x92, 0xa0, 0x09, 0xa9, 0xf0, 0xd4, 0xca, 0xb8,
    0x72, 0x0e, 0x82, 0x0b, 0x5f, 0x64, 0x25, 0x40,
    0xa2, 0xb2, 0x7b, 0x54, 0x16, 0x50, 0x3f, 0x8f,
    0xb3, 0x76, 0x22, 0x23, 0xeb, 0xdb, 0x69, 0xda,
    0x08, 0x5a, 0xc1, 0xe4, 0x3e, 0x15, 0x99, 0x6e,
    0x45, 0x8f, 0x36, 0x13, 0xd0, 0xf1, 0x1d, 0x8c,
    0x38, 0x7b, 0x2e, 0xae, 0xb4, 0x30, 0x2a, 0xee,
    0xb0, 0x0d, 0x29, 0x16, 0x12, 0xbb, 0x0c, 0x00,
];

fn bench_sign(c: &mut Criterion) {
    let mut group = c.benchmark_group("ed25519_sign");
    group.throughput(Throughput::Elements(1));

    // Sanity: confirm the framework signs to the RFC byte string before
    // we start the harness — diverging signatures would make the
    // ns/op numbers apples-to-oranges.
    {
        let mut sig = [0u8; 64];
        curve25519_jasmin::ed25519_rustcmd::sign(&mut sig, &SEED, &MSG);
        assert_eq!(sig, SIG, "framework sign disagrees with RFC 8032 TEST 2");
    }

    group.bench_function("framework", |b| {
        let seed = SEED;
        let msg = MSG;
        let mut sig = [0u8; 64];
        b.iter(|| {
            curve25519_jasmin::ed25519_rustcmd::sign(
                black_box(&mut sig),
                black_box(&seed),
                black_box(&msg),
            );
        });
    });

    group.bench_function("dalek", |b| {
        let signing = SigningKey::from_bytes(&SEED);
        let msg = MSG;
        b.iter(|| {
            black_box(signing.sign(black_box(&msg)));
        });
    });

    group.finish();
}

fn bench_verify(c: &mut Criterion) {
    let mut group = c.benchmark_group("ed25519_verify");
    group.throughput(Throughput::Elements(1));

    // Sanity: framework must accept the RFC vector.
    assert!(
        curve25519_jasmin::ed25519_rustcmd::verify(&SIG, &PK, &MSG),
        "framework verify rejected valid RFC 8032 TEST 2 sig",
    );

    group.bench_function("framework", |b| {
        let sig = SIG;
        let pk = PK;
        let msg = MSG;
        b.iter(|| {
            black_box(curve25519_jasmin::ed25519_rustcmd::verify(
                black_box(&sig),
                black_box(&pk),
                black_box(&msg),
            ));
        });
    });

    group.bench_function("dalek", |b| {
        let vk = ed25519_dalek::VerifyingKey::from_bytes(&PK)
            .expect("RFC 8032 TEST 2 PK is a valid Edwards point");
        let sig = ed25519_dalek::Signature::from_bytes(&SIG);
        let msg = MSG;
        b.iter(|| {
            black_box(vk.verify(black_box(&msg), black_box(&sig)).is_ok());
        });
    });

    group.finish();
}

criterion_group!(benches, bench_sign, bench_verify);
criterion_main!(benches);
