//! Benchmark: our verified X25519 vs. curve25519-dalek backends.

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use curve25519_jasmin::Fe25519;

// RFC 7748 test vector scalar and point
const SCALAR: [u8; 32] = [
    0xa5, 0x46, 0xe3, 0x6b, 0xf0, 0x52, 0x7c, 0x9d,
    0x3b, 0x16, 0x15, 0x4b, 0x82, 0x46, 0x5e, 0xdd,
    0x62, 0x14, 0x4c, 0x0a, 0xc1, 0xfc, 0x5a, 0x18,
    0x50, 0x6a, 0x22, 0x44, 0xba, 0x44, 0x9a, 0xc4,
];
const U_COORD: [u8; 32] = [
    0xe6, 0xdb, 0x68, 0x67, 0x58, 0x30, 0x30, 0xdb,
    0x35, 0x94, 0xc1, 0xa4, 0x24, 0xb1, 0x5f, 0x7c,
    0x72, 0x66, 0x24, 0xec, 0x26, 0xb3, 0x35, 0x3b,
    0x10, 0xa9, 0x03, 0xa6, 0xd0, 0xab, 0x1c, 0x4c,
];

fn bench_x25519(c: &mut Criterion) {
    let mut group = c.benchmark_group("x25519_scalar_mult");

    // Our pure Jasmin path (libjade mulx, EasyCrypt-verified)
    group.bench_function("jasmin_pure", |b| {
        b.iter(|| {
            curve25519_jasmin::x25519_jasmin(
                black_box(&SCALAR), black_box(&U_COORD))
        })
    });

    // CryptOpt-inlined Jasmin (optimized MULX/ADCX/ADOX schedule, jasminc-compiled)
    group.bench_function("jasmin_cryptopt", |b| {
        b.iter(|| {
            curve25519_jasmin::x25519_cryptopt(
                black_box(&SCALAR), black_box(&U_COORD))
        })
    });

    // Hybrid path (Rust ladder + CryptOpt mul/sqr + Jasmin add/sub via FFI)
    group.bench_function("hybrid_ffi", |b| {
        b.iter(|| {
            curve25519_jasmin::x25519_hybrid(
                black_box(&SCALAR), black_box(&U_COORD))
        })
    });

    // bedrock2 ToCString extraction (exact verified code, clang -O3)
    group.bench_function("bedrock2_c", |b| {
        b.iter(|| {
            curve25519_jasmin::x25519_bedrock2(
                black_box(&SCALAR), black_box(&U_COORD))
        })
    });

    // fiat-crypto standalone C field ops + hand-written ladder (clang -O3)
    group.bench_function("fiat_c", |b| {
        b.iter(|| {
            curve25519_jasmin::x25519_fiat_c(
                black_box(&SCALAR), black_box(&U_COORD))
        })
    });

    // dalek (default backend)
    group.bench_function("dalek_default", |b| {
        use x25519_dalek::{PublicKey, StaticSecret};
        let secret = StaticSecret::from(SCALAR);
        let public = PublicKey::from(U_COORD);
        b.iter(|| secret.diffie_hellman(black_box(&public)))
    });

    group.finish();
}

fn bench_base_mult(c: &mut Criterion) {
    let mut group = c.benchmark_group("x25519_base_mult");

    group.bench_function("jasmin_base", |b| {
        b.iter(|| curve25519_jasmin::x25519_jasmin_base(black_box(&SCALAR)))
    });

    group.bench_function("dalek_base", |b| {
        use x25519_dalek::StaticSecret;
        let secret = StaticSecret::from(SCALAR);
        b.iter(|| x25519_dalek::PublicKey::from(black_box(&secret)))
    });

    group.finish();
}

fn bench_field_ops(c: &mut Criterion) {
    let mut group = c.benchmark_group("field_ops");

    let a = Fe25519::from_limbs([
        0x0fffffffffffffff, 0x0fffffffffffffff,
        0x0fffffffffffffff, 0x0fffffffffffffff,
    ]);
    let b = Fe25519::from_limbs([
        0x0123456789abcdef, 0xfedcba9876543210,
        0x0011223344556677, 0x7766554433221100,
    ]);

    // CryptOpt mul (via FFI)
    group.bench_function("cryptopt_mul", |b_| {
        let mut out = Fe25519::zero();
        b_.iter(|| curve25519_jasmin::fe_mul(&mut out, black_box(&a), black_box(&b)))
    });

    // CryptOpt square (via FFI)
    group.bench_function("cryptopt_square", |b_| {
        let mut out = Fe25519::zero();
        b_.iter(|| curve25519_jasmin::fe_square(&mut out, black_box(&a)))
    });

    // Jasmin add (via FFI)
    group.bench_function("jasmin_add", |b_| {
        let mut out = Fe25519::zero();
        b_.iter(|| curve25519_jasmin::fe_add(&mut out, black_box(&a), black_box(&b)))
    });

    // Jasmin sub (via FFI)
    group.bench_function("jasmin_sub", |b_| {
        let mut out = Fe25519::zero();
        b_.iter(|| curve25519_jasmin::fe_sub(&mut out, black_box(&a), black_box(&b)))
    });

    // Jasmin mul_a24 (via FFI)
    group.bench_function("jasmin_mul_a24", |b_| {
        let mut out = Fe25519::zero();
        b_.iter(|| curve25519_jasmin::fe_mul_a24(&mut out, black_box(&a)))
    });

    // Jasmin cswap (via FFI)
    group.bench_function("jasmin_cswap", |b_| {
        let mut x = a;
        let mut y = b;
        b_.iter(|| curve25519_jasmin::fe_cswap(&mut x, &mut y, black_box(1)))
    });

    group.finish();
}

criterion_group!(benches, bench_x25519, bench_base_mult, bench_field_ops);
criterion_main!(benches);
