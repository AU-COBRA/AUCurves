//! B2 feasibility microbench: compare fiat-rust 5×51 carry_mul/carry_square
//! against CryptOpt's 4×64 asm mul/square, with and without representation
//! bridging cost.  Answers: is wiring CryptOpt asm into the
//! `decomposed_leaves` fe25519 shim a net win, or does the 5×51↔4×64 hop
//! cost more than the asm saves?

#![cfg(feature = "decomposed_leaves")]

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use fiat_crypto::curve25519_64::{
    fiat_25519_carry_mul, fiat_25519_carry_square, fiat_25519_from_bytes,
    fiat_25519_loose_field_element, fiat_25519_relax, fiat_25519_tight_field_element,
    fiat_25519_to_bytes,
};

// Route through the library's `fe_mul`/`fe_square` wrappers so the
// static-lib link to libcurve25519_jasmin_asm.a survives `--gc-sections`.
use curve25519_jasmin::{fe_mul as cryptopt_mul, fe_square as cryptopt_square, Fe25519};

fn bench(c: &mut Criterion) {
    let mut g = c.benchmark_group("fe25519_micro");

    // Realistic-ish inputs: pseudo-random 251-bit values.
    let a_t = fiat_25519_tight_field_element([
        0x012345_6789abc,
        0x019876_5432101,
        0x0abcde_f012345,
        0x056789_abcdef0,
        0x011223_3445566,
    ]);
    let b_t = fiat_25519_tight_field_element([
        0x0fedcb_a987654,
        0x0123456789abcu64,
        0x0aabbc_cddee01,
        0x0223344556677u64,
        0x07eeff_aabbcc1,
    ]);
    let mut a_l = fiat_25519_loose_field_element([0; 5]);
    let mut b_l = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_relax(&mut a_l, &a_t);
    fiat_25519_relax(&mut b_l, &b_t);

    // (A) bare fiat 5x51 carry_mul / carry_square
    g.bench_function("fiat5x51_carry_mul_bare", |b| {
        let mut out = fiat_25519_tight_field_element([0; 5]);
        b.iter(|| {
            fiat_25519_carry_mul(&mut out, black_box(&a_l), black_box(&b_l));
        });
    });
    g.bench_function("fiat5x51_carry_square_bare", |b| {
        let mut out = fiat_25519_tight_field_element([0; 5]);
        b.iter(|| {
            fiat_25519_carry_square(&mut out, black_box(&a_l));
        });
    });

    // (B) what fe25519_portable.rs actually does on each mul:
    //   read 40-byte tight slot -> from_bytes -> relax -> carry_mul -> to_bytes
    g.bench_function("fiat5x51_full_shim_mul", |b| {
        let a_bytes = {
            let mut bs = [0u8; 40];
            fiat_25519_to_bytes(<&mut [u8; 32]>::try_from(&mut bs[0..32]).unwrap(), &a_t);
            bs
        };
        let b_bytes = {
            let mut bs = [0u8; 40];
            fiat_25519_to_bytes(<&mut [u8; 32]>::try_from(&mut bs[0..32]).unwrap(), &b_t);
            bs
        };
        b.iter(|| {
            let mut at = fiat_25519_tight_field_element([0; 5]);
            let mut bt = fiat_25519_tight_field_element([0; 5]);
            let mut head = [0u8; 32];
            head.copy_from_slice(&black_box(a_bytes)[0..32]);
            head[31] &= 0x7f;
            fiat_25519_from_bytes(&mut at, &head);
            head.copy_from_slice(&black_box(b_bytes)[0..32]);
            head[31] &= 0x7f;
            fiat_25519_from_bytes(&mut bt, &head);
            let mut al = fiat_25519_loose_field_element([0; 5]);
            let mut bl = fiat_25519_loose_field_element([0; 5]);
            fiat_25519_relax(&mut al, &at);
            fiat_25519_relax(&mut bl, &bt);
            let mut r = fiat_25519_tight_field_element([0; 5]);
            fiat_25519_carry_mul(&mut r, &al, &bl);
            let mut out_bytes = [0u8; 32];
            fiat_25519_to_bytes(&mut out_bytes, &r);
            black_box(out_bytes);
        });
    });

    // (C) raw CryptOpt 4x64 mul / square — no bridging, just the asm.
    let a4 = Fe25519::from_limbs([0x0123456789abcdefu64, 0xfedcba9876543210, 0x0011223344556677, 0x7766554433221100]);
    let b4 = Fe25519::from_limbs([0xaabbccddeeff0011u64, 0x1100ffeeddccbbaa, 0x123456789abcdef0, 0x0fedcba987654321]);
    g.bench_function("cryptopt4x64_mul_bare", |b| {
        let mut out = Fe25519::zero();
        b.iter(|| {
            cryptopt_mul(&mut out, black_box(&a4), black_box(&b4));
            black_box(&out);
        });
    });
    g.bench_function("cryptopt4x64_square_bare", |b| {
        let mut out = Fe25519::zero();
        b.iter(|| {
            cryptopt_square(&mut out, black_box(&a4));
            black_box(&out);
        });
    });

    // (D) CryptOpt 4x64 mul WITH 5x51↔4x64 bridge (this is what we'd pay
    //     if we keep the 5x51 byte-slot representation and only swap the
    //     mul/square primitive).
    g.bench_function("cryptopt4x64_mul_with_5x51_bridge", |b| {
        b.iter(|| {
            // 5x51 tight -> 32 LE bytes -> 4x64
            let mut ab = [0u8; 32];
            let mut bb = [0u8; 32];
            fiat_25519_to_bytes(&mut ab, black_box(&a_t));
            fiat_25519_to_bytes(&mut bb, black_box(&b_t));
            let a4 = Fe25519::from_limbs([
                u64::from_le_bytes(ab[0..8].try_into().unwrap()),
                u64::from_le_bytes(ab[8..16].try_into().unwrap()),
                u64::from_le_bytes(ab[16..24].try_into().unwrap()),
                u64::from_le_bytes(ab[24..32].try_into().unwrap()),
            ]);
            let b4 = Fe25519::from_limbs([
                u64::from_le_bytes(bb[0..8].try_into().unwrap()),
                u64::from_le_bytes(bb[8..16].try_into().unwrap()),
                u64::from_le_bytes(bb[16..24].try_into().unwrap()),
                u64::from_le_bytes(bb[24..32].try_into().unwrap()),
            ]);
            let mut out4 = Fe25519::zero();
            cryptopt_mul(&mut out4, &a4, &b4);
            // 4x64 -> 32 LE bytes -> 5x51 tight.  NB: this is missing the
            // canonical reduction (out4 may be in [0, 2^256)), so for a
            // real shim we'd also pay one reduction here.
            let mut ob = [0u8; 32];
            ob[0..8].copy_from_slice(&out4.0[0].to_le_bytes());
            ob[8..16].copy_from_slice(&out4.0[1].to_le_bytes());
            ob[16..24].copy_from_slice(&out4.0[2].to_le_bytes());
            ob[24..32].copy_from_slice(&out4.0[3].to_le_bytes());
            ob[31] &= 0x7f;
            let mut out_t = fiat_25519_tight_field_element([0; 5]);
            fiat_25519_from_bytes(&mut out_t, &ob);
            black_box(out_t);
        });
    });

    g.finish();
}

criterion_group!(benches, bench);
criterion_main!(benches);
