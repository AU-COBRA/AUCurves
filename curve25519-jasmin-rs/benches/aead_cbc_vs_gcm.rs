//! Benchmark: AES-256-CBC + HMAC-SHA-256 (the runtime Signal-spec
//! AEAD since 2026-05-13) vs legacy AES-256-GCM (RustCrypto AES-NI).
//!
//! The CBC + HMAC path uses libcrux-lean-specs's pure-Rust FIPS-197
//! AES (no AES-NI, no `unsafe`) + safe-Rust CBC chaining + verified
//! HMAC-SHA-256 over libjade SHA-256.  Expected delta vs AES-GCM:
//! ~1-2 orders of magnitude slower for the cipher path (AES-NI runs
//! at ~1-3 cycles/byte, software FIPS-197 at ~30-80 cycles/byte).
//!
//! Build / run:
//!   JASMINC=$(which jasminc) \
//!     cargo bench --features "dalek_leaves aes_gcm_legacy" \
//!                 --bench aead_cbc_vs_gcm
//!
//! The `aes_gcm_legacy` feature is REQUIRED to compile the GCM
//! comparison arm.  Without it, only the CBC+HMAC arm runs (still
//! useful as a steady-state perf number for the new path).

use criterion::{black_box, criterion_group, criterion_main, Criterion, Throughput};

use curve25519_jasmin::symmetric::{
    aes256_cbc_hmac_encrypt_nonce, aes256_cbc_hmac_decrypt_nonce,
};

#[cfg(feature = "aes_gcm_legacy")]
use curve25519_jasmin::symmetric::{aes256_gcm_encrypt, aes256_gcm_decrypt};

const SIZES: &[usize] = &[16, 64, 256, 1024, 4096];

fn bench_encrypt(c: &mut Criterion) {
    let key = [0xA5u8; 32];
    let nonce = [0x5Au8; 12];
    let aad = b"signal-aad";

    let mut group = c.benchmark_group("aead_encrypt");
    for &len in SIZES {
        group.throughput(Throughput::Bytes(len as u64));
        let pt: Vec<u8> = (0..len).map(|i| (i as u8).wrapping_mul(31)).collect();

        group.bench_function(format!("cbc_hmac/{len}"), |b| {
            b.iter(|| {
                let ct = aes256_cbc_hmac_encrypt_nonce(
                    black_box(&key), black_box(&nonce),
                    black_box(aad), black_box(&pt)).unwrap();
                black_box(ct)
            })
        });

        #[cfg(feature = "aes_gcm_legacy")]
        group.bench_function(format!("gcm_legacy/{len}"), |b| {
            b.iter(|| {
                let ct = aes256_gcm_encrypt(
                    black_box(&key), black_box(&nonce),
                    black_box(aad), black_box(&pt)).unwrap();
                black_box(ct)
            })
        });
    }
    group.finish();
}

fn bench_decrypt(c: &mut Criterion) {
    let key = [0xA5u8; 32];
    let nonce = [0x5Au8; 12];
    let aad = b"signal-aad";

    let mut group = c.benchmark_group("aead_decrypt");
    for &len in SIZES {
        group.throughput(Throughput::Bytes(len as u64));
        let pt: Vec<u8> = (0..len).map(|i| (i as u8).wrapping_mul(31)).collect();
        let cbc_wire = aes256_cbc_hmac_encrypt_nonce(&key, &nonce, aad, &pt).unwrap();
        group.bench_function(format!("cbc_hmac/{len}"), |b| {
            b.iter(|| {
                let pt2 = aes256_cbc_hmac_decrypt_nonce(
                    black_box(&key), black_box(&nonce),
                    black_box(aad), black_box(&cbc_wire)).unwrap();
                black_box(pt2)
            })
        });

        #[cfg(feature = "aes_gcm_legacy")]
        {
            let gcm_wire = aes256_gcm_encrypt(&key, &nonce, aad, &pt).unwrap();
            group.bench_function(format!("gcm_legacy/{len}"), |b| {
                b.iter(|| {
                    let pt2 = aes256_gcm_decrypt(
                        black_box(&key), black_box(&nonce),
                        black_box(aad), black_box(&gcm_wire)).unwrap();
                    black_box(pt2)
                })
            });
        }
    }
    group.finish();
}

criterion_group!(benches, bench_encrypt, bench_decrypt);
criterion_main!(benches);
