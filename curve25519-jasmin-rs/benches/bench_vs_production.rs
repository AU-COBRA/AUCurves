//! Track X: CT-only invert benchmark — OURS vs production references.
//!
//! Compares the divstep impl in this crate (BCH^4MWWY EUROCRYPT 2026 port of
//! libsecp256k1's `secp256k1_modinv64`) against each upstream library's
//! built-in inverse for the same prime.  ONLY constant-time references are
//! included; the following are deliberately excluded:
//!
//!  - arkworks 0.4 (ark-{bn254,bls12-377,bls12-381}): uses BEA (Algorithm 16
//!    Guajardo–Kumar–Paar–Pelzl, ark-ff/montgomery_backend.rs:295).
//!    Data-dependent `while u.is_even()` loops → NOT constant-time.
//!  - rust-secp256k1 0.30 + secp256k1-sys: doesn't expose `Scalar::inverse`.
//!    We use `k256` (RustCrypto, Fermat addition chain) for secp256k1 CT.
//!  - ring 0.17: doesn't expose modular inverse.
//!  - OpenSSL BN_mod_inverse: variable-time (paper Table 1.2.1).
//!
//! CT references INCLUDED (curve → impl):
//!  - secp256k1  → k256::FieldElement::invert     (Fermat addition chain)
//!  - P-224      → p224::FieldElement::invert     (Fermat addition chain)
//!  - P-256      → p256::FieldElement::invert     (Fermat addition chain)
//!  - P-384      → p384::FieldElement::invert     (Fermat addition chain)
//!  - P-521      → p521::FieldElement::invert     (Fermat addition chain)
//!  - Pallas     → pasta_curves::Fp::invert       (pow_vartime over public p-2)
//!  - Vesta      → pasta_curves::Fq::invert       (pow_vartime over public p-2)
//!  - BLS12-381  → bls12_381::Fp::invert          (zkcrypto, Fermat chain)
//!                + blst::blst_fp_inverse         (hand-tuned asm)
//!                + blst::blst_fp_eucl_inverse    (classical Euclidean)
//!
//! Note on `pow_vartime`: the name refers to vartime-over-exponent.  For
//! invert the exponent is the PUBLIC constant `p-2`, so the function is
//! CT over the secret input — same situation as p256's fixed addition chain.

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use ff::Field as _;

use curve25519_jasmin::safegcd_bls12_381::bls12_invert_divstep_sat;
use curve25519_jasmin::safegcd_bn254::bn254_invert_divstep_sat;
use curve25519_jasmin::safegcd_p256::p256_invert_divstep_sat;
use curve25519_jasmin::safegcd_p384::p384_invert_divstep_sat;
use curve25519_jasmin::safegcd_pallas::pallas_invert_divstep_sat;
use curve25519_jasmin::safegcd_secp256k1::secp_invert_divstep_sat;
use curve25519_jasmin::safegcd_vesta::vesta_invert_divstep_sat;

fn input_bytes_32() -> [u8; 32] {
    let mut bs = [0u8; 32];
    for (i, b) in bs.iter_mut().enumerate() {
        *b = (i as u8).wrapping_mul(7) | 1;
    }
    bs[31] &= 0x7f;
    bs
}

fn bytes_to_u4_le(bs: &[u8; 32]) -> [u64; 4] {
    let mut x = [0u64; 4];
    for i in 0..4 {
        x[i] = u64::from_le_bytes([
            bs[8 * i],
            bs[8 * i + 1],
            bs[8 * i + 2],
            bs[8 * i + 3],
            bs[8 * i + 4],
            bs[8 * i + 5],
            bs[8 * i + 6],
            bs[8 * i + 7],
        ]);
    }
    x
}

fn bench(c: &mut Criterion) {
    let bs32 = input_bytes_32();
    let x4 = bytes_to_u4_le(&bs32);

    let mut g = c.benchmark_group("vs_production_ct");
    g.sample_size(200);

    // ─── secp256k1 base field ─────────────────────────────────────────────
    // OURS
    let mut secp_x = x4;
    secp_x[3] &= 0x7FFF_FFFF_FFFF_FFFF;
    g.bench_function("secp256k1_OURS_divstep", |b| {
        let mut out = [0u64; 4];
        b.iter(|| secp_invert_divstep_sat(&mut out, black_box(&secp_x)));
    });
    // k256 (Fermat addition chain)
    let mut be_secp = bs32;
    be_secp.reverse();
    be_secp[0] &= 0x7f;
    let secp_fe = k256::FieldElement::from_bytes(&be_secp.into()).unwrap();
    g.bench_function("secp256k1_k256_FermatChain", |b| {
        b.iter(|| {
            let r = black_box(&secp_fe).invert();
            black_box(r);
        });
    });

    // ─── P-256 base field ─────────────────────────────────────────────────
    g.bench_function("p256_OURS_divstep", |b| {
        let mut out = [0u64; 4];
        b.iter(|| p256_invert_divstep_sat(&mut out, black_box(&secp_x)));
    });
    let p256_fe = {
        let mut be = bs32;
        be.reverse();
        be[0] = 0; // ensure < p256 prime
        p256::FieldElement::from_bytes(&be.into()).unwrap()
    };
    g.bench_function("p256_RustCrypto_FermatChain", |b| {
        b.iter(|| {
            let r = black_box(&p256_fe).invert();
            black_box(r);
        });
    });

    // P-224 / P-521: RustCrypto crates DO NOT expose FieldElement (no
    // `expose-field` feature in 0.13.x).  Their `Scalar` is at a different
    // prime than our divstep impl targets — omitted to keep comparison fair.

    // ─── P-384 ────────────────────────────────────────────────────────────
    // OURS — 6×u64.
    let p384_x: [u64; 6] = [
        x4[0], x4[1], x4[2], x4[3],
        0x0123_4567_89ab_cdef,
        0x0011_2233_4455_6677,
    ];
    g.bench_function("p384_OURS_divstep", |b| {
        let mut out = [0u64; 6];
        b.iter(|| p384_invert_divstep_sat(&mut out, black_box(&p384_x)));
    });
    let p384_fe = {
        let mut be = [0u8; 48];
        for i in 0..48 {
            be[i] = ((i as u8).wrapping_mul(7) | 1) & if i == 0 { 0x7f } else { 0xff };
        }
        p384::FieldElement::from_bytes(&be.into()).unwrap()
    };
    g.bench_function("p384_RustCrypto_FermatChain", |b| {
        b.iter(|| {
            let r = black_box(&p384_fe).invert();
            black_box(r);
        });
    });

    // ─── Pallas Fp ────────────────────────────────────────────────────────
    let mut pallas_x = x4;
    pallas_x[3] &= 0x3FFF_FFFF_FFFF_FFFF;
    g.bench_function("pallas_OURS_divstep", |b| {
        let mut out = [0u64; 4];
        b.iter(|| pallas_invert_divstep_sat(&mut out, black_box(&pallas_x)));
    });
    let pallas_fe = pasta_curves::Fp::from_raw(pallas_x);
    g.bench_function("pallas_Pasta_FermatChain", |b| {
        b.iter(|| {
            let r = black_box(&pallas_fe).invert();
            black_box(r);
        });
    });

    // ─── Vesta Fq ─────────────────────────────────────────────────────────
    let mut vesta_x = x4;
    vesta_x[3] &= 0x3FFF_FFFF_FFFF_FFFF;
    g.bench_function("vesta_OURS_divstep", |b| {
        let mut out = [0u64; 4];
        b.iter(|| vesta_invert_divstep_sat(&mut out, black_box(&vesta_x)));
    });
    let vesta_fe = pasta_curves::Fq::from_raw(vesta_x);
    g.bench_function("vesta_Pasta_FermatChain", |b| {
        b.iter(|| {
            let r = black_box(&vesta_fe).invert();
            black_box(r);
        });
    });

    // ─── BLS12-381 base field ─────────────────────────────────────────────
    let bls12_x: [u64; 6] = [
        x4[0],
        x4[1],
        x4[2],
        x4[3] & 0x0FFF_FFFF_FFFF_FFFF,
        0x0123_4567_89ab_cdef,
        0x0011_2233_4455_6677,
    ];
    g.bench_function("bls12_381_OURS_divstep", |b| {
        let mut out = [0u64; 6];
        b.iter(|| bls12_invert_divstep_sat(&mut out, black_box(&bls12_x)));
    });
    // zkcrypto bls12_381 doesn't re-export `Fp` (it lives in `mod fp;` →
    // private).  Their only exposed CT inverter is `Scalar::invert` over Fr,
    // a different prime; not directly comparable to our Fp divstep — skip.
    // blst (hand-tuned asm)
    let blst_input = blst::blst_fp { l: bls12_x };
    g.bench_function("bls12_381_blst_asm_inverse", |b| {
        let mut out = blst::blst_fp { l: [0; 6] };
        b.iter(|| unsafe { blst::blst_fp_inverse(&mut out, black_box(&blst_input)) });
    });
    g.bench_function("bls12_381_blst_eucl_inverse", |b| {
        let mut out = blst::blst_fp { l: [0; 6] };
        b.iter(|| unsafe { blst::blst_fp_eucl_inverse(&mut out, black_box(&blst_input)) });
    });

    // ─── BN254 ────────────────────────────────────────────────────────────
    // Our impl only — no CT BN254 production reference (arkworks excluded).
    let mut bn_x = x4;
    bn_x[3] &= 0x0FFF_FFFF_FFFF_FFFF;
    g.bench_function("bn254_OURS_divstep_noref", |b| {
        let mut out = [0u64; 4];
        b.iter(|| bn254_invert_divstep_sat(&mut out, black_box(&bn_x)));
    });

    g.finish();
}

criterion_group!(benches, bench);
criterion_main!(benches);
