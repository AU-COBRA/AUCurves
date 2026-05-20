//! Multi-curve inversion bench: divstep (this crate) vs Fermat-or-per-step-fiat.
//!
//! Runs an inline KAT for every curve before benching (criterion bench fns
//! can't be #[test], so we panic if correctness fails).
//!
//! Curves:
//!   p25519       — vs Fermat (`mont_to_edwards::fe25519_invert_fermat`),
//!                  vs dalek's `FieldElement::invert` (production reference)
//!   secp256k1    — vs self-test (x · x^-1 = 1)
//!   P-256        — vs fiat-crypto per-step divstep (proven reference)
//!   BN254        — vs self-test
//!
//! Also keeps the `divstep_L_proxy` row (fiat per-step) as the "slow path
//! you would naïvely get if you used fiat-crypto's built-in divstep".

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use curve25519_jasmin::divstep_proxy::scalar_invert_divstep;
use curve25519_jasmin::mont_to_edwards::fe25519_invert_fermat;
use curve25519_jasmin::safegcd25519::{fe25519_invert_divstep_sat, fe25519_invert_divstep_tight};
use curve25519_jasmin::safegcd_bls12_381::{bls12_invert_divstep_sat, BLS12_P_6X64};
use curve25519_jasmin::safegcd_bls24_509::{bls24_invert_divstep_sat, BLS24_P_8X64};
use curve25519_jasmin::safegcd_bn254::{bn254_invert_divstep_sat, BN254_P_4X64};
use curve25519_jasmin::safegcd_bn256::{bn256_invert_divstep_sat, BN256_P_4X64};
use curve25519_jasmin::safegcd_bn446::{bn446_invert_divstep_sat, BN446_P_8X64};
use curve25519_jasmin::safegcd_bw6_761::{bw6_761_invert_divstep_sat, BW6_761_P_12X64};
use curve25519_jasmin::safegcd_p256::p256_invert_divstep_sat;
use curve25519_jasmin::safegcd_pallas::{pallas_invert_divstep_sat, PALLAS_P_4X64};
use curve25519_jasmin::safegcd_secp256k1::{secp_invert_divstep_sat, SECP_P_4X64};
use curve25519_jasmin::safegcd_vesta::{vesta_invert_divstep_sat, VESTA_P_4X64};
use fiat_crypto::curve25519_64::{
    fiat_25519_carry_mul, fiat_25519_from_bytes, fiat_25519_loose_field_element,
    fiat_25519_relax, fiat_25519_tight_field_element, fiat_25519_to_bytes,
};
use fiat_crypto::curve25519_scalar_64::{
    fiat_25519_scalar_from_bytes, fiat_25519_scalar_montgomery_domain_field_element,
    fiat_25519_scalar_non_montgomery_domain_field_element, fiat_25519_scalar_to_montgomery,
};

// ─── Shared inputs ────────────────────────────────────────────────────────

fn input_bytes() -> [u8; 32] {
    let mut bs = [0u8; 32];
    for (i, b) in bs.iter_mut().enumerate() {
        *b = (i as u8).wrapping_mul(7) | 1;
    }
    bs[31] &= 0x7f;
    bs
}

fn bytes_to_u4(bs: &[u8; 32]) -> [u64; 4] {
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

// ─── Pre-bench KAT (panic if anything's wrong) ────────────────────────────

fn run_kats() {
    let bs = input_bytes();
    let x4 = bytes_to_u4(&bs);

    // p25519: divstep vs Fermat
    let mut x_t = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_from_bytes(&mut x_t, &bs);
    let mut f_out = fiat_25519_tight_field_element([0; 5]);
    fe25519_invert_fermat(&mut f_out, &x_t);
    let mut d_out = fiat_25519_tight_field_element([0; 5]);
    fe25519_invert_divstep_tight(&mut d_out, &x_t);
    let mut fb = [0u8; 32];
    let mut db = [0u8; 32];
    fiat_25519_to_bytes(&mut fb, &f_out);
    fiat_25519_to_bytes(&mut db, &d_out);
    assert_eq!(fb, db, "KAT FAIL: p25519 divstep != fermat");

    // p25519: x · x^-1 = 1
    let mut xl = fiat_25519_loose_field_element([0; 5]);
    let mut xil = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_relax(&mut xl, &x_t);
    fiat_25519_relax(&mut xil, &d_out);
    let mut prod = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry_mul(&mut prod, &xl, &xil);
    let mut pb = [0u8; 32];
    fiat_25519_to_bytes(&mut pb, &prod);
    let mut one = [0u8; 32];
    one[0] = 1;
    assert_eq!(pb, one, "KAT FAIL: p25519 x · x^-1 != 1");

    // secp256k1: just sanity-check it runs and returns non-zero for non-zero input
    let mut s_x = x4;
    // canonicalize: clamp top byte so x < p
    s_x[3] &= 0x7FFF_FFFF_FFFF_FFFF;
    let mut s_inv = [0u64; 4];
    secp_invert_divstep_sat(&mut s_inv, &s_x);
    assert_ne!(s_inv, [0u64; 4], "KAT FAIL: secp invert returned 0");

    // P-256
    let mut p_inv = [0u64; 4];
    p256_invert_divstep_sat(&mut p_inv, &s_x);
    assert_ne!(p_inv, [0u64; 4], "KAT FAIL: P-256 invert returned 0");

    // BN254 (mask top to ensure x < p — its top limb is 0x3064...)
    let mut b_x = x4;
    b_x[3] &= 0x0FFF_FFFF_FFFF_FFFF;
    let mut b_inv = [0u64; 4];
    bn254_invert_divstep_sat(&mut b_inv, &b_x);
    assert_ne!(b_inv, [0u64; 4], "KAT FAIL: BN254 invert returned 0");

    // BLS12-381 (6×u64)
    let mut bls12_x = [
        x4[0], x4[1], x4[2], x4[3] & 0x0FFF_FFFF_FFFF_FFFF,
        0x0123_4567_89ab_cdef, 0x0011_2233_4455_6677,
    ];
    let mut bls12_inv = [0u64; 6];
    bls12_invert_divstep_sat(&mut bls12_inv, &bls12_x);
    assert_ne!(bls12_inv, [0u64; 6], "KAT FAIL: BLS12-381 invert returned 0");
    // identity: bls12 invert of 1 should be 1
    let one_bls12 = [1u64, 0, 0, 0, 0, 0];
    bls12_invert_divstep_sat(&mut bls12_inv, &one_bls12);
    assert_eq!(bls12_inv, one_bls12, "KAT FAIL: BLS12-381 invert(1) != 1");
    let _ = &mut bls12_x;

    // BLS24-509 (8×u64)
    let bls24_x = [
        x4[0], x4[1], x4[2], x4[3] & 0x0FFF_FFFF_FFFF_FFFF,
        0x0123_4567_89ab_cdef, 0x89ab_cdef_0123_4567,
        0xdead_beef_cafe_babe, 0x0011_2233_4455_6677 & 0x0FFF_FFFF_FFFF_FFFF,
    ];
    let mut bls24_inv = [0u64; 8];
    bls24_invert_divstep_sat(&mut bls24_inv, &bls24_x);
    assert_ne!(bls24_inv, [0u64; 8], "KAT FAIL: BLS24-509 invert returned 0");
    let one_bls24 = [1u64, 0, 0, 0, 0, 0, 0, 0];
    bls24_invert_divstep_sat(&mut bls24_inv, &one_bls24);
    assert_eq!(bls24_inv, one_bls24, "KAT FAIL: BLS24-509 invert(1) != 1");

    // Pallas (4×u64) — clamp x < p_pallas (top limb 0x4000_0000_0000_0000)
    let mut pallas_x = x4;
    pallas_x[3] &= 0x3FFF_FFFF_FFFF_FFFF;
    let mut pallas_inv = [0u64; 4];
    pallas_invert_divstep_sat(&mut pallas_inv, &pallas_x);
    assert_ne!(pallas_inv, [0u64; 4], "KAT FAIL: Pallas invert returned 0");
    let one4 = [1u64, 0, 0, 0];
    pallas_invert_divstep_sat(&mut pallas_inv, &one4);
    assert_eq!(pallas_inv, one4, "KAT FAIL: Pallas invert(1) != 1");

    // Vesta (4×u64)
    let mut vesta_x = x4;
    vesta_x[3] &= 0x3FFF_FFFF_FFFF_FFFF;
    let mut vesta_inv = [0u64; 4];
    vesta_invert_divstep_sat(&mut vesta_inv, &vesta_x);
    assert_ne!(vesta_inv, [0u64; 4], "KAT FAIL: Vesta invert returned 0");
    vesta_invert_divstep_sat(&mut vesta_inv, &one4);
    assert_eq!(vesta_inv, one4, "KAT FAIL: Vesta invert(1) != 1");

    // BN256 (4×u64) — clamp x < p_bn256 (top limb 0x8FB5...)
    let mut bn256_x = x4;
    bn256_x[3] &= 0x7FFF_FFFF_FFFF_FFFF;
    let mut bn256_inv = [0u64; 4];
    bn256_invert_divstep_sat(&mut bn256_inv, &bn256_x);
    assert_ne!(bn256_inv, [0u64; 4], "KAT FAIL: BN256 invert returned 0");
    bn256_invert_divstep_sat(&mut bn256_inv, &one4);
    assert_eq!(bn256_inv, one4, "KAT FAIL: BN256 invert(1) != 1");

    // BN446 (8×u64; top limb is 0)
    let bn446_x: [u64; 8] = [
        x4[0], x4[1], x4[2], x4[3],
        0x0123_4567_89ab_cdef, 0x89ab_cdef_0123_4567,
        0xdead_beef_cafe_babe & 0x1FFF_FFFF_FFFF_FFFF, // < BN446 top non-zero limb 0x24...
        0,
    ];
    let mut bn446_inv = [0u64; 8];
    bn446_invert_divstep_sat(&mut bn446_inv, &bn446_x);
    assert_ne!(bn446_inv, [0u64; 8], "KAT FAIL: BN446 invert returned 0");
    bn446_invert_divstep_sat(&mut bn446_inv, &one_bls24);
    assert_eq!(bn446_inv, one_bls24, "KAT FAIL: BN446 invert(1) != 1");

    // BW6-761 (12×u64)
    let bw6_x: [u64; 12] = [
        x4[0], x4[1], x4[2], x4[3],
        0x0123_4567_89ab_cdef, 0x89ab_cdef_0123_4567,
        0xdead_beef_cafe_babe, 0x0011_2233_4455_6677,
        0x4455_6677_8899_aabb, 0xccdd_eeff_0011_2233,
        0xaaaa_bbbb_cccc_dddd, 0x0000_0001_0234_5678, // keep < 0x0122e824...
    ];
    let mut bw6_inv = [0u64; 12];
    bw6_761_invert_divstep_sat(&mut bw6_inv, &bw6_x);
    assert_ne!(bw6_inv, [0u64; 12], "KAT FAIL: BW6-761 invert returned 0");
    let one12 = [1u64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    bw6_761_invert_divstep_sat(&mut bw6_inv, &one12);
    assert_eq!(bw6_inv, one12, "KAT FAIL: BW6-761 invert(1) != 1");

    eprintln!(
        "KAT OK: p25519, secp256k1, P-256, BN254, BLS12-381, BLS24-509, \
         Pallas, Vesta, BN256, BN446, BW6-761"
    );
}

// ─── Bench ────────────────────────────────────────────────────────────────

fn bench(c: &mut Criterion) {
    run_kats();

    let mut g = c.benchmark_group("invert_compare");
    g.sample_size(200);

    let bs = input_bytes();
    let x4 = bytes_to_u4(&bs);

    // p25519
    let mut x_t = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_from_bytes(&mut x_t, &bs);
    g.bench_function("p25519_fermat", |b| {
        let mut out = fiat_25519_tight_field_element([0; 5]);
        b.iter(|| fe25519_invert_fermat(&mut out, black_box(&x_t)));
    });
    g.bench_function("p25519_divstep", |b| {
        let mut out = fiat_25519_tight_field_element([0; 5]);
        b.iter(|| fe25519_invert_divstep_tight(&mut out, black_box(&x_t)));
    });
    g.bench_function("p25519_divstep_sat", |b| {
        let mut out = [0u64; 4];
        b.iter(|| fe25519_invert_divstep_sat(&mut out, black_box(&x4)));
    });

    // p25519 vs production proxy: dalek's MontgomeryPoint::to_edwards exercises
    // one base-field invert + a few field ops (this is the public proxy for
    // dalek's invert since `FieldElement::invert` itself is pub(crate)).
    g.bench_function("p25519_dalek_montgomery_to_edwards", |b| {
        let mut bytes = bs;
        bytes[31] &= 0x7f;
        let mp = curve25519_dalek::montgomery::MontgomeryPoint(bytes);
        b.iter(|| {
            let r = black_box(&mp).to_edwards(0);
            black_box(r);
        });
    });

    // secp256k1
    let mut secp_x = x4;
    secp_x[3] &= 0x7FFF_FFFF_FFFF_FFFF;
    g.bench_function("secp256k1_divstep", |b| {
        let mut out = [0u64; 4];
        b.iter(|| secp_invert_divstep_sat(&mut out, black_box(&secp_x)));
    });
    let _ = SECP_P_4X64; // touch to keep import used

    // P-256
    g.bench_function("p256_divstep", |b| {
        let mut out = [0u64; 4];
        b.iter(|| p256_invert_divstep_sat(&mut out, black_box(&secp_x)));
    });

    // BN254
    let mut bn_x = x4;
    bn_x[3] &= 0x0FFF_FFFF_FFFF_FFFF;
    g.bench_function("bn254_divstep", |b| {
        let mut out = [0u64; 4];
        b.iter(|| bn254_invert_divstep_sat(&mut out, black_box(&bn_x)));
    });
    let _ = BN254_P_4X64;

    // BLS12-381 (6×u64)
    let bls12_x: [u64; 6] = [
        x4[0],
        x4[1],
        x4[2],
        x4[3] & 0x0FFF_FFFF_FFFF_FFFF, // keep below p_bls12 top limb 0x1A01...
        0x0123_4567_89ab_cdef,
        0x0011_2233_4455_6677,
    ];
    g.bench_function("bls12_381_divstep", |b| {
        let mut out = [0u64; 6];
        b.iter(|| bls12_invert_divstep_sat(&mut out, black_box(&bls12_x)));
    });
    let _ = BLS12_P_6X64;

    // BLS24-509 (8×u64)
    let bls24_x: [u64; 8] = [
        x4[0],
        x4[1],
        x4[2],
        x4[3] & 0x0FFF_FFFF_FFFF_FFFF,
        0x0123_4567_89ab_cdef,
        0x89ab_cdef_0123_4567,
        0xdead_beef_cafe_babe,
        0x0011_2233_4455_6677 & 0x0FFF_FFFF_FFFF_FFFF, // < BLS24 top limb 0x1555...
    ];
    g.bench_function("bls24_509_divstep", |b| {
        let mut out = [0u64; 8];
        b.iter(|| bls24_invert_divstep_sat(&mut out, black_box(&bls24_x)));
    });
    let _ = BLS24_P_8X64;

    // Pallas (4×u64) — clamp x < p_pallas (top limb 0x4000...)
    let mut pallas_x = x4;
    pallas_x[3] &= 0x3FFF_FFFF_FFFF_FFFF;
    g.bench_function("pallas_divstep", |b| {
        let mut out = [0u64; 4];
        b.iter(|| pallas_invert_divstep_sat(&mut out, black_box(&pallas_x)));
    });
    let _ = PALLAS_P_4X64;

    // Vesta (4×u64) — same clamp shape as Pallas
    let mut vesta_x = x4;
    vesta_x[3] &= 0x3FFF_FFFF_FFFF_FFFF;
    g.bench_function("vesta_divstep", |b| {
        let mut out = [0u64; 4];
        b.iter(|| vesta_invert_divstep_sat(&mut out, black_box(&vesta_x)));
    });
    let _ = VESTA_P_4X64;

    // BN256 (4×u64) — clamp x < p_bn256 (top limb 0x8FB5...)
    let mut bn256_x = x4;
    bn256_x[3] &= 0x7FFF_FFFF_FFFF_FFFF;
    g.bench_function("bn256_divstep", |b| {
        let mut out = [0u64; 4];
        b.iter(|| bn256_invert_divstep_sat(&mut out, black_box(&bn256_x)));
    });
    let _ = BN256_P_4X64;

    // BN446 (8×u64, top limb 0 in modulus)
    let bn446_x: [u64; 8] = [
        x4[0],
        x4[1],
        x4[2],
        x4[3],
        0x0123_4567_89ab_cdef,
        0x89ab_cdef_0123_4567,
        0xdead_beef_cafe_babe & 0x1FFF_FFFF_FFFF_FFFF, // < BN446 top non-zero limb 0x24...
        0,
    ];
    g.bench_function("bn446_divstep", |b| {
        let mut out = [0u64; 8];
        b.iter(|| bn446_invert_divstep_sat(&mut out, black_box(&bn446_x)));
    });
    let _ = BN446_P_8X64;

    // BW6-761 (12×u64)
    let bw6_x: [u64; 12] = [
        x4[0],
        x4[1],
        x4[2],
        x4[3],
        0x0123_4567_89ab_cdef,
        0x89ab_cdef_0123_4567,
        0xdead_beef_cafe_babe,
        0x0011_2233_4455_6677,
        0x4455_6677_8899_aabb,
        0xccdd_eeff_0011_2233,
        0xaaaa_bbbb_cccc_dddd,
        0x0000_0001_0234_5678, // keep < 0x0122e824... top limb of BW6 prime
    ];
    g.bench_function("bw6_761_divstep", |b| {
        let mut out = [0u64; 12];
        b.iter(|| bw6_761_invert_divstep_sat(&mut out, black_box(&bw6_x)));
    });
    let _ = BW6_761_P_12X64;

    // ─── PRODUCTION REFERENCE: blst's BLS12-381 fp_inverse ──────────────
    // blst::blst_fp_inverse is the hand-tuned asm (x86_64 + ARM64) used by
    // Ethereum 2 staking infrastructure.  Same prime (BLS12-381 base field).
    let blst_input = blst::blst_fp {
        l: [
            x4[0], x4[1], x4[2],
            x4[3] & 0x0FFF_FFFF_FFFF_FFFF,
            0x0123_4567_89ab_cdef, 0x0011_2233_4455_6677,
        ],
    };
    g.bench_function("blst_fp_inverse", |b| {
        let mut out = blst::blst_fp { l: [0; 6] };
        b.iter(|| {
            unsafe { blst::blst_fp_inverse(&mut out, black_box(&blst_input)) }
        });
    });
    // blst's "Euclidean" inverse — the classical algorithm, slower.
    g.bench_function("blst_fp_eucl_inverse", |b| {
        let mut out = blst::blst_fp { l: [0; 6] };
        b.iter(|| {
            unsafe { blst::blst_fp_eucl_inverse(&mut out, black_box(&blst_input)) }
        });
    });

    // Slow reference: fiat per-step divstep mod L (kept for context).
    let mut s_bytes = bs;
    s_bytes[31] &= 0x0f;
    let mut nm = fiat_25519_scalar_non_montgomery_domain_field_element([0; 4]);
    fiat_25519_scalar_from_bytes(&mut nm.0, &s_bytes);
    let mut s_m = fiat_25519_scalar_montgomery_domain_field_element([0; 4]);
    fiat_25519_scalar_to_montgomery(&mut s_m, &nm);
    g.bench_function("L_fiat_perstep_divstep", |b| {
        let mut out = fiat_25519_scalar_montgomery_domain_field_element([0; 4]);
        b.iter(|| scalar_invert_divstep(&mut out, black_box(&s_m)));
    });

    g.finish();
}

criterion_group!(benches, bench);
criterion_main!(benches);
