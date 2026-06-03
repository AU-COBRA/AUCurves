//! C-ABI surface for the verified Pallas base-field leaves.
//!
//! These `extern "C"` symbols expose the machine-checked fiat-crypto
//! WordByWordMontgomery field operations (`fiat_pallas_*`, from
//! `fiat-crypto/fiat-rust/src/pallas_64.rs`) and the Bernstein-Yang
//! divstep constant-time inverse (`safegcd_pallas::pallas_invert_divstep_sat`)
//! so a C harness (the CatCrypt Halo2 Pasta MSM bench) can route its
//! Montgomery reduce and field inverse through the verified leaves
//! instead of hand-written CIOS / Fermat-ladder C glue.
//!
//! All field elements are 4×u64 little-endian, in the Montgomery domain
//! (`x·R mod p`, `R = 2^256`), matching fiat-crypto's `eval` convention
//! (`z[0] + z[1]<<64 + z[2]<<128 + z[3]<<192`).  The inverse converts out
//! of / back into the Montgomery domain internally, so its C contract is
//! the same as the multiply: Montgomery-in, Montgomery-out.

use crate::{Fp, FpRaw};
use fiat_crypto::pallas_64::{
    fiat_pallas_add, fiat_pallas_from_montgomery, fiat_pallas_mul, fiat_pallas_opp,
    fiat_pallas_square, fiat_pallas_sub, fiat_pallas_to_montgomery,
};

#[inline(always)]
unsafe fn ld(p: *const u64) -> [u64; 4] {
    [*p, *p.add(1), *p.add(2), *p.add(3)]
}
#[inline(always)]
unsafe fn st(p: *mut u64, v: &[u64; 4]) {
    *p = v[0];
    *p.add(1) = v[1];
    *p.add(2) = v[2];
    *p.add(3) = v[3];
}

/// `r = a * b * R^{-1} mod p` — the verified fiat WordByWordMontgomery
/// multiply (256×256 product + Montgomery reduce, machine-checked).
#[no_mangle]
pub unsafe extern "C" fn pallas_fp_mul(r: *mut u64, a: *const u64, b: *const u64) {
    let (xa, xb) = (Fp(ld(a)), Fp(ld(b)));
    let mut out = Fp([0u64; 4]);
    fiat_pallas_mul(&mut out, &xa, &xb);
    st(r, &out.0);
}

/// `r = a + b mod p` (Montgomery-linear), verified fiat.
#[no_mangle]
pub unsafe extern "C" fn pallas_fp_add(r: *mut u64, a: *const u64, b: *const u64) {
    let (xa, xb) = (Fp(ld(a)), Fp(ld(b)));
    let mut out = Fp([0u64; 4]);
    fiat_pallas_add(&mut out, &xa, &xb);
    st(r, &out.0);
}

/// `r = a - b mod p` (Montgomery-linear), verified fiat.
#[no_mangle]
pub unsafe extern "C" fn pallas_fp_sub(r: *mut u64, a: *const u64, b: *const u64) {
    let (xa, xb) = (Fp(ld(a)), Fp(ld(b)));
    let mut out = Fp([0u64; 4]);
    fiat_pallas_sub(&mut out, &xa, &xb);
    st(r, &out.0);
}

/// `r = a^2 * R^{-1} mod p`, verified fiat square.
#[no_mangle]
pub unsafe extern "C" fn pallas_fp_sqr(r: *mut u64, a: *const u64) {
    let xa = Fp(ld(a));
    let mut out = Fp([0u64; 4]);
    fiat_pallas_square(&mut out, &xa);
    st(r, &out.0);
}

/// `r = -a mod p`, verified fiat opp.
#[no_mangle]
pub unsafe extern "C" fn pallas_fp_opp(r: *mut u64, a: *const u64) {
    let xa = Fp(ld(a));
    let mut out = Fp([0u64; 4]);
    fiat_pallas_opp(&mut out, &xa);
    st(r, &out.0);
}

/// `r = a^{-1} mod p` — both operands in the Montgomery domain.
/// Routes through the Bernstein-Yang divstep constant-time inverse:
/// convert out of Montgomery, invert on saturated limbs, convert back in.
#[no_mangle]
pub unsafe extern "C" fn pallas_fp_inv(r: *mut u64, a: *const u64) {
    let xa = Fp(ld(a));
    let mut raw_in = FpRaw([0u64; 4]);
    fiat_pallas_from_montgomery(&mut raw_in, &xa);
    let mut raw_inv = [0u64; 4];
    safegcd::safegcd_pallas::pallas_invert_divstep_sat(&mut raw_inv, &raw_in.0);
    let mut out = Fp([0u64; 4]);
    fiat_pallas_to_montgomery(&mut out, &FpRaw(raw_inv));
    st(r, &out.0);
}

/// Convert a canonical (non-Montgomery) saturated 4×u64 to the Montgomery
/// domain: `r = a·R mod p`, verified fiat.
#[no_mangle]
pub unsafe extern "C" fn pallas_fp_to_mont(r: *mut u64, a: *const u64) {
    let raw = FpRaw(ld(a));
    let mut out = Fp([0u64; 4]);
    fiat_pallas_to_montgomery(&mut out, &raw);
    st(r, &out.0);
}

/// Convert a Montgomery-domain element back to canonical saturated form:
/// `r = a·R^{-1} mod p`, verified fiat.
#[no_mangle]
pub unsafe extern "C" fn pallas_fp_from_mont(r: *mut u64, a: *const u64) {
    let xa = Fp(ld(a));
    let mut out = FpRaw([0u64; 4]);
    fiat_pallas_from_montgomery(&mut out, &xa);
    st(r, &out.0);
}

/// `r = a^{-1} mod p` on raw saturated little-endian limbs (not Montgomery):
/// the bare Bernstein-Yang divstep leaf, for the `inv·x == 1 mod p` KAT.
#[no_mangle]
pub unsafe extern "C" fn pallas_invert_sat(r: *mut u64, a: *const u64) {
    let xin = ld(a);
    let mut out = [0u64; 4];
    safegcd::safegcd_pallas::pallas_invert_divstep_sat(&mut out, &xin);
    st(r, &out);
}
