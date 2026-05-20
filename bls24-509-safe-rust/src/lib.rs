//! BLS24-509 field arithmetic — fiat-rust leaves + Bernstein-Yang inverse.
//!
//! Field operations (add, sub, mul, square, opp, to/from Montgomery,
//! to/from bytes) come from the auto-generated, machine-checked
//! `fiat-crypto/fiat-rust/src/bls24_509_64.rs`.  Constant-time modular
//! inversion comes from the Bernstein-Yang divstep port in
//! `safegcd-rs/src/safegcd_bls24_509.rs` (verified against the
//! convergence certificate in
//! `src/Arithmetic/safegcd/divsteps_bls24_509_half.v`).
//!
//! 509-bit prime, 8×u64 saturated limb representation.
//! Curve seed z = -0x800000ffff801.

#![allow(non_snake_case, non_camel_case_types)]

pub use fiat_crypto::bls24_509_64::fiat_bls24_509_montgomery_domain_field_element as Fp;
pub use fiat_crypto::bls24_509_64::fiat_bls24_509_non_montgomery_domain_field_element as FpRaw;

use fiat_crypto::bls24_509_64::*;

#[inline] pub fn fp_add(out: &mut Fp, x: &Fp, y: &Fp)     { fiat_bls24_509_add(out, x, y) }
#[inline] pub fn fp_sub(out: &mut Fp, x: &Fp, y: &Fp)     { fiat_bls24_509_sub(out, x, y) }
#[inline] pub fn fp_mul(out: &mut Fp, x: &Fp, y: &Fp)     { fiat_bls24_509_mul(out, x, y) }
#[inline] pub fn fp_square(out: &mut Fp, x: &Fp)          { fiat_bls24_509_square(out, x) }
#[inline] pub fn fp_opp(out: &mut Fp, x: &Fp)             { fiat_bls24_509_opp(out, x) }
#[inline] pub fn fp_to_bytes(out: &mut [u8; 509/8 + (509%8>0) as usize], x: &Fp) {
    fiat_bls24_509_to_bytes(out, &x.0)
}
#[inline] pub fn fp_from_bytes(out: &mut FpRaw, bs: &[u8; 509/8 + (509%8>0) as usize]) {
    fiat_bls24_509_from_bytes(&mut out.0, bs)
}
#[inline] pub fn fp_to_montgomery(out: &mut Fp, x: &FpRaw)    { fiat_bls24_509_to_montgomery(out, x) }
#[inline] pub fn fp_from_montgomery(out: &mut FpRaw, x: &Fp)  { fiat_bls24_509_from_montgomery(out, x) }

/// Constant-time modular inverse via the Bernstein–Yang divstep port.
/// Input/output are in Montgomery form.  Convert out → invert → convert in.
pub fn fp_inv(out: &mut Fp, x: &Fp) {
    let mut raw_in = FpRaw([0u64; 8]);
    fp_from_montgomery(&mut raw_in, x);
    let mut raw_inv = [0u64; 8];
    safegcd::safegcd_bls24_509::bls24_invert_divstep_sat(&mut raw_inv, &raw_in.0);
    fp_to_montgomery(out, &FpRaw(raw_inv));
}

/// Bernstein–Yang raw inverse on canonical 8×u64 limbs (NOT in
/// Montgomery form).
pub fn invert_raw(out: &mut [u64; 8], x: &[u64; 8]) {
    safegcd::safegcd_bls24_509::bls24_invert_divstep_sat(out, x);
}

// Safe tower extraction pipeline IS wired (see
// src/Bedrock/ExtractSafeTowerBLS24_509.v + bls24_509_safe_tower_main.ml);
// generated/bls24_509_safe_tower.rs has 58 functions across Fp2/Fp4/Fp8/
// Fp24.  BLOCKED: the aggregated BLS24_509_Extract.bls24_all_funcs list
// is missing helpers needed by the emitted Rust:
//   - bls24_509_one, bls24_509_zero (Fp constructors)
//   - bls24_Fp4_inv, bls24_Fp8_inv (intermediate-tower inverses)
//   - bls24_Fp2_mul_by_nr type mismatch (called with &Fp; expects &Fp2)
// Need to extend bls24_all_funcs in BLS24_509_Extract.v to cover these.
// For now the tower mod is NOT included; the field-op wrapper above is
// the linkable surface.

#[cfg(test)]
mod kat;
