//! BW6-761 field arithmetic — fiat-rust leaves + Bernstein-Yang inverse.
//!
//! Field operations (add, sub, mul, square, opp, to/from Montgomery,
//! to/from bytes) come from the auto-generated, machine-checked
//! `fiat-crypto/fiat-rust/src/bw6_761_64.rs`.  Constant-time modular
//! inversion comes from the Bernstein-Yang divstep port in
//! `safegcd-rs/src/safegcd_bw6_761.rs` (verified against the
//! convergence certificate in
//! `src/Arithmetic/safegcd/divsteps_bw6_761_half.v`).
//!
//! 761-bit prime, 12×u64 saturated limb representation.

#![allow(non_snake_case, non_camel_case_types)]

pub use fiat_crypto::bw6_761_64::fiat_bw6_761_montgomery_domain_field_element as Fp;
pub use fiat_crypto::bw6_761_64::fiat_bw6_761_non_montgomery_domain_field_element as FpRaw;

use fiat_crypto::bw6_761_64::*;

#[inline] pub fn fp_add(out: &mut Fp, x: &Fp, y: &Fp)     { fiat_bw6_761_add(out, x, y) }
#[inline] pub fn fp_sub(out: &mut Fp, x: &Fp, y: &Fp)     { fiat_bw6_761_sub(out, x, y) }
#[inline] pub fn fp_mul(out: &mut Fp, x: &Fp, y: &Fp)     { fiat_bw6_761_mul(out, x, y) }
#[inline] pub fn fp_square(out: &mut Fp, x: &Fp)          { fiat_bw6_761_square(out, x) }
#[inline] pub fn fp_opp(out: &mut Fp, x: &Fp)             { fiat_bw6_761_opp(out, x) }
#[inline] pub fn fp_to_bytes(out: &mut [u8; 761/8 + (761%8>0) as usize], x: &Fp) {
    fiat_bw6_761_to_bytes(out, &x.0)
}
#[inline] pub fn fp_from_bytes(out: &mut FpRaw, bs: &[u8; 761/8 + (761%8>0) as usize]) {
    fiat_bw6_761_from_bytes(&mut out.0, bs)
}
#[inline] pub fn fp_to_montgomery(out: &mut Fp, x: &FpRaw)    { fiat_bw6_761_to_montgomery(out, x) }
#[inline] pub fn fp_from_montgomery(out: &mut FpRaw, x: &Fp)  { fiat_bw6_761_from_montgomery(out, x) }

/// Constant-time modular inverse via the Bernstein–Yang divstep port.
/// Input/output are in Montgomery form.  Convert out → invert → convert in.
pub fn fp_inv(out: &mut Fp, x: &Fp) {
    let mut raw_in = FpRaw([0u64; 12]);
    fp_from_montgomery(&mut raw_in, x);
    let mut raw_inv = [0u64; 12];
    safegcd::safegcd_bw6_761::bw6_761_invert_divstep_sat(&mut raw_inv, &raw_in.0);
    fp_to_montgomery(out, &FpRaw(raw_inv));
}

/// Bernstein–Yang raw inverse on canonical 12×u64 limbs (NOT in
/// Montgomery form).
pub fn invert_raw(out: &mut [u64; 12], x: &[u64; 12]) {
    safegcd::safegcd_bw6_761::bw6_761_invert_divstep_sat(out, x);
}

#[cfg(test)]
mod kat;
