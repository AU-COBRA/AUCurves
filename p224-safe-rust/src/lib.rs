//! p224 field arithmetic — fiat-rust leaves + Bernstein-Yang inverse.
//!
//! Field operations (add, sub, mul, square, opp, to/from Montgomery,
//! to/from bytes) come from the auto-generated, machine-checked
//! `fiat-crypto/fiat-rust/src/p224_64.rs`.  Constant-time modular
//! inversion comes from the Bernstein-Yang divstep port in
//! `../curve25519-jasmin-rs/src/safegcd_p224.rs` (verified
//! against the convergence certificate in
//! `src/Arithmetic/safegcd/divsteps_p224_half.v`).
//!
//! 224-bit prime, 4×u64 saturated limb representation.

#![allow(non_snake_case, non_camel_case_types)]

pub use fiat_crypto::p224_64::fiat_p224_montgomery_domain_field_element as Fp;
pub use fiat_crypto::p224_64::fiat_p224_non_montgomery_domain_field_element as FpRaw;

use fiat_crypto::p224_64::*;

#[inline] pub fn fp_add(out: &mut Fp, x: &Fp, y: &Fp)     { fiat_p224_add(out, x, y) }
#[inline] pub fn fp_sub(out: &mut Fp, x: &Fp, y: &Fp)     { fiat_p224_sub(out, x, y) }
#[inline] pub fn fp_mul(out: &mut Fp, x: &Fp, y: &Fp)     { fiat_p224_mul(out, x, y) }
#[inline] pub fn fp_square(out: &mut Fp, x: &Fp)          { fiat_p224_square(out, x) }
#[inline] pub fn fp_opp(out: &mut Fp, x: &Fp)             { fiat_p224_opp(out, x) }
#[inline] pub fn fp_to_bytes(out: &mut [u8; 224/8 + (224%8>0) as usize], x: &Fp) {
    fiat_p224_to_bytes(out, &x.0)
}
#[inline] pub fn fp_from_bytes(out: &mut FpRaw, bs: &[u8; 224/8 + (224%8>0) as usize]) {
    fiat_p224_from_bytes(&mut out.0, bs)
}
#[inline] pub fn fp_to_montgomery(out: &mut Fp, x: &FpRaw)    { fiat_p224_to_montgomery(out, x) }
#[inline] pub fn fp_from_montgomery(out: &mut FpRaw, x: &Fp)  { fiat_p224_from_montgomery(out, x) }

#[cfg(test)]
mod kat;
