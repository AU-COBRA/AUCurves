//! Vesta (Pasta) base field arithmetic — fiat-rust leaves + Bernstein-Yang inverse.
//!
//! Field operations (add, sub, mul, square, opp, to/from Montgomery,
//! to/from bytes) come from the auto-generated, machine-checked
//! `fiat-crypto/fiat-rust/src/vesta_64.rs`.  Constant-time modular
//! inversion comes from the Bernstein-Yang divstep port in
//! `safegcd-rs/src/safegcd_vesta.rs` (verified against the
//! convergence certificate in
//! `src/Arithmetic/safegcd/divsteps_vesta_half.v`).
//!
//! 255-bit prime, 4×u64 saturated limb representation.
//! Prime q = 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001.

#![allow(non_snake_case, non_camel_case_types)]

pub use fiat_crypto::vesta_64::fiat_vesta_montgomery_domain_field_element as Fp;
pub use fiat_crypto::vesta_64::fiat_vesta_non_montgomery_domain_field_element as FpRaw;

use fiat_crypto::vesta_64::*;

#[inline] pub fn fp_add(out: &mut Fp, x: &Fp, y: &Fp)     { fiat_vesta_add(out, x, y) }
#[inline] pub fn fp_sub(out: &mut Fp, x: &Fp, y: &Fp)     { fiat_vesta_sub(out, x, y) }
#[inline] pub fn fp_mul(out: &mut Fp, x: &Fp, y: &Fp)     { fiat_vesta_mul(out, x, y) }
#[inline] pub fn fp_square(out: &mut Fp, x: &Fp)          { fiat_vesta_square(out, x) }
#[inline] pub fn fp_opp(out: &mut Fp, x: &Fp)             { fiat_vesta_opp(out, x) }
#[inline] pub fn fp_to_bytes(out: &mut [u8; 256/8 + (256%8>0) as usize], x: &Fp) {
    fiat_vesta_to_bytes(out, &x.0)
}
#[inline] pub fn fp_from_bytes(out: &mut FpRaw, bs: &[u8; 256/8 + (256%8>0) as usize]) {
    fiat_vesta_from_bytes(&mut out.0, bs)
}
#[inline] pub fn fp_to_montgomery(out: &mut Fp, x: &FpRaw)    { fiat_vesta_to_montgomery(out, x) }
#[inline] pub fn fp_from_montgomery(out: &mut FpRaw, x: &Fp)  { fiat_vesta_from_montgomery(out, x) }

/// Constant-time modular inverse via the Bernstein–Yang divstep port.
/// Input/output are in Montgomery form.  Convert out → invert → convert in.
pub fn fp_inv(out: &mut Fp, x: &Fp) {
    let mut raw_in = FpRaw([0u64; 4]);
    fp_from_montgomery(&mut raw_in, x);
    let mut raw_inv = [0u64; 4];
    safegcd::safegcd_vesta::vesta_invert_divstep_sat(&mut raw_inv, &raw_in.0);
    fp_to_montgomery(out, &FpRaw(raw_inv));
}

/// Constant-time modular inverse on raw saturated little-endian limbs.
/// Same low-level entry point that was exposed by the earlier skeleton.
pub fn invert_raw(out: &mut [u64; 4], x: &[u64; 4]) {
    safegcd::safegcd_vesta::vesta_invert_divstep_sat(out, x);
}

#[cfg(test)]
mod kat;
