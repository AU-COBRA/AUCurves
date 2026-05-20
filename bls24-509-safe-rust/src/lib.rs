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
// generated/bls24_509_safe_tower.rs has 58 functions across the BLS24
// Fp2/Fp4/Fp8/Fp24 tower.  BLOCKED at a deeper level than missing
// aggregator entries:
//
//  (1) ToSafeRustBody.v's type-inference (type_of_bytes / field_path /
//      type_rank / drill / descend / base_type_of_name / type_decls)
//      hardcodes the BLS12-style tower Fp/Fp2/Fp6/Fp12.  BLS24 uses
//      Fp/Fp2/Fp4/Fp8/Fp24.  Result: all bls24_Fp4_*, bls24_Fp8_*,
//      bls24_Fp24_* functions are emitted with `&mut Fp` parameters
//      instead of the correct tower type, and bls24_Fp24_inv reads
//      `.c8`/`.c16` fields that the (BLS12) Fp2 type doesn't have.
//
//  (2) bls24_Fp4_inv and bls24_Fp8_inv exist only as `spec_of` instances
//      in BLS24_509_MillerLoop_proof.v — no `Definition` of an actual
//      bedrock2 body.  Compare to bls12_377_Fp2.v which has a closed
//      hand-written Fp2_inv using the norm trick.  BLS24 needs the same
//      for Fp4 (norm into Fp2, base inv on the norm) and Fp8 (norm into
//      Fp4, recursive).
//
//  (3) The aggregator bls24_all_funcs duplicates the base-Fp ops
//      (bls24_509_add etc.) which collide with the extern-C leaf
//      wrappers emitted by bls24_509_safe_tower_main.ml.
//
//  (4) bls24_509_one / bls24_509_zero are called by Fp2 zero/one bodies
//      but the leaf wrapper block only declares add/sub/mul/square/opp/
//      felem_copy/from_word/select_znz/inv.
//
// Until ToSafeRustBody.v is generalised over the tower shape (or a
// BLS24-specific variant is forked), the generated file cannot link.
// Field-op wrapper above remains the linkable surface.

#[cfg(test)]
mod kat;
