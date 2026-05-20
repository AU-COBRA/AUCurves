//! BLS24-509 base field Fp + pairing tower
//!
//! SKELETON — see ../PENDING.md.  Needs Rocq extraction of the full Fp2/Fp4/Fp8/Fp24 pairing tower.
//!
//! The Bernstein–Yang constant-time inverse IS available (it doesn't
//! depend on Montgomery field ops), exposed below as
//! `invert_raw`.  Verified against
//! `src/Arithmetic/safegcd/divsteps_bls24_509_half.v`.

#![allow(non_snake_case, dead_code)]

/// Constant-time modular inverse on raw saturated little-endian limbs.
/// Returns `x^-1 mod p` in the same limb format.  8×u64.
pub fn invert_raw(out: &mut [u64; 8], x: &[u64; 8]) {
    safegcd::safegcd_bls24_509::bls24_invert_divstep_sat(out, x);
}
