//! BLS12-377 base field Fp + pairing tower
//!
//! SKELETON — see ../PENDING.md.  Needs Rocq extraction of the full Fp2/Fp6/Fp12 pairing tower (see bn256-safe-rust for the pattern).
//!
//! The Bernstein–Yang constant-time inverse IS available (it doesn't
//! depend on Montgomery field ops), exposed below as
//! `invert_raw`.  Verified against
//! `src/Arithmetic/safegcd/divsteps_bls12_381_half.v`.

#![allow(non_snake_case, dead_code)]

/// Constant-time modular inverse on raw saturated little-endian limbs.
/// Returns `x^-1 mod p` in the same limb format.  6×u64.
pub fn invert_raw(out: &mut [u64; 6], x: &[u64; 6]) {
    safegcd::safegcd_bls12_381::bls12_invert_divstep_sat(out, x);
}
