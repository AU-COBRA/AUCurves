//! BW6-761 base field Fp + pairing tower
//!
//! SKELETON — see ../PENDING.md.  Needs Rocq extraction of the full Fp3/Fp6 pairing tower.
//!
//! The Bernstein–Yang constant-time inverse IS available (it doesn't
//! depend on Montgomery field ops), exposed below as
//! `invert_raw`.  Verified against
//! `src/Arithmetic/safegcd/divsteps_bw6_761_half.v`.

#![allow(non_snake_case, dead_code)]

/// Constant-time modular inverse on raw saturated little-endian limbs.
/// Returns `x^-1 mod p` in the same limb format.  12×u64.
pub fn invert_raw(out: &mut [u64; 12], x: &[u64; 12]) {
    safegcd::safegcd_bw6_761::bw6_761_invert_divstep_sat(out, x);
}
