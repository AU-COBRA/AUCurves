//! Vesta (Pasta) base field — Fq
//!
//! SKELETON — see ../PENDING.md.  fiat-rust does not currently emit Pasta primes; needs a fresh extraction from the bedrock2 specs.
//!
//! The Bernstein–Yang constant-time inverse IS available (it doesn't
//! depend on Montgomery field ops), exposed below as
//! `invert_raw`.  Verified against
//! `src/Arithmetic/safegcd/divsteps_vesta_half.v`.

#![allow(non_snake_case, dead_code)]

/// Constant-time modular inverse on raw saturated little-endian limbs.
/// Returns `x^-1 mod p` in the same limb format.  4×u64.
pub fn invert_raw(out: &mut [u64; 4], x: &[u64; 4]) {
    safegcd::safegcd_vesta::vesta_invert_divstep_sat(out, x);
}
