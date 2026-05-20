//! P-521 field arithmetic — fiat-rust Solinas leaves.
//!
//! P-521 uses the Solinas prime `2^521 - 1`, so fiat-rust emits an
//! unsaturated representation: a *tight* limb form for stable values
//! and a *loose* form for intermediates that may carry beyond 58 bits.
//! `carry` brings a loose value back to tight; `relax` widens tight to
//! loose.  Mul/square take loose inputs and produce tight outputs
//! (`carry_mul`); add/sub/opp take tight and produce loose.
//!
//! Constant-time inversion lives in
//! `../curve25519-jasmin-rs/src/safegcd_p521.rs` (verified against
//! `src/Arithmetic/safegcd/divsteps_p521_half.v`).

#![allow(non_snake_case, non_camel_case_types)]

pub use fiat_crypto::p521_64::fiat_p521_tight_field_element  as FpT;
pub use fiat_crypto::p521_64::fiat_p521_loose_field_element  as FpL;

use fiat_crypto::p521_64::*;

#[inline] pub fn fp_carry_mul(out: &mut FpT, x: &FpL, y: &FpL) { fiat_p521_carry_mul(out, x, y) }
#[inline] pub fn fp_carry_square(out: &mut FpT, x: &FpL)       { fiat_p521_carry_square(out, x) }
#[inline] pub fn fp_carry(out: &mut FpT, x: &FpL)              { fiat_p521_carry(out, x) }
#[inline] pub fn fp_relax(out: &mut FpL, x: &FpT)              { fiat_p521_relax(out, x) }
#[inline] pub fn fp_add(out: &mut FpL, x: &FpT, y: &FpT)       { fiat_p521_add(out, x, y) }
#[inline] pub fn fp_sub(out: &mut FpL, x: &FpT, y: &FpT)       { fiat_p521_sub(out, x, y) }
#[inline] pub fn fp_opp(out: &mut FpL, x: &FpT)                { fiat_p521_opp(out, x) }
#[inline] pub fn fp_to_bytes(out: &mut [u8; 66], x: &FpT)      { fiat_p521_to_bytes(out, x) }
#[inline] pub fn fp_from_bytes(out: &mut FpT, bs: &[u8; 66])   { fiat_p521_from_bytes(out, bs) }

#[cfg(test)]
mod kat {
    use super::*;
    fn zero_t() -> FpT { FpT([0u64; 9]) }
    fn zero_l() -> FpL { FpL([0u64; 9]) }

    fn one_t() -> FpT {
        let mut bs = [0u8; 66];
        bs[0] = 1;
        let mut t = zero_t();
        fp_from_bytes(&mut t, &bs);
        t
    }

    #[test]
    fn add_zero_identity() {
        let a = one_t();
        let mut out = zero_l();
        fp_add(&mut out, &a, &zero_t());
        let mut t = zero_t();
        fp_carry(&mut t, &out);
        assert_eq!(t.0, a.0);
    }

    #[test]
    fn sub_self_is_zero() {
        // Solinas sub returns `a - b + k*p` which after `carry` is reduced but
        // not necessarily canonical-zero in limbs; canonicalise via to_bytes.
        let a = one_t();
        let mut out = zero_l();
        fp_sub(&mut out, &a, &a);
        let mut t = zero_t();
        fp_carry(&mut t, &out);
        let mut bytes = [0u8; 66];
        fp_to_bytes(&mut bytes, &t);
        assert_eq!(bytes, [0u8; 66]);
    }

    #[test]
    fn mul_one_identity() {
        let a = one_t();
        let mut a_loose = zero_l();
        fp_relax(&mut a_loose, &a);
        let mut out = zero_t();
        fp_carry_mul(&mut out, &a_loose, &a_loose);  // 1 * 1 = 1
        assert_eq!(out.0, a.0);
    }
}
