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

pub mod group;
pub mod extracted_leaves;

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

/// Constant-time modular inverse via the Bernstein–Yang divstep port.
/// P-521 uses Solinas form so we round-trip through bytes to/from the
/// 9×u64 saturated representation safegcd expects.
pub fn fp_inv(out: &mut FpT, x: &FpT) {
    // tight -> bytes -> 9 saturated u64 little-endian limbs
    let mut bytes_in = [0u8; 66];
    fp_to_bytes(&mut bytes_in, x);
    let mut sat_in = [0u64; 9];
    for i in 0..8 {
        sat_in[i] = u64::from_le_bytes(bytes_in[8*i..8*i+8].try_into().unwrap());
    }
    // 9th limb holds the top 2 bytes (= 521 % 64 = 9 bits) of the prime.
    sat_in[8] = u64::from(bytes_in[64]) | (u64::from(bytes_in[65]) << 8);

    let mut sat_inv = [0u64; 9];
    safegcd::safegcd_p521::p521_invert_divstep_sat(&mut sat_inv, &sat_in);

    // Re-pack to 66 LE bytes, then from_bytes.
    let mut bytes_out = [0u8; 66];
    for i in 0..8 {
        bytes_out[8*i..8*i+8].copy_from_slice(&sat_inv[i].to_le_bytes());
    }
    bytes_out[64] = (sat_inv[8] & 0xff) as u8;
    bytes_out[65] = ((sat_inv[8] >> 8) & 0xff) as u8;
    fp_from_bytes(out, &bytes_out);
}

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

    #[test]
    fn invert_roundtrip() {
        // Construct a non-trivial tight element via from_bytes.
        let mut bytes = [0u8; 66];
        for i in 0..64 { bytes[i] = ((i as u8).wrapping_mul(7)) | 1; }
        bytes[64] = 0x01;
        bytes[65] = 0x00;
        let mut a = zero_t();
        fp_from_bytes(&mut a, &bytes);

        let mut a_inv = zero_t();
        fp_inv(&mut a_inv, &a);

        // a * a^-1 should reduce to 1.  Cross-check via to_bytes canonical form.
        let mut a_loose = zero_l(); fp_relax(&mut a_loose, &a);
        let mut inv_loose = zero_l(); fp_relax(&mut inv_loose, &a_inv);
        let mut prod_tight = zero_t();
        fp_carry_mul(&mut prod_tight, &a_loose, &inv_loose);
        let mut prod_bytes = [0u8; 66];
        fp_to_bytes(&mut prod_bytes, &prod_tight);

        let mut expected_one = [0u8; 66];
        expected_one[0] = 1;
        assert_eq!(prod_bytes, expected_one, "a * a^-1 should equal 1 in canonical bytes");
    }
}
