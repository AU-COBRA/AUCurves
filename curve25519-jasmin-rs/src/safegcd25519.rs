//! Bernstein-Yang divstep modular inversion mod p25519 = 2^255 - 19.
//!
//! Thin curve-specific wrapper over the generic core in `safegcd.rs`.
//! See that module for algorithm details.  All curves use the same
//! Wuille structure (10 outer × 59 divsteps = 590 total, δ₀=1/2 via
//! `zeta = -1` encoding).
//!
//! Reference: libsecp256k1 `secp256k1_modinv64.c` (MIT, Dettman 2020),
//! retargeted from secp256k1 to p25519.

use crate::safegcd::{self as sg, ModInfo, Signed62};
use fiat_crypto::curve25519_64::{
    fiat_25519_from_bytes, fiat_25519_tight_field_element, fiat_25519_to_bytes,
};

/// `p25519^{-1} mod 2^62` — computed once at compile time.
const P25519_INV_62: u64 = sg::modinv_62(0x3FFF_FFFF_FFFF_FFED);

/// p25519 metadata.
pub const P25519: ModInfo<5> = ModInfo {
    modulus: [
        0x3FFF_FFFF_FFFF_FFEDi64,
        0x3FFF_FFFF_FFFF_FFFFi64,
        0x3FFF_FFFF_FFFF_FFFFi64,
        0x3FFF_FFFF_FFFF_FFFFi64,
        0x0000_0000_0000_007Fi64,
    ],
    modulus_inv_62: P25519_INV_62,
    outer_iters: 10, // 590 = 10·59 divsteps, paper §3.4 for δ₀=1/2 + b=256
};

/// Constant-time modular inversion mod p25519 on 4×u64 saturated input.
#[inline(never)]
pub fn fe25519_invert_divstep_sat(out: &mut [u64; 4], x: &[u64; 4]) {
    let x_lim: Signed62<5> = sg::from_saturated_4(x);
    let inv = sg::invert(x_lim, &P25519);
    *out = sg::to_saturated_4(&inv);
}

/// Wrapper matching the radix-2^51 (fiat tight) interface.
#[inline(never)]
pub fn fe25519_invert_divstep_tight(
    out: &mut fiat_25519_tight_field_element,
    a: &fiat_25519_tight_field_element,
) {
    let mut bytes = [0u8; 32];
    fiat_25519_to_bytes(&mut bytes, a);

    let mut x = [0u64; 4];
    for i in 0..4 {
        x[i] = u64::from_le_bytes([
            bytes[8 * i],
            bytes[8 * i + 1],
            bytes[8 * i + 2],
            bytes[8 * i + 3],
            bytes[8 * i + 4],
            bytes[8 * i + 5],
            bytes[8 * i + 6],
            bytes[8 * i + 7],
        ]);
    }

    let mut y = [0u64; 4];
    fe25519_invert_divstep_sat(&mut y, &x);

    let mut out_bytes = [0u8; 32];
    for i in 0..4 {
        out_bytes[8 * i..8 * i + 8].copy_from_slice(&y[i].to_le_bytes());
    }
    out_bytes[31] &= 0x7f;
    fiat_25519_from_bytes(out, &out_bytes);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mont_to_edwards::fe25519_invert_fermat as fermat;

    fn tight_from_bytes(bs: &[u8; 32]) -> fiat_25519_tight_field_element {
        let mut t = fiat_25519_tight_field_element([0; 5]);
        let mut b = *bs;
        b[31] &= 0x7f;
        fiat_25519_from_bytes(&mut t, &b);
        t
    }

    #[test]
    fn divstep_matches_fermat_for_small_inputs() {
        for k in 1u8..8 {
            let mut bs = [0u8; 32];
            bs[0] = k;
            let x = tight_from_bytes(&bs);

            let mut f_out = fiat_25519_tight_field_element([0; 5]);
            fermat(&mut f_out, &x);
            let mut d_out = fiat_25519_tight_field_element([0; 5]);
            fe25519_invert_divstep_tight(&mut d_out, &x);

            let mut fb = [0u8; 32];
            let mut db = [0u8; 32];
            fiat_25519_to_bytes(&mut fb, &f_out);
            fiat_25519_to_bytes(&mut db, &d_out);
            assert_eq!(fb, db, "divstep != fermat for x = {}", k);
        }
    }

    #[test]
    fn divstep_matches_fermat_for_random_input() {
        let mut bs = [0u8; 32];
        for (i, b) in bs.iter_mut().enumerate() {
            *b = (i as u8).wrapping_mul(37).wrapping_add(11);
        }
        bs[31] &= 0x7f;
        let x = tight_from_bytes(&bs);

        let mut f_out = fiat_25519_tight_field_element([0; 5]);
        fermat(&mut f_out, &x);
        let mut d_out = fiat_25519_tight_field_element([0; 5]);
        fe25519_invert_divstep_tight(&mut d_out, &x);

        let mut fb = [0u8; 32];
        let mut db = [0u8; 32];
        fiat_25519_to_bytes(&mut fb, &f_out);
        fiat_25519_to_bytes(&mut db, &d_out);
        assert_eq!(fb, db);
    }

    #[test]
    fn limb_conversion_roundtrips() {
        let cases: [[u64; 4]; 4] = [
            [1, 0, 0, 0],
            [0xdead_beef_cafe_babe, 0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210, 0x1f],
            [u64::MAX, u64::MAX, u64::MAX, 0x7fff_ffff_ffff_ffff],
            [0, 0, 0, 0],
        ];
        for x in &cases {
            let s = sg::from_saturated_4(x);
            let y = sg::to_saturated_4(&s);
            assert_eq!(*x, y, "roundtrip failed for {:?}", x);
        }
    }
}
