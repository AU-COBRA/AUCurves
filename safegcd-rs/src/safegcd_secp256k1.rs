//! Bernstein-Yang divstep modular inversion mod secp256k1 prime
//! = 2^256 − 2^32 − 977 = 0xFFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFE_FFFFFC2F.
//!
//! Uses the same generic core as `safegcd25519` — only the modulus
//! constants change.  10 outer iterations × 59 divsteps = 590 (paper §3.4,
//! δ₀=1/2, b=256), matches what libsecp256k1 itself ships.

use crate::safegcd::{self as sg, ModInfo, Signed62};

/// secp256k1 prime p = 2^256 − 2^32 − 977, in 4×u64 little-endian.
pub const SECP_P_4X64: [u64; 4] = [
    0xFFFF_FFFE_FFFF_FC2F,
    0xFFFF_FFFF_FFFF_FFFF,
    0xFFFF_FFFF_FFFF_FFFF,
    0xFFFF_FFFF_FFFF_FFFF,
];

pub const SECP256K1: ModInfo<5> = sg::modinfo_from_4u64(SECP_P_4X64, 10);

/// `x^{-1} mod secp256k1_p` on 4×u64 saturated input.
#[inline(never)]
pub fn secp_invert_divstep_sat(out: &mut [u64; 4], x: &[u64; 4]) {
    let x_lim: Signed62<5> = sg::from_saturated_4(x);
    let inv = sg::invert(x_lim, &SECP256K1);
    *out = sg::to_saturated_4(&inv);
}

#[cfg(test)]
mod tests {
    use super::*;

    const SECP_P_SATURATED: [u64; 4] = SECP_P_4X64;

    /// Schoolbook 4×4 -> 8 limb multiplication, then mod-secp reduce.
    /// Slow but correct — used only to verify the inversion via x · x^{-1} ≡ 1.
    fn mul_mod_secp(a: &[u64; 4], b: &[u64; 4]) -> [u64; 4] {
        // a, b in [0, 2^256).  product in [0, 2^512).
        // We work in u128 limbs and then reduce mod p.
        let mut prod = [0u64; 8];
        for i in 0..4 {
            let mut carry: u128 = 0;
            for j in 0..4 {
                let hi_lo = (a[i] as u128) * (b[j] as u128)
                    + (prod[i + j] as u128)
                    + carry;
                prod[i + j] = hi_lo as u64;
                carry = hi_lo >> 64;
            }
            prod[i + 4] = carry as u64;
        }
        // Reduce: use the fact that 2^256 ≡ 2^32 + 977 (mod p).
        // result = lo + (2^32 + 977) * hi, repeated until hi = 0.
        let mut lo = [prod[0], prod[1], prod[2], prod[3]];
        let mut hi = [prod[4], prod[5], prod[6], prod[7]];

        for _ in 0..2 {
            // r = lo + 977*hi + (2^32)*hi
            // First: 977 * hi -> 5-limb (4 + carry)
            let c977: u128 = 977;
            let mut h977 = [0u64; 5];
            let mut carry: u128 = 0;
            for i in 0..4 {
                let v = (hi[i] as u128) * c977 + carry;
                h977[i] = v as u64;
                carry = v >> 64;
            }
            h977[4] = carry as u64;

            // (2^32) * hi -> shift by 32 bits across limbs, 5-limb output
            let mut hshift = [0u64; 5];
            let mut carry: u64 = 0;
            for i in 0..4 {
                hshift[i] = (hi[i] << 32) | carry;
                carry = hi[i] >> 32;
            }
            hshift[4] = carry;

            // Add lo + h977 + hshift  (-> at most 5 limbs)
            let mut t = [0u64; 5];
            let mut c: u128 = 0;
            for i in 0..5 {
                let lo_i = if i < 4 { lo[i] as u128 } else { 0 };
                let v = lo_i + (h977[i] as u128) + (hshift[i] as u128) + c;
                t[i] = v as u64;
                c = v >> 64;
            }

            lo = [t[0], t[1], t[2], t[3]];
            hi = [t[4], 0, 0, 0];
        }

        // Final canonicalization: subtract p if lo >= p
        // (loop bound: after two reductions hi is 0 and lo can be < 2*p)
        let mut borrow: i128 = 0;
        let mut t = [0u64; 4];
        for i in 0..4 {
            let v = (lo[i] as i128) - (SECP_P_SATURATED[i] as i128) - borrow;
            t[i] = v as u64;
            borrow = if v < 0 { 1 } else { 0 };
        }
        if borrow == 0 {
            lo = t;
        }
        lo
    }

    fn is_zero(x: &[u64; 4]) -> bool {
        x[0] | x[1] | x[2] | x[3] == 0
    }

    #[test]
    fn secp_invert_times_self_is_one() {
        // Several deterministic non-zero inputs in [1, p).
        let inputs: [[u64; 4]; 5] = [
            [1, 0, 0, 0],
            [2, 0, 0, 0],
            [0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210, 0xdead_beef, 0x1],
            [
                0xa1b2_c3d4_e5f6_0708,
                0x1122_3344_5566_7788,
                0x99aa_bbcc_ddee_ff00,
                0x0011_2233_4455_6677,
            ],
            // p - 1
            [
                SECP_P_SATURATED[0] - 1,
                SECP_P_SATURATED[1],
                SECP_P_SATURATED[2],
                SECP_P_SATURATED[3],
            ],
        ];

        for (i, x) in inputs.iter().enumerate() {
            let mut xi = [0u64; 4];
            secp_invert_divstep_sat(&mut xi, x);
            assert!(!is_zero(&xi), "invert returned 0 for input {} = {:?}", i, x);
            let prod = mul_mod_secp(x, &xi);
            let expected_one = [1u64, 0, 0, 0];
            assert_eq!(
                prod, expected_one,
                "x · x^{{-1}} != 1 for input {}: x={:?}, xi={:?}, prod={:?}",
                i, x, xi, prod
            );
        }
    }

    #[test]
    fn secp_zero_input_returns_zero() {
        let mut xi = [0u64; 4];
        secp_invert_divstep_sat(&mut xi, &[0, 0, 0, 0]);
        assert!(is_zero(&xi), "invert(0) should be 0");
    }
}
