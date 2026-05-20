//! Bernstein-Yang divstep modular inversion mod BN256 base prime
//! p = 36u^4 + 36u^3 + 24u^2 + 6u + 1, with u = 0x5A76AE9AEC588301
//!   = 65000549695646603732796438742359905742825358107623003571877145026864184071783
//!   = 0x8FB501E3_4AA387F9_AA6FECB8_6184DC21_EE5B88D1_20B5B59E_185CAC6C_5E089667.
//!
//! 256-bit BN curve base prime (AUCurves Spec, `bn256_prime_certif.v`).
//!
//! Iteration count: for δ₀=1/2 and b=256, paper Theorem 1 gives
//!   ⌈(9437·256 + 1)/4096⌉ = 590 divsteps.
//! We use 10 outer iterations × 59 = 590 divsteps (matches BN254 / P-256).
//!
//! KAT via `x · x^{-1} ≡ 1 (mod p)`.

use crate::safegcd::{self as sg, ModInfo, Signed62};

/// BN256 base prime as 4×u64 LE.
pub const BN256_P_4X64: [u64; 4] = [
    0x185C_AC6C_5E08_9667,
    0xEE5B_88D1_20B5_B59E,
    0xAA6F_ECB8_6184_DC21,
    0x8FB5_01E3_4AA3_87F9,
];

pub const BN256: ModInfo<5> = sg::modinfo_from_4u64(BN256_P_4X64, 10);

/// `x^{-1} mod p_bn256` on 4×u64 saturated input.
#[inline(never)]
pub fn bn256_invert_divstep_sat(out: &mut [u64; 4], x: &[u64; 4]) {
    let x_lim: Signed62<5> = sg::from_saturated_4(x);
    let inv = sg::invert(x_lim, &BN256);
    *out = sg::to_saturated_4(&inv);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mul_mod_p(a: &[u64; 4], b: &[u64; 4], p: &[u64; 4]) -> [u64; 4] {
        let mut prod = [0u64; 8];
        for i in 0..4 {
            let mut carry: u128 = 0;
            for j in 0..4 {
                let v = (a[i] as u128) * (b[j] as u128) + (prod[i + j] as u128) + carry;
                prod[i + j] = v as u64;
                carry = v >> 64;
            }
            prod[i + 4] = carry as u64;
        }
        let mut p_ext = [0u64; 8];
        p_ext[..4].copy_from_slice(p);
        let mut rem = [0u64; 8];
        for bit in (0..512).rev() {
            let mut carry: u64 = 0;
            for limb in rem.iter_mut() {
                let new_carry = *limb >> 63;
                *limb = (*limb << 1) | carry;
                carry = new_carry;
            }
            let limb = bit / 64;
            let lbit = bit % 64;
            rem[0] |= (prod[limb] >> lbit) & 1;
            let mut ge = true;
            for k in (0..8).rev() {
                if rem[k] > p_ext[k] {
                    ge = true;
                    break;
                }
                if rem[k] < p_ext[k] {
                    ge = false;
                    break;
                }
            }
            if ge {
                let mut borrow: i128 = 0;
                for k in 0..8 {
                    let v = (rem[k] as i128) - (p_ext[k] as i128) - borrow;
                    rem[k] = v as u64;
                    borrow = if v < 0 { 1 } else { 0 };
                }
            }
        }
        [rem[0], rem[1], rem[2], rem[3]]
    }

    fn is_zero(x: &[u64; 4]) -> bool {
        x[0] | x[1] | x[2] | x[3] == 0
    }

    #[test]
    fn bn256_invert_times_self_is_one() {
        let inputs: [[u64; 4]; 4] = [
            [1, 0, 0, 0],
            [2, 0, 0, 0],
            [0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210, 0xdead_beef, 0x1],
            [
                BN256_P_4X64[0] - 1,
                BN256_P_4X64[1],
                BN256_P_4X64[2],
                BN256_P_4X64[3],
            ],
        ];
        for (i, x) in inputs.iter().enumerate() {
            let mut xi = [0u64; 4];
            bn256_invert_divstep_sat(&mut xi, x);
            assert!(!is_zero(&xi), "BN256 invert(x) = 0 for input {}", i);
            let prod = mul_mod_p(x, &xi, &BN256_P_4X64);
            let one = [1u64, 0, 0, 0];
            assert_eq!(prod, one, "BN256: x · x^-1 != 1 for input {}: x={:?}", i, x);
        }
    }
}
