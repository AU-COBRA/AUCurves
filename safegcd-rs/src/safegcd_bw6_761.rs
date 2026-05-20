//! Bernstein-Yang divstep modular inversion mod BW6-761 base prime
//! (761-bit Fp, AUCurves `bw6_761_prime_certif.v`).
//!
//! p = 0x122e824fb83ce0ad187c94004faff3eb926186a81d14688528275ef8087be417
//!     07ba638e584e91903cebaff25b423048689c8ed12f9fd9071dcd3dc73ebff2e9
//!     8a116c25667a8f8160cf8aeeaf0a437e6913e6870000082f49d00000000008b
//!   = 6891450384315732539396789682275657542479668912536150109513790160209623422243491736087683183289411687640864567753786613451161759120554247759349511699125301598951605099378508850372543631423596795951899700429969112842764913119068299.
//!
//! Uses 13×62-bit signed limbs (12×u64 saturated input).
//!
//! Iteration count: for δ₀=1/2 and b=761, paper Theorem 1 gives
//!   ⌈(9437·761 + 1)/4096⌉ = 1754 divsteps.
//! We use 30 outer iterations × 59 = 1770 divsteps (≥ 1754).
//!
//! KAT via `x · x^{-1} ≡ 1 (mod p)` using schoolbook mul-mod.

use crate::safegcd::{self as sg, ModInfo, Signed62};

/// BW6-761 base prime as 12×u64 LE.
pub const BW6_761_P_12X64: [u64; 12] = [
    0xF49D_0000_0000_008B,
    0xE691_3E68_7000_0082,
    0x160C_F8AE_EAF0_A437,
    0x98A1_16C2_5667_A8F8,
    0x71DC_D3DC_73EB_FF2E,
    0x8689_C8ED_12F9_FD90,
    0x03CE_BAFF_25B4_2304,
    0x707B_A638_E584_E919,
    0x5282_75EF_8087_BE41,
    0xB926_186A_81D1_4688,
    0xD187_C940_04FA_FF3E,
    0x0122_E824_FB83_CE0A,
];

pub const BW6_761: ModInfo<13> = sg::modinfo_from_12u64(BW6_761_P_12X64, 30);

/// `x^{-1} mod p_bw6_761` on 12×u64 saturated input.
#[inline(never)]
pub fn bw6_761_invert_divstep_sat(out: &mut [u64; 12], x: &[u64; 12]) {
    let x_lim: Signed62<13> = sg::from_saturated_12(x);
    let inv = sg::invert(x_lim, &BW6_761);
    *out = sg::to_saturated_12(&inv);
}

#[cfg(test)]
mod tests {
    use super::*;

    /// 12×12 → 24-limb schoolbook multiply, then long-divide mod p.
    fn mul_mod_p_12(a: &[u64; 12], b: &[u64; 12], p: &[u64; 12]) -> [u64; 12] {
        let mut prod = [0u64; 24];
        for i in 0..12 {
            let mut carry: u128 = 0;
            for j in 0..12 {
                let v = (a[i] as u128) * (b[j] as u128) + (prod[i + j] as u128) + carry;
                prod[i + j] = v as u64;
                carry = v >> 64;
            }
            prod[i + 12] = carry as u64;
        }
        const N: usize = 24;
        let mut p_ext = [0u64; N];
        p_ext[..12].copy_from_slice(p);
        let mut rem = [0u64; N];
        for bit in (0..(N * 64)).rev() {
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
            for k in (0..N).rev() {
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
                for k in 0..N {
                    let v = (rem[k] as i128) - (p_ext[k] as i128) - borrow;
                    rem[k] = v as u64;
                    borrow = if v < 0 { 1 } else { 0 };
                }
            }
        }
        let mut out = [0u64; 12];
        out.copy_from_slice(&rem[..12]);
        out
    }

    fn is_zero(x: &[u64; 12]) -> bool {
        x.iter().all(|&v| v == 0)
    }

    #[test]
    fn bw6_761_invert_times_self_is_one() {
        let inputs: [[u64; 12]; 3] = [
            [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [
                0x0123_4567_89ab_cdef,
                0xfedc_ba98_7654_3210,
                0xdead_beef_cafe_babe,
                0x1, 0x0, 0x0, 0x0, 0x0,
                0x0, 0x0, 0x0, 0x0,
            ],
        ];
        for (i, x) in inputs.iter().enumerate() {
            let mut xi = [0u64; 12];
            bw6_761_invert_divstep_sat(&mut xi, x);
            assert!(!is_zero(&xi), "BW6-761 invert(x) = 0 for input {}", i);
            let prod = mul_mod_p_12(x, &xi, &BW6_761_P_12X64);
            let one = [1u64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
            assert_eq!(prod, one, "BW6-761: x · x^-1 != 1 for input {}", i);
        }
    }
}
