//! Bernstein-Yang divstep modular inversion mod BLS12-381 base prime
//! (381-bit Fp).
//!
//! Uses 7×62-bit signed limbs (matches what libsecp256k1's design generalizes
//! to for larger primes).
//!
//! Iteration count: for δ₀=1/2 and b=381, paper Theorem 1 gives
//!   ⌈(9437·381 + 1)/4096⌉ = 878 divsteps.
//! We use 15 outer iterations × 59 = 885 divsteps (≥ 878).
//!
//! KAT via `x · x^{-1} ≡ 1 (mod p)` using schoolbook mul-mod.

use crate::safegcd::{self as sg, ModInfo, Signed62};

/// BLS12-381 base prime as 6×u64 LE.
/// p = 0x1A0111EA397FE69A_4B1BA7B6434BACD7_64774B84F38512BF_6730D2A0F6B0F624_1EABFFFEB153FFFF_B9FEFFFFFFFFAAAB
pub const BLS12_P_6X64: [u64; 6] = [
    0xB9FE_FFFF_FFFF_AAAB,
    0x1EAB_FFFE_B153_FFFF,
    0x6730_D2A0_F6B0_F624,
    0x6477_4B84_F385_12BF,
    0x4B1B_A7B6_434B_ACD7,
    0x1A01_11EA_397F_E69A,
];

pub const BLS12_381: ModInfo<7> = sg::modinfo_from_6u64(BLS12_P_6X64, 15);

/// `x^{-1} mod p_bls12` on 6×u64 saturated input.
#[inline(never)]
pub fn bls12_invert_divstep_sat(out: &mut [u64; 6], x: &[u64; 6]) {
    let x_lim: Signed62<7> = sg::from_saturated_6(x);
    let inv = sg::invert(x_lim, &BLS12_381);
    *out = sg::to_saturated_6(&inv);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mul_mod_p_6(a: &[u64; 6], b: &[u64; 6], p: &[u64; 6]) -> [u64; 6] {
        // 6×6→12-limb schoolbook
        let mut prod = [0u64; 12];
        for i in 0..6 {
            let mut carry: u128 = 0;
            for j in 0..6 {
                let v = (a[i] as u128) * (b[j] as u128) + (prod[i + j] as u128) + carry;
                prod[i + j] = v as u64;
                carry = v >> 64;
            }
            prod[i + 6] = carry as u64;
        }
        // Long-division mod p, bit by bit.
        const N: usize = 12;
        let mut p_ext = [0u64; N];
        p_ext[..6].copy_from_slice(p);
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
        [rem[0], rem[1], rem[2], rem[3], rem[4], rem[5]]
    }

    fn is_zero(x: &[u64; 6]) -> bool {
        x.iter().all(|&v| v == 0)
    }

    #[test]
    fn bls12_invert_times_self_is_one() {
        let inputs: [[u64; 6]; 4] = [
            [1, 0, 0, 0, 0, 0],
            [2, 0, 0, 0, 0, 0],
            [
                0x0123_4567_89ab_cdef,
                0xfedc_ba98_7654_3210,
                0xdead_beef_cafe_babe,
                0x1, 0x0, 0x0,
            ],
            // p - 1
            [
                BLS12_P_6X64[0] - 1,
                BLS12_P_6X64[1],
                BLS12_P_6X64[2],
                BLS12_P_6X64[3],
                BLS12_P_6X64[4],
                BLS12_P_6X64[5],
            ],
        ];
        for (i, x) in inputs.iter().enumerate() {
            let mut xi = [0u64; 6];
            bls12_invert_divstep_sat(&mut xi, x);
            assert!(!is_zero(&xi), "BLS12 invert(x) = 0 for input {}", i);
            let prod = mul_mod_p_6(x, &xi, &BLS12_P_6X64);
            let one = [1u64, 0, 0, 0, 0, 0];
            assert_eq!(prod, one, "BLS12: x · x^-1 != 1 for input {}", i);
        }
    }
}
