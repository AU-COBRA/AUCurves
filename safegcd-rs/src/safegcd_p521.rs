//! Bernstein-Yang divstep modular inversion mod NIST P-521
//! = 2^521 − 1 (Mersenne prime M_521).
//!
//! Uses 10×62-bit signed limbs (9 u64 input).  Iteration count: 21 outer
//! × 59 = 1239 divsteps (paper bound for 521-bit prime: ⌈(9437·521+1)/(4096·59)⌉
//! = 21).
//!
//! KAT via `x · x^{-1} ≡ 1 (mod p)` using schoolbook mul-mod.

use crate::safegcd::{self as sg, ModInfo, Signed62};

/// P-521 prime in 9×u64 little-endian.
/// p = 2^521 - 1 → 8 limbs of all-ones plus high limb 0x1ff (9 bits).
pub const P521_P_9X64: [u64; 9] = [
    0xFFFF_FFFF_FFFF_FFFF,
    0xFFFF_FFFF_FFFF_FFFF,
    0xFFFF_FFFF_FFFF_FFFF,
    0xFFFF_FFFF_FFFF_FFFF,
    0xFFFF_FFFF_FFFF_FFFF,
    0xFFFF_FFFF_FFFF_FFFF,
    0xFFFF_FFFF_FFFF_FFFF,
    0xFFFF_FFFF_FFFF_FFFF,
    0x0000_0000_0000_01FF,
];

pub const P521: ModInfo<10> = sg::modinfo_from_9u64(P521_P_9X64, 21);

/// `x^{-1} mod p521` on 9×u64 saturated input.
#[inline(never)]
pub fn p521_invert_divstep_sat(out: &mut [u64; 9], x: &[u64; 9]) {
    let x_lim: Signed62<10> = sg::from_saturated_9(x);
    let inv = sg::invert(x_lim, &P521);
    *out = sg::to_saturated_9(&inv);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mul_mod_p_9(a: &[u64; 9], b: &[u64; 9], p: &[u64; 9]) -> [u64; 9] {
        let mut prod = [0u64; 18];
        for i in 0..9 {
            let mut carry: u128 = 0;
            for j in 0..9 {
                let v = (a[i] as u128) * (b[j] as u128) + (prod[i + j] as u128) + carry;
                prod[i + j] = v as u64;
                carry = v >> 64;
            }
            prod[i + 9] = carry as u64;
        }
        const N: usize = 18;
        let mut p_ext = [0u64; N];
        p_ext[..9].copy_from_slice(p);
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
        let mut out = [0u64; 9];
        out.copy_from_slice(&rem[..9]);
        out
    }

    fn is_zero(x: &[u64; 9]) -> bool {
        x.iter().all(|&v| v == 0)
    }

    #[test]
    fn p521_invert_times_self_is_one() {
        let inputs: [[u64; 9]; 4] = [
            [1, 0, 0, 0, 0, 0, 0, 0, 0],
            [2, 0, 0, 0, 0, 0, 0, 0, 0],
            [
                0x0123_4567_89ab_cdef,
                0xfedc_ba98_7654_3210,
                0xdead_beef_cafe_babe,
                0x1, 0x0, 0x0, 0x0, 0x0, 0x0,
            ],
            // p - 1
            [
                P521_P_9X64[0] - 1,
                P521_P_9X64[1],
                P521_P_9X64[2],
                P521_P_9X64[3],
                P521_P_9X64[4],
                P521_P_9X64[5],
                P521_P_9X64[6],
                P521_P_9X64[7],
                P521_P_9X64[8],
            ],
        ];
        for (i, x) in inputs.iter().enumerate() {
            let mut xi = [0u64; 9];
            p521_invert_divstep_sat(&mut xi, x);
            assert!(!is_zero(&xi), "P-521 invert(x) = 0 for input {}", i);
            let prod = mul_mod_p_9(x, &xi, &P521_P_9X64);
            let one = [1u64, 0, 0, 0, 0, 0, 0, 0, 0];
            assert_eq!(prod, one, "P-521: x · x^-1 != 1 for input {}", i);
        }
    }
}
