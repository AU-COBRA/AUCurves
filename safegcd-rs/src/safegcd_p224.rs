//! Bernstein-Yang divstep modular inversion mod NIST P-224
//! = 2^224 − 2^96 + 1.
//!
//! Uses 5×62-bit signed limbs (4 u64 input).  Iteration count: 9 outer
//! × 59 = 531 divsteps.  Paper bound for 224-bit prime: ⌈(9437·224+1)/(4096·59)⌉
//! = 9.  OCaml half-framework bisection (δ₀=1/2) converges at N ≤ 517, well
//! within 9 outer iterations.  Track W: tightened 10→9 (2026-05-20).
//!
//! KAT via `x · x^{-1} ≡ 1 (mod p)` using schoolbook mul-mod.

use crate::safegcd::{self as sg, ModInfo, Signed62};

/// P-224 prime in 4×u64 little-endian.
/// p = 0xffffffff_ffffffff_ffffffff_ffffffff_00000000_00000000_00000000_00000001
pub const P224_P_4X64: [u64; 4] = [
    0x0000_0000_0000_0001,
    0xFFFF_FFFF_0000_0000,
    0xFFFF_FFFF_FFFF_FFFF,
    0x0000_0000_FFFF_FFFF,
];

pub const P224: ModInfo<5> = sg::modinfo_from_4u64(P224_P_4X64, 9);

/// `x^{-1} mod p224` on 4×u64 saturated input.
#[inline(never)]
pub fn p224_invert_divstep_sat(out: &mut [u64; 4], x: &[u64; 4]) {
    let x_lim: Signed62<5> = sg::from_saturated_4(x);
    let inv = sg::invert(x_lim, &P224);
    *out = sg::to_saturated_4(&inv);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mul_mod_p_4(a: &[u64; 4], b: &[u64; 4], p: &[u64; 4]) -> [u64; 4] {
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
        const N: usize = 8;
        let mut p_ext = [0u64; N];
        p_ext[..4].copy_from_slice(p);
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
        let mut out = [0u64; 4];
        out.copy_from_slice(&rem[..4]);
        out
    }

    fn is_zero(x: &[u64; 4]) -> bool {
        x.iter().all(|&v| v == 0)
    }

    #[test]
    fn p224_invert_times_self_is_one() {
        let inputs: [[u64; 4]; 4] = [
            [1, 0, 0, 0],
            [2, 0, 0, 0],
            [0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210, 0xdead_beef, 0x1],
            // p - 1
            [
                P224_P_4X64[0] - 1,
                P224_P_4X64[1],
                P224_P_4X64[2],
                P224_P_4X64[3],
            ],
        ];
        for (i, x) in inputs.iter().enumerate() {
            let mut xi = [0u64; 4];
            p224_invert_divstep_sat(&mut xi, x);
            assert!(!is_zero(&xi), "P-224 invert(x) = 0 for input {}", i);
            let prod = mul_mod_p_4(x, &xi, &P224_P_4X64);
            let one = [1u64, 0, 0, 0];
            assert_eq!(prod, one, "P-224: x · x^-1 != 1 for input {}", i);
        }
    }
}
