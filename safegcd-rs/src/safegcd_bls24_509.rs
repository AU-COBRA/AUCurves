//! Bernstein-Yang divstep modular inversion mod BLS24-509 base prime
//! (509-bit Fp).
//!
//! Uses 9×62-bit signed limbs.
//!
//! Iteration count: for δ₀=1/2 and b=509, paper Theorem 1 gives
//!   ⌈(9437·509 + 1)/4096⌉ = 1173 divsteps.
//! We use 20 outer iterations × 59 = 1180 divsteps (≥ 1173).
//!
//! KAT via `x · x^{-1} ≡ 1 (mod p)` using schoolbook mul-mod.

use crate::safegcd::{self as sg, ModInfo, Signed62};

/// BLS24-509 base prime as 8×u64 LE.
/// p = ((z-1)^2 · (z^8 - z^4 + 1)) / 3 + z,  z = -0x800000ffff801.
pub const BLS24_P_8X64: [u64; 8] = [
    0xA13D_118D_B8BF_D2AB,
    0xEE63_BD07_6E8D_9300,
    0xCFCB_5C60_71BA_D3D2,
    0x626E_85BF_7C18_A0F0,
    0x32EA_0103_E010_90BB,
    0xCB8A_C849_5D18_7E8C,
    0xFCED_F2B4_F9C0_ECF6,
    0x1555_56FF_FF39_CA9B,
];

pub const BLS24_509: ModInfo<9> = sg::modinfo_from_8u64(BLS24_P_8X64, 20);

/// `x^{-1} mod p_bls24` on 8×u64 saturated input.
#[inline(never)]
pub fn bls24_invert_divstep_sat(out: &mut [u64; 8], x: &[u64; 8]) {
    let x_lim: Signed62<9> = sg::from_saturated_8(x);
    let inv = sg::invert(x_lim, &BLS24_509);
    *out = sg::to_saturated_8(&inv);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mul_mod_p_8(a: &[u64; 8], b: &[u64; 8], p: &[u64; 8]) -> [u64; 8] {
        let mut prod = [0u64; 16];
        for i in 0..8 {
            let mut carry: u128 = 0;
            for j in 0..8 {
                let v = (a[i] as u128) * (b[j] as u128) + (prod[i + j] as u128) + carry;
                prod[i + j] = v as u64;
                carry = v >> 64;
            }
            prod[i + 8] = carry as u64;
        }
        const N: usize = 16;
        let mut p_ext = [0u64; N];
        p_ext[..8].copy_from_slice(p);
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
        let mut out = [0u64; 8];
        out.copy_from_slice(&rem[..8]);
        out
    }

    fn is_zero(x: &[u64; 8]) -> bool {
        x.iter().all(|&v| v == 0)
    }

    #[test]
    fn bls24_invert_times_self_is_one() {
        let inputs: [[u64; 8]; 3] = [
            [1, 0, 0, 0, 0, 0, 0, 0],
            [2, 0, 0, 0, 0, 0, 0, 0],
            [
                0x0123_4567_89ab_cdef,
                0xfedc_ba98_7654_3210,
                0xdead_beef_cafe_babe,
                0x1, 0x0, 0x0, 0x0, 0x0,
            ],
        ];
        for (i, x) in inputs.iter().enumerate() {
            let mut xi = [0u64; 8];
            bls24_invert_divstep_sat(&mut xi, x);
            assert!(!is_zero(&xi), "BLS24 invert(x) = 0 for input {}", i);
            let prod = mul_mod_p_8(x, &xi, &BLS24_P_8X64);
            let one = [1u64, 0, 0, 0, 0, 0, 0, 0];
            assert_eq!(prod, one, "BLS24: x · x^-1 != 1 for input {}", i);
        }
    }
}
