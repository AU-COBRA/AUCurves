//! Bernstein-Yang divstep modular inversion mod BN254 base prime
//! p = 0x30644E72E131A029_B85045B68181585D_97816A916871CA8D_3C208C16D87CFD47
//!   = 21888242871839275222246405745257275088696311157297823662689037894645226208583.
//!
//! KAT-tested via the x · x^{-1} ≡ 1 (mod p) identity using a self-contained
//! schoolbook multiplier + Barrett-style reduction (fiat-rust 0.3.0 doesn't
//! ship a BN254 module).

use crate::safegcd::{self as sg, ModInfo, Signed62};

/// BN254 base prime in 4×u64 little-endian.
pub const BN254_P_4X64: [u64; 4] = [
    0x3C20_8C16_D87C_FD47,
    0x9781_6A91_6871_CA8D,
    0xB850_45B6_8181_585D,
    0x3064_4E72_E131_A029,
];

pub const BN254: ModInfo<5> = sg::modinfo_from_4u64(BN254_P_4X64, 10);

/// `x^{-1} mod p_bn254` on 4×u64 saturated input.
#[inline(never)]
pub fn bn254_invert_divstep_sat(out: &mut [u64; 4], x: &[u64; 4]) {
    let x_lim: Signed62<5> = sg::from_saturated_4(x);
    let inv = sg::invert(x_lim, &BN254);
    *out = sg::to_saturated_4(&inv);
}

#[cfg(test)]
mod tests {
    use super::*;

    /// 4×4 -> 8 limb schoolbook multiply, then 8→4 limb Barrett-style reduce
    /// using big integer division.  Slow but correct.
    fn mul_mod_p(a: &[u64; 4], b: &[u64; 4], p: &[u64; 4]) -> [u64; 4] {
        let to_u512 = |x: &[u64; 4]| -> [u64; 8] {
            let mut out = [0u64; 8];
            out[..4].copy_from_slice(x);
            out
        };
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
        // Long-division mod p (≤ 256-bit divisor, ≤ 512-bit dividend).
        // Implemented via simple bit-by-bit shift+subtract.  ~512 iterations.
        let p_ext = to_u512(p);
        let mut rem = [0u64; 8];
        for bit in (0..512).rev() {
            // Shift rem left by 1.
            let mut carry: u64 = 0;
            for limb in rem.iter_mut() {
                let new_carry = *limb >> 63;
                *limb = (*limb << 1) | carry;
                carry = new_carry;
            }
            // Bring down next bit of prod.
            let limb = bit / 64;
            let lbit = bit % 64;
            rem[0] |= (prod[limb] >> lbit) & 1;
            // If rem >= p_ext (compare as 512-bit), subtract p_ext.
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
    fn bn254_invert_times_self_is_one() {
        let inputs: [[u64; 4]; 4] = [
            [1, 0, 0, 0],
            [2, 0, 0, 0],
            [0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210, 0xdead_beef, 0x1],
            // p - 1
            [
                BN254_P_4X64[0] - 1,
                BN254_P_4X64[1],
                BN254_P_4X64[2],
                BN254_P_4X64[3],
            ],
        ];
        for (i, x) in inputs.iter().enumerate() {
            let mut xi = [0u64; 4];
            bn254_invert_divstep_sat(&mut xi, x);
            assert!(!is_zero(&xi), "invert(x) = 0 for input {}", i);
            let prod = mul_mod_p(x, &xi, &BN254_P_4X64);
            let one = [1u64, 0, 0, 0];
            assert_eq!(prod, one, "x · x^{{-1}} != 1 for input {}: x={:?}", i, x);
        }
    }
}
