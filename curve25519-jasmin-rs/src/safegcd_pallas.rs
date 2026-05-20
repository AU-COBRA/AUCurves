//! Bernstein-Yang divstep modular inversion mod Pallas base prime
//! q = 2^254 + 45560315531419706090280762371685220353
//!   = 0x40000000_00000000_00000000_00000000_224698fc_094cf91b_992d30ed_00000001
//!   = 28948022309329048855892746252171976963363056481941560715954676764349967630337.
//!
//! 255-bit Pasta-cycle base prime (= scalar of Vesta).
//!
//! Iteration count: for δ₀=1/2 and b=255, paper Theorem 1 gives
//!   ⌈(9437·255 + 1)/4096⌉ = 588 divsteps.
//! We use 10 outer iterations × 59 = 590 divsteps (matches secp256k1 / P-256).
//!
//! KAT via `x · x^{-1} ≡ 1 (mod p)`.

use crate::safegcd::{self as sg, ModInfo, Signed62};

/// Pallas base prime as 4×u64 LE.
pub const PALLAS_P_4X64: [u64; 4] = [
    0x992D_30ED_0000_0001,
    0x2246_98FC_094C_F91B,
    0x0000_0000_0000_0000,
    0x4000_0000_0000_0000,
];

pub const PALLAS: ModInfo<5> = sg::modinfo_from_4u64(PALLAS_P_4X64, 10);

/// `x^{-1} mod p_pallas` on 4×u64 saturated input.
#[inline(never)]
pub fn pallas_invert_divstep_sat(out: &mut [u64; 4], x: &[u64; 4]) {
    let x_lim: Signed62<5> = sg::from_saturated_4(x);
    let inv = sg::invert(x_lim, &PALLAS);
    *out = sg::to_saturated_4(&inv);
}

#[cfg(test)]
mod tests {
    use super::*;

    /// 4×4 -> 8 limb schoolbook multiply, then long-divide mod p.
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
            // ge starts true so the `rem == p_ext` case (all limbs equal,
            // no break taken) correctly subtracts p.
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
    fn pallas_invert_times_self_is_one() {
        let inputs: [[u64; 4]; 4] = [
            [1, 0, 0, 0],
            [2, 0, 0, 0],
            [0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210, 0xdead_beef, 0x1],
            // p - 1
            [
                PALLAS_P_4X64[0] - 1,
                PALLAS_P_4X64[1],
                PALLAS_P_4X64[2],
                PALLAS_P_4X64[3],
            ],
        ];
        for (i, x) in inputs.iter().enumerate() {
            let mut xi = [0u64; 4];
            pallas_invert_divstep_sat(&mut xi, x);
            assert!(!is_zero(&xi), "Pallas invert(x) = 0 for input {}", i);
            let prod = mul_mod_p(x, &xi, &PALLAS_P_4X64);
            let one = [1u64, 0, 0, 0];
            assert_eq!(prod, one, "Pallas: x · x^-1 != 1 for input {}: x={:?}", i, x);
        }
    }
}
