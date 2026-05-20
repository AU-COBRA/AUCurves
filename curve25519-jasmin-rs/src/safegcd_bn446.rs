//! Bernstein-Yang divstep modular inversion mod BN446 base prime
//! (446-bit Fp, AUCurves `bn446_prime_certif.v`).
//!
//! Seed u = 2^110 + 2^36 + 1 = 0x4000000000000000001000000001.
//! Prime p = 36u^4 + 36u^3 + 24u^2 + 6u + 1
//!   = 102211695604069718983520304652693874995639508460729604902280098199792736381528662976886082950231100101353700265360419596271313339023463.
//!
//! Native size is 7×u64, but we pad to 8×u64 (top limb = 0) so we can
//! re-use the 8×u64 → 9×62 conversion that already powers BLS24-509.
//!
//! Iteration count: for δ₀=1/2 and b=446, paper Theorem 1 gives
//!   ⌈(9437·446 + 1)/4096⌉ = 1028 divsteps.
//! We use 18 outer iterations × 59 = 1062 divsteps (≥ 1028).
//!
//! KAT via `x · x^{-1} ≡ 1 (mod p)` using schoolbook mul-mod.

use crate::safegcd::{self as sg, ModInfo, Signed62};

/// BN446 base prime as 8×u64 LE (top limb is 0; 446-bit value lives in
/// limbs 0..7 with the high bits of limb 6).
pub const BN446_P_8X64: [u64; 8] = [
    0x0000_1320_0000_0067,
    0x0057_C000_0001_5C00,
    0x8700_0000_0B04_0000,
    0x0000_0018_0000_0000,
    0x0000_0D80_0000_021C,
    0x0024_0000_0002_D000,
    0x2400_0000_0000_0000,
    0x0000_0000_0000_0000,
];

pub const BN446: ModInfo<9> = sg::modinfo_from_8u64(BN446_P_8X64, 18);

/// `x^{-1} mod p_bn446` on 8×u64 saturated input (top limb assumed 0).
#[inline(never)]
pub fn bn446_invert_divstep_sat(out: &mut [u64; 8], x: &[u64; 8]) {
    let x_lim: Signed62<9> = sg::from_saturated_8(x);
    let inv = sg::invert(x_lim, &BN446);
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
    fn bn446_invert_times_self_is_one() {
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
            bn446_invert_divstep_sat(&mut xi, x);
            assert!(!is_zero(&xi), "BN446 invert(x) = 0 for input {}", i);
            let prod = mul_mod_p_8(x, &xi, &BN446_P_8X64);
            let one = [1u64, 0, 0, 0, 0, 0, 0, 0];
            assert_eq!(prod, one, "BN446: x · x^-1 != 1 for input {}", i);
        }
    }
}
