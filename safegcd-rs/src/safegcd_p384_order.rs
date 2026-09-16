//! Bernstein-Yang divstep modular inversion mod the NIST P-384 group order
//! n = 0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973.
//!
//! The sibling of `safegcd_p384.rs`, which does the same for the base field.
//! Both moduli are odd and 384 bits wide, so both use 7×62-bit signed limbs
//! (6 u64 input) and the same iteration count: `ModInfo::outer_iters`
//! requires `⌈(9437·b + 1)/(4096·59)⌉` for a b-bit modulus under the δ₀=1/2
//! encoding, which is 15 at b = 384, and `modinv_62` requires only that the
//! bottom limb be odd.  n's bottom limb is `0xecec196accc52973`.
//!
//! The inversion is over the scalar field of P-384, which is where ECDSA
//! needs `s^{-1}` and `k^{-1}`.
//!
//! KAT via `x · x^{-1} ≡ 1 (mod n)` using schoolbook mul-mod.

use crate::safegcd::{self as sg, ModInfo, Signed62};

/// P-384 group order in 6×u64 little-endian.
pub const P384_N_6X64: [u64; 6] = [
    0xecec_196a_ccc5_2973,
    0x581a_0db2_48b0_a77a,
    0xc763_4d81_f437_2ddf,
    0xFFFF_FFFF_FFFF_FFFF,
    0xFFFF_FFFF_FFFF_FFFF,
    0xFFFF_FFFF_FFFF_FFFF,
];

pub const P384_ORDER: ModInfo<7> = sg::modinfo_from_6u64(P384_N_6X64, 15);

/// `x^{-1} mod n` on 6×u64 saturated input, and 0 for `x ≡ 0`.
///
/// `x` is taken to be already reduced, i.e. in `[0, n)`.
#[inline(never)]
pub fn p384_order_invert_divstep_sat(out: &mut [u64; 6], x: &[u64; 6]) {
    let x_lim: Signed62<7> = sg::from_saturated_6(x);
    let inv = sg::invert(x_lim, &P384_ORDER);
    *out = sg::to_saturated_6(&inv);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mul_mod_n_6(a: &[u64; 6], b: &[u64; 6], n: &[u64; 6]) -> [u64; 6] {
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
        const M: usize = 12;
        let mut n_ext = [0u64; M];
        n_ext[..6].copy_from_slice(n);
        let mut rem = [0u64; M];
        for bit in (0..(M * 64)).rev() {
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
            for k in (0..M).rev() {
                if rem[k] > n_ext[k] {
                    ge = true;
                    break;
                }
                if rem[k] < n_ext[k] {
                    ge = false;
                    break;
                }
            }
            if ge {
                let mut borrow: i128 = 0;
                for k in 0..M {
                    let v = (rem[k] as i128) - (n_ext[k] as i128) - borrow;
                    rem[k] = v as u64;
                    borrow = if v < 0 { 1 } else { 0 };
                }
            }
        }
        let mut out = [0u64; 6];
        out.copy_from_slice(&rem[..6]);
        out
    }

    fn is_zero(x: &[u64; 6]) -> bool {
        x.iter().all(|&v| v == 0)
    }

    #[test]
    fn p384_order_invert_times_self_is_one() {
        let inputs: [[u64; 6]; 4] = [
            [1, 0, 0, 0, 0, 0],
            [2, 0, 0, 0, 0, 0],
            [
                0x0123_4567_89ab_cdef,
                0xfedc_ba98_7654_3210,
                0xdead_beef,
                0x1,
                0x0,
                0x0,
            ],
            // n - 1
            [
                P384_N_6X64[0] - 1,
                P384_N_6X64[1],
                P384_N_6X64[2],
                P384_N_6X64[3],
                P384_N_6X64[4],
                P384_N_6X64[5],
            ],
        ];
        for (i, x) in inputs.iter().enumerate() {
            let mut xi = [0u64; 6];
            p384_order_invert_divstep_sat(&mut xi, x);
            assert!(!is_zero(&xi), "P-384 order: invert(x) = 0 for input {}", i);
            let prod = mul_mod_n_6(x, &xi, &P384_N_6X64);
            let one = [1u64, 0, 0, 0, 0, 0];
            assert_eq!(prod, one, "P-384 order: x · x^-1 != 1 for input {}", i);
        }
    }

    /// The modulus is 384 bits and odd, which is what `modinfo_from_6u64`
    /// and the 15 outer iterations require.
    #[test]
    fn p384_order_is_odd_and_384_bits() {
        assert_eq!(P384_N_6X64[0] & 1, 1);
        assert_eq!(P384_N_6X64[5] >> 63, 1);
        assert_eq!(P384_ORDER.outer_iters, 15);
        // ⌈(9437·384 + 1) / (4096·59)⌉ = ⌈3623809 / 241664⌉ = 15.
        let need = (9437u64 * 384 + 1).div_ceil(4096 * 59);
        assert_eq!(need as usize, P384_ORDER.outer_iters);
    }

    #[test]
    fn p384_order_invert_of_zero_is_zero() {
        let mut out = [1u64; 6];
        p384_order_invert_divstep_sat(&mut out, &[0u64; 6]);
        assert!(is_zero(&out));
    }
}
