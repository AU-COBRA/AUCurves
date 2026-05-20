//! Bernstein-Yang divstep modular inversion mod P-256
//! = 2^256 − 2^224 + 2^192 + 2^96 − 1.
//!
//! KAT-tested against fiat-crypto's reference `fiat_p256_divstep` (per-step,
//! slow but proven correct) — see tests below.

use crate::safegcd::{self as sg, ModInfo, Signed62};

/// P-256 prime in 4×u64 little-endian.
pub const P256_P_4X64: [u64; 4] = [
    0xFFFF_FFFF_FFFF_FFFF,
    0x0000_0000_FFFF_FFFF,
    0x0000_0000_0000_0000,
    0xFFFF_FFFF_0000_0001,
];

pub const P256: ModInfo<5> = sg::modinfo_from_4u64(P256_P_4X64, 10);

/// `x^{-1} mod p256` on 4×u64 saturated input.
#[inline(never)]
pub fn p256_invert_divstep_sat(out: &mut [u64; 4], x: &[u64; 4]) {
    let x_lim: Signed62<5> = sg::from_saturated_4(x);
    let inv = sg::invert(x_lim, &P256);
    *out = sg::to_saturated_4(&inv);
}

#[cfg(test)]
mod tests {
    use super::*;
    use fiat_crypto::p256_64::{
        fiat_p256_divstep, fiat_p256_divstep_precomp, fiat_p256_from_montgomery,
        fiat_p256_montgomery_domain_field_element, fiat_p256_msat, fiat_p256_mul,
        fiat_p256_non_montgomery_domain_field_element, fiat_p256_opp, fiat_p256_selectznz,
        fiat_p256_set_one, fiat_p256_to_montgomery,
    };

    /// Reference P-256 inversion via fiat-crypto's per-step divstep.
    /// Slow but proven correct via fiat-crypto's machine-checked synthesis.
    fn p256_invert_fiat(out: &mut [u64; 4], x_nm: &[u64; 4]) {
        // x must be in non-Montgomery domain.  We pass x_nm directly.
        let mut precomp = fiat_p256_montgomery_domain_field_element([0; 4]);
        fiat_p256_divstep_precomp(&mut precomp.0);

        let mut d: u64 = 1;
        let mut f = [0u64; 5];
        fiat_p256_msat(&mut f);
        let mut g = [0u64; 5];
        g[0] = x_nm[0];
        g[1] = x_nm[1];
        g[2] = x_nm[2];
        g[3] = x_nm[3];
        g[4] = 0;
        let mut r = fiat_p256_montgomery_domain_field_element([0; 4]);
        fiat_p256_set_one(&mut r);
        let mut v = fiat_p256_montgomery_domain_field_element([0; 4]);

        let mut t_d: u64 = 0;
        let mut t_f = [0u64; 5];
        let mut t_g = [0u64; 5];
        let mut t_v = fiat_p256_montgomery_domain_field_element([0; 4]);
        let mut t_r = fiat_p256_montgomery_domain_field_element([0; 4]);

        const ITERS: usize = 741;
        for _ in 0..(ITERS / 2) {
            fiat_p256_divstep(
                &mut t_d, &mut t_f, &mut t_g, &mut t_v.0, &mut t_r.0,
                d, &f, &g, &v.0, &r.0,
            );
            fiat_p256_divstep(
                &mut d, &mut f, &mut g, &mut v.0, &mut r.0,
                t_d, &t_f, &t_g, &t_v.0, &t_r.0,
            );
        }
        if ITERS & 1 != 0 {
            fiat_p256_divstep(
                &mut t_d, &mut t_f, &mut t_g, &mut t_v.0, &mut t_r.0,
                d, &f, &g, &v.0, &r.0,
            );
            v = t_v;
            f = t_f;
        }

        let sign_bit = ((f[4] >> 63) & 1) as u8;
        let mut v_neg = fiat_p256_montgomery_domain_field_element([0; 4]);
        fiat_p256_opp(&mut v_neg, &v);
        let mut v_fixed = fiat_p256_montgomery_domain_field_element([0; 4]);
        fiat_p256_selectznz(&mut v_fixed.0, sign_bit, &v.0, &v_neg.0);

        let mut out_mont = fiat_p256_montgomery_domain_field_element([0; 4]);
        fiat_p256_mul(&mut out_mont, &v_fixed, &precomp);

        // Bring back to non-Montgomery for comparison with our divstep output.
        let mut out_nm = fiat_p256_non_montgomery_domain_field_element([0; 4]);
        fiat_p256_from_montgomery(&mut out_nm, &out_mont);
        *out = out_nm.0;
    }

    #[test]
    fn p256_divstep_matches_fiat_reference() {
        let inputs: [[u64; 4]; 5] = [
            [1, 0, 0, 0],
            [2, 0, 0, 0],
            [0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210, 0xdead_beef, 0x1],
            [
                0xa1b2_c3d4_e5f6_0708,
                0x1122_3344_5566_7788,
                0x99aa_bbcc_ddee_ff00,
                0x0011_2233_4455_6677,
            ],
            // p - 1
            [
                P256_P_4X64[0] - 1,
                P256_P_4X64[1],
                P256_P_4X64[2],
                P256_P_4X64[3],
            ],
        ];

        for (i, x) in inputs.iter().enumerate() {
            let mut ours = [0u64; 4];
            p256_invert_divstep_sat(&mut ours, x);
            let mut theirs = [0u64; 4];
            p256_invert_fiat(&mut theirs, x);
            assert_eq!(
                ours, theirs,
                "divstep != fiat reference for input {}: x={:?}, ours={:?}, theirs={:?}",
                i, x, ours, theirs
            );
        }
    }
}
