//! Bernstein–Yang divstep modular inversion — proxy benchmark for fe25519_invert.
//!
//! Uses fiat-crypto's verified `curve25519_scalar_64` divstep primitives to
//! compute inverses mod L = 2^252 + 27742317777372353535851937790883648493.
//! L is a 253-bit prime, comparable in size to p25519 = 2^255 - 19 (255 bits).
//!
//! # Purpose
//!
//! The current fe25519_invert (in `mont_to_edwards.rs`) is the 254-square +
//! 11-multiplication Fermat addition chain.  Switching to divstep (per the
//! EUROCRYPT 2026 paper by Bernstein–Chen–Harrison–Huang–Maxwell–Wang–
//! Wuille–Yang) would require running fiat-crypto's WordByWordMontgomery
//! generator on p25519 to obtain `fiat_25519_divstep` + `_msat` + `_divstep_precomp`,
//! plus mirroring the wiring pattern of `AUCurves/src/Implementations/C/bls12_by_inv.c`.
//!
//! Before doing that work, this file provides a realistic cycle-count
//! estimate by running the **identical algorithm** on the **near-identical-size**
//! scalar prime L.  The cycle count here is representative of what an
//! analogous p25519 implementation would achieve.
//!
//! # Reference
//!
//! Mirrors `AUCurves/src/Implementations/C/bls12_by_inv.c::by_fp_inv`, which
//! is the BLS12-381 divstep inverter wired into `bls12-jasmin-rs::pairing::fp_inv`.

use fiat_crypto::curve25519_scalar_64::{
    fiat_25519_scalar_divstep, fiat_25519_scalar_divstep_precomp,
    fiat_25519_scalar_from_montgomery, fiat_25519_scalar_montgomery_domain_field_element,
    fiat_25519_scalar_msat, fiat_25519_scalar_mul,
    fiat_25519_scalar_non_montgomery_domain_field_element, fiat_25519_scalar_opp,
    fiat_25519_scalar_selectznz, fiat_25519_scalar_set_one,
};

/// Number of divstep iterations for L (253-bit prime).
///
/// Bernstein–Yang Theorem 11.2 (CHES 2019) bound: floor((49·n + 80)/17)
/// suffices for n ≥ 46.  For n = 253: floor((49·253 + 80)/17) = floor(12477/17) = 733.
///
/// The paper this file's port targets (EUROCRYPT 2026) tightens this to
/// ceil((9437·n + 1)/4096) ≈ 2.304·n by using δ₀ = 1/2.  For n = 256 this
/// gives 590 (down from 724 with δ₀ = 1).  Applied to n = 253: ceil(2389817/4096) = 584.
/// This file uses 741 (matching `bls12_by_inv.c`'s loose constant for the
/// δ₀ = 1 case) so the proxy reflects the *current* fiat-crypto template —
/// the new paper's win would multiply both Fermat-vs-divstep and divstep-old-vs-new.
const BY_ITERATIONS: usize = 741;

/// Bernstein-Yang divstep inversion mod L.
///
/// Input and output are in Montgomery domain (same convention as
/// `fiat_25519_scalar_mul`).  If the input is 0 mod L, output is 0.
///
/// Constant-time: the iteration count is fixed, all branches inside
/// `fiat_25519_scalar_divstep` are constant-time (selectznz-based).
#[inline(never)]
pub fn scalar_invert_divstep(
    out: &mut fiat_25519_scalar_montgomery_domain_field_element,
    x: &fiat_25519_scalar_montgomery_domain_field_element,
) {
    // precomp = ((L+1)/2)^iterations mod L, in Montgomery form.
    // fiat-crypto generates this constant inline (no runtime computation).
    let mut precomp = fiat_25519_scalar_montgomery_domain_field_element([0; 4]);
    fiat_25519_scalar_divstep_precomp(&mut precomp.0);

    // Initial δ = 1 (encoded as u64 = 1).
    let mut d: u64 = 1;

    // f := saturated representation of L (5 × u64, sign-extended).
    let mut f = [0u64; 5];
    fiat_25519_scalar_msat(&mut f);

    // g := input in non-Montgomery (standard) form, zero-extended to 5 limbs.
    let mut g_nm = fiat_25519_scalar_non_montgomery_domain_field_element([0; 4]);
    fiat_25519_scalar_from_montgomery(&mut g_nm, x);
    let mut g = [0u64; 5];
    g[0] = g_nm.0[0];
    g[1] = g_nm.0[1];
    g[2] = g_nm.0[2];
    g[3] = g_nm.0[3];
    g[4] = 0;

    // r := 1 (in Montgomery domain).
    let mut r = fiat_25519_scalar_montgomery_domain_field_element([0; 4]);
    fiat_25519_scalar_set_one(&mut r);

    // v := 0 (in Montgomery domain).
    let mut v = fiat_25519_scalar_montgomery_domain_field_element([0; 4]);

    // Ping-pong scratch slots (avoid memcpy per step, mirroring bls12_by_inv.c).
    let mut t_d: u64 = 0;
    let mut t_f = [0u64; 5];
    let mut t_g = [0u64; 5];
    let mut t_v = fiat_25519_scalar_montgomery_domain_field_element([0; 4]);
    let mut t_r = fiat_25519_scalar_montgomery_domain_field_element([0; 4]);

    let pairs = BY_ITERATIONS / 2;
    for _ in 0..pairs {
        fiat_25519_scalar_divstep(
            &mut t_d, &mut t_f, &mut t_g, &mut t_v.0, &mut t_r.0,
            d, &f, &g, &v.0, &r.0,
        );
        fiat_25519_scalar_divstep(
            &mut d, &mut f, &mut g, &mut v.0, &mut r.0,
            t_d, &t_f, &t_g, &t_v.0, &t_r.0,
        );
    }
    if BY_ITERATIONS & 1 != 0 {
        fiat_25519_scalar_divstep(
            &mut t_d, &mut t_f, &mut t_g, &mut t_v.0, &mut t_r.0,
            d, &f, &g, &v.0, &r.0,
        );
        v = t_v;
        f = t_f;
    }

    // Sign correction: if f's top limb has its sign bit set, negate v.
    let sign_bit = ((f[4] >> 63) & 1) as u8;
    let mut v_neg = fiat_25519_scalar_montgomery_domain_field_element([0; 4]);
    fiat_25519_scalar_opp(&mut v_neg, &v);
    let mut v_fixed = fiat_25519_scalar_montgomery_domain_field_element([0; 4]);
    fiat_25519_scalar_selectznz(&mut v_fixed.0, sign_bit, &v.0, &v_neg.0);

    // Final: out = v_fixed * precomp (Montgomery multiplication).
    fiat_25519_scalar_mul(out, &v_fixed, &precomp);
}

#[cfg(test)]
mod tests {
    use super::*;
    use fiat_crypto::curve25519_scalar_64::{
        fiat_25519_scalar_from_bytes, fiat_25519_scalar_to_montgomery,
    };

    #[test]
    fn invert_times_self_is_one() {
        // KAT: x · scalar_invert_divstep(x) ≡ 1 (mod L).
        let mut s_bytes = [0u8; 32];
        for (i, b) in s_bytes.iter_mut().enumerate() {
            *b = (i as u8).wrapping_mul(11) | 1;
        }
        // Force into canonical range by clearing the top bits.
        s_bytes[31] &= 0x0f;

        let mut nm = fiat_25519_scalar_non_montgomery_domain_field_element([0; 4]);
        fiat_25519_scalar_from_bytes(&mut nm.0, &s_bytes);
        let mut x = fiat_25519_scalar_montgomery_domain_field_element([0; 4]);
        fiat_25519_scalar_to_montgomery(&mut x, &nm);

        let mut xi = fiat_25519_scalar_montgomery_domain_field_element([0; 4]);
        scalar_invert_divstep(&mut xi, &x);

        let mut prod = fiat_25519_scalar_montgomery_domain_field_element([0; 4]);
        fiat_25519_scalar_mul(&mut prod, &x, &xi);

        let mut one = fiat_25519_scalar_montgomery_domain_field_element([0; 4]);
        fiat_25519_scalar_set_one(&mut one);
        assert_eq!(prod.0, one.0, "x * inv_divstep(x) should equal 1 mod L");
    }
}
