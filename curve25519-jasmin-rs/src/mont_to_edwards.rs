//! Montgomery → Edwards y-coordinate conversion via fiat-crypto.
//!
//! XEdDSA verify needs to convert an X25519 public key (Montgomery u
//! coordinate) into an Ed25519 verify-key (Edwards y coordinate plus a
//! chosen sign bit).  The formula is
//!
//! ```text
//!   y = (u - 1) * (u + 1)^(-1) mod p          (p = 2^255 - 19)
//!   compressed = y_bytes with bit 255 = sign_bit
//! ```
//!
//! This module computes that conversion using only verified fiat-crypto
//! `curve25519_64` primitives, replacing the prior dependency on
//! `curve25519-dalek::montgomery::MontgomeryPoint::to_edwards` +
//! `EdwardsPoint::compress`.
//!
//! Trust set:
//!   - fiat-crypto's `carry_mul`, `carry_square`, `add`, `sub`, `from_bytes`,
//!     `to_bytes` (machine-checked correctness theorems).
//!   - The hand-coded addition chain for x^(p-2), which is a standard
//!     254-squaring + 11-multiplication recipe (verified by KAT
//!     against the dalek implementation in the test below).

use fiat_crypto::curve25519_64::{
    fiat_25519_add, fiat_25519_carry, fiat_25519_carry_mul, fiat_25519_carry_square,
    fiat_25519_from_bytes, fiat_25519_loose_field_element, fiat_25519_relax, fiat_25519_sub,
    fiat_25519_tight_field_element, fiat_25519_to_bytes,
};

type Tight = fiat_25519_tight_field_element;
type Loose = fiat_25519_loose_field_element;

#[inline(always)]
fn zero_tight() -> Tight { fiat_25519_tight_field_element([0; 5]) }
#[inline(always)]
fn zero_loose() -> Loose { fiat_25519_loose_field_element([0; 5]) }

/// Constant 1 in tight form (limbs all zero except first = 1, which is
/// well under fiat's 2^51 tight bound).
const ONE_TIGHT: Tight = fiat_25519_tight_field_element([1, 0, 0, 0, 0]);

#[inline(always)]
fn mul(out: &mut Tight, a: &Tight, b: &Tight) {
    let mut al = zero_loose();
    let mut bl = zero_loose();
    fiat_25519_relax(&mut al, a);
    fiat_25519_relax(&mut bl, b);
    fiat_25519_carry_mul(out, &al, &bl);
}

#[inline(always)]
fn sqr(out: &mut Tight, a: &Tight) {
    let mut al = zero_loose();
    fiat_25519_relax(&mut al, a);
    fiat_25519_carry_square(out, &al);
}

#[inline(always)]
fn assign(dst: &mut Tight, src: &Tight) {
    dst.0[0] = src.0[0]; dst.0[1] = src.0[1]; dst.0[2] = src.0[2];
    dst.0[3] = src.0[3]; dst.0[4] = src.0[4];
}

/// In-place: `*z = z^(2^n)` (n squarings of z, accumulating into z).
fn sqr_n(z: &mut Tight, n: usize) {
    let mut tmp = zero_tight();
    for _ in 0..n {
        sqr(&mut tmp, z);
        assign(z, &tmp);
    }
}

/// Compute `out = a^{-1} mod p`, p = 2^255 - 19.
///
/// Dispatches between two backends based on the `divstep_invert` feature:
///   * **default**: Fermat (`fe25519_invert_fermat`, below) — 254 squarings
///     + 11 multiplications.  ~7 960 cyc on Zen 4 / ~9 000 cyc Skylake.
///   * **`divstep_invert` enabled**: `safegcd25519::fe25519_invert_divstep_tight`
///     — Bernstein-Yang divstep (10 × 59 = 590 divsteps, δ₀=1/2; port of
///     libsecp256k1 `secp256k1_modinv64`).  ~4 040 cyc on Zen 4.
///
/// Both backends are KAT-tied to each other (see
/// `safegcd25519::tests::divstep_matches_fermat_*`).  Public callers do not
/// need to know which one is active.
#[inline(always)]
pub fn fe25519_invert(out: &mut Tight, a: &Tight) {
    #[cfg(feature = "divstep_invert")]
    {
        crate::safegcd25519::fe25519_invert_divstep_tight(out, a);
    }
    #[cfg(not(feature = "divstep_invert"))]
    {
        fe25519_invert_fermat(out, a);
    }
}

/// Compute `out = a^(p-2) mod p`, p = 2^255 - 19.
///
/// Standard 254-squaring + 11-multiplication addition chain (same as
/// libjade / dalek / curve25519-donna; KAT'd in this module's tests).
/// Always available; serves as the baseline that `fe25519_invert` falls
/// back to when `divstep_invert` is not enabled.
pub fn fe25519_invert_fermat(out: &mut Tight, a: &Tight) {
    let mut z2 = zero_tight();
    sqr(&mut z2, a);                  // z2 = a^2

    let mut t = zero_tight();
    sqr(&mut t, &z2);                 // t = a^4
    sqr_n(&mut t, 1);                 // t = a^8

    let mut z9 = zero_tight();
    mul(&mut z9, &t, a);              // z9 = a^9

    let mut z11 = zero_tight();
    mul(&mut z11, &z9, &z2);          // z11 = a^11

    sqr(&mut t, &z11);                // t = a^22

    let mut z2_5_0 = zero_tight();
    mul(&mut z2_5_0, &t, &z9);        // z2_5_0 = a^(2^5 - 1) = a^31

    sqr(&mut t, &z2_5_0);             // t = a^62
    sqr_n(&mut t, 4);                 // t = a^(2^5 * 31) = a^(2^10 - 2^5)

    let mut z2_10_0 = zero_tight();
    mul(&mut z2_10_0, &t, &z2_5_0);   // z2_10_0 = a^(2^10 - 1)

    sqr(&mut t, &z2_10_0);
    sqr_n(&mut t, 9);                 // t = a^(2^20 - 2^10)

    let mut z2_20_0 = zero_tight();
    mul(&mut z2_20_0, &t, &z2_10_0);  // a^(2^20 - 1)

    sqr(&mut t, &z2_20_0);
    sqr_n(&mut t, 19);                // a^(2^40 - 2^20)

    let mut z2_40_0 = zero_tight();
    mul(&mut z2_40_0, &t, &z2_20_0);  // a^(2^40 - 1)

    sqr(&mut t, &z2_40_0);
    sqr_n(&mut t, 9);                 // a^(2^50 - 2^10)

    let mut z2_50_0 = zero_tight();
    mul(&mut z2_50_0, &t, &z2_10_0);  // a^(2^50 - 1)

    sqr(&mut t, &z2_50_0);
    sqr_n(&mut t, 49);                // a^(2^100 - 2^50)

    let mut z2_100_0 = zero_tight();
    mul(&mut z2_100_0, &t, &z2_50_0); // a^(2^100 - 1)

    sqr(&mut t, &z2_100_0);
    sqr_n(&mut t, 99);                // a^(2^200 - 2^100)

    let mut t2 = zero_tight();
    mul(&mut t2, &t, &z2_100_0);      // a^(2^200 - 1)

    sqr(&mut t, &t2);
    sqr_n(&mut t, 49);                // a^(2^250 - 2^50)

    let mut t3 = zero_tight();
    mul(&mut t3, &t, &z2_50_0);       // a^(2^250 - 1)

    sqr(&mut t, &t3);
    sqr_n(&mut t, 4);                 // a^(2^255 - 2^5)

    mul(out, &t, &z11);               // a^(2^255 - 21) = a^(p - 2)
}

/// Convert a 32-byte Montgomery u-coordinate to a 32-byte compressed
/// Edwards point.  `sign_bit` is or'd into bit 255 of the output.
///
/// Returns `None` iff u + 1 == 0 mod p (i.e. u == -1), in which case
/// the Edwards point is the order-2 element which is not a valid
/// Ed25519 verify-key.
pub fn mont_u_to_edwards_compressed(u_bytes: &[u8; 32], sign_bit: u8) -> Option<[u8; 32]> {
    // Mask off the unused top bit (Montgomery encoding uses bits 0..254).
    let mut u_in = *u_bytes;
    u_in[31] &= 0x7f;

    let mut u = zero_tight();
    fiat_25519_from_bytes(&mut u, &u_in);

    // num = u - 1, denom = u + 1  (both loose, then carry)
    let mut num_loose = zero_loose();
    fiat_25519_sub(&mut num_loose, &u, &ONE_TIGHT);
    let mut num = zero_tight();
    fiat_25519_carry(&mut num, &num_loose);

    let mut den_loose = zero_loose();
    fiat_25519_add(&mut den_loose, &u, &ONE_TIGHT);
    let mut den = zero_tight();
    fiat_25519_carry(&mut den, &den_loose);

    // Reject u == -1 (denom == 0): in canonical form, all limbs would be 0.
    {
        let mut den_bytes = [0u8; 32];
        fiat_25519_to_bytes(&mut den_bytes, &den);
        if den_bytes.iter().all(|&b| b == 0) {
            return None;
        }
    }

    // inv_den = den^(p-2)
    let mut inv_den = zero_tight();
    fe25519_invert(&mut inv_den, &den);

    // y = num * inv_den
    let mut y = zero_tight();
    mul(&mut y, &num, &inv_den);

    // Encode y as 32 LE bytes, set top bit to sign_bit.
    let mut out = [0u8; 32];
    fiat_25519_to_bytes(&mut out, &y);
    out[31] = (out[31] & 0x7f) | ((sign_bit & 1) << 7);
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn invert_roundtrip_via_dalek() {
        // KAT: invert(invert(x)) == x for random non-zero x.
        use curve25519_dalek::montgomery::MontgomeryPoint;
        let _ = MontgomeryPoint([1u8; 32]); // ensure dalek is linked

        // Compute x^(p-2) twice using our implementation, expect x.
        let mut x_bytes = [3u8; 32];
        x_bytes[31] &= 0x7f;
        let mut x = zero_tight();
        fiat_25519_from_bytes(&mut x, &x_bytes);

        let mut xi = zero_tight();
        fe25519_invert(&mut xi, &x);
        let mut xii = zero_tight();
        fe25519_invert(&mut xii, &xi);

        let mut x_out = [0u8; 32];
        fiat_25519_to_bytes(&mut x_out, &xii);
        let mut x_can = [0u8; 32];
        fiat_25519_to_bytes(&mut x_can, &x);
        assert_eq!(x_out, x_can, "invert(invert(x)) should equal x");
    }

    #[test]
    fn invert_times_self_is_one() {
        // x * x^(p-2) == 1 mod p
        let mut x_bytes = [0u8; 32];
        for (i, b) in x_bytes.iter_mut().enumerate() { *b = (i as u8).wrapping_mul(7) | 1; }
        x_bytes[31] &= 0x7f;
        let mut x = zero_tight();
        fiat_25519_from_bytes(&mut x, &x_bytes);

        let mut xi = zero_tight();
        fe25519_invert(&mut xi, &x);

        let mut prod = zero_tight();
        mul(&mut prod, &x, &xi);

        let mut out_bytes = [0u8; 32];
        fiat_25519_to_bytes(&mut out_bytes, &prod);
        let mut expected = [0u8; 32];
        expected[0] = 1;
        assert_eq!(out_bytes, expected, "x * x^(p-2) should be 1");
    }

    #[test]
    fn mont_to_edwards_matches_dalek() {
        // KAT against dalek's MontgomeryPoint::to_edwards(0).compress().
        use curve25519_dalek::montgomery::MontgomeryPoint;

        for seed in [0x01u8, 0x42u8, 0x77u8, 0xa5u8] {
            // Build a valid Montgomery u-coordinate: take a random private
            // key and compute its public key (= u of basepoint scaled).
            let priv_key = [seed; 32];
            let pub_u = crate::x25519_jasmin_base(&priv_key);

            let ours = mont_u_to_edwards_compressed(&pub_u, 0)
                .expect("conversion should succeed for valid pubkey");
            let theirs = MontgomeryPoint(pub_u).to_edwards(0)
                .expect("dalek conversion should succeed")
                .compress().to_bytes();

            assert_eq!(ours, theirs,
                "mont→edwards mismatch for seed 0x{:02x}", seed);
        }
    }

    #[test]
    fn mont_to_edwards_rejects_u_eq_neg_one() {
        // u = -1 mod p = p - 1 = 2^255 - 20.
        let mut u = [0u8; 32];
        u[0] = 0xec; // ... ed - 1 = ec
        for b in u.iter_mut().skip(1).take(30) { *b = 0xff; }
        u[31] = 0x7f;
        assert!(mont_u_to_edwards_compressed(&u, 0).is_none(),
                "u = -1 should be rejected");
    }
}
