//! Scalar arithmetic mod `L`, the order of the Curve25519 basepoint.
//!
//! `L = 2^252 + 27742317777372353535851937790883648493`.
//!
//! Built on fiat-crypto's verified `curve25519_scalar_64` primitives.
//! Replaces the dalek `Scalar` type in xeddsa_sign so the trust set
//! does not include dalek's Scalar arithmetic.
//!
//! All public API mirrors what XEdDSA-sign needs: `from_bytes_mod_order`,
//! `from_bytes_mod_order_wide` (64 → 32-byte reduction for SHA-512
//! hashes), `negate`, `add`, `mul`, `to_bytes`.
//!
//! Trust set: fiat_25519_scalar_{mul, add, sub, opp, to_montgomery,
//! from_montgomery, to_bytes, from_bytes} (machine-checked).
//!
//! Internals: values are kept in Montgomery domain inside `Scalar25519`.

use fiat_crypto::curve25519_scalar_64::{
    fiat_25519_scalar_add, fiat_25519_scalar_from_bytes,
    fiat_25519_scalar_from_montgomery, fiat_25519_scalar_mul,
    fiat_25519_scalar_montgomery_domain_field_element,
    fiat_25519_scalar_non_montgomery_domain_field_element,
    fiat_25519_scalar_opp, fiat_25519_scalar_sub, fiat_25519_scalar_to_bytes,
    fiat_25519_scalar_to_montgomery,
};

type Mont = fiat_25519_scalar_montgomery_domain_field_element;
type NonMont = fiat_25519_scalar_non_montgomery_domain_field_element;

#[inline(always)]
fn zero_mont() -> Mont { fiat_25519_scalar_montgomery_domain_field_element([0; 4]) }
#[inline(always)]
fn zero_nm() -> NonMont { fiat_25519_scalar_non_montgomery_domain_field_element([0; 4]) }

#[derive(Copy, Clone)]
pub struct Scalar25519(pub(crate) Mont);

impl Scalar25519 {
    /// Build the zero scalar.
    pub fn zero() -> Self { Self(zero_mont()) }

    /// Build a scalar from a 32-byte little-endian non-Montgomery value.
    /// The input is interpreted as an integer mod `2^256` and then
    /// reduced mod L by `to_montgomery` (fiat's REDC handles values
    /// up to `2 * 2^256` correctly; in particular `< 2 * L` always
    /// reduces to canonical form).
    pub fn from_bytes_mod_order(bytes: &[u8; 32]) -> Self {
        let mut nm = zero_nm();
        fiat_25519_scalar_from_bytes(&mut nm.0, bytes);
        let mut m = zero_mont();
        fiat_25519_scalar_to_montgomery(&mut m, &nm);
        Self(m)
    }

    /// Reduce a 64-byte little-endian value mod L.
    ///
    /// Split: `wide = hi || lo` where each half is 32 bytes LE.
    /// `wide mod L = ((hi * 2^256) + lo) mod L = (hi * c256 + lo) mod L`
    /// where `c256 = 2^256 mod L`.
    ///
    /// We derive c256 via verified scalar ops as `-16 · L_extra mod L`,
    /// where `L_extra = L - 2^252 = 27742317...8493`:
    ///   2^256 = 16 · 2^252 ≡ 16 · (L - L_extra) ≡ -16 · L_extra  (mod L).
    /// This avoids hard-coding any large hex constants whose correctness
    /// could only be checked by inspection.
    pub fn from_bytes_mod_order_wide(bytes: &[u8; 64]) -> Self {
        let mut lo_bytes = [0u8; 32];
        let mut hi_bytes = [0u8; 32];
        lo_bytes.copy_from_slice(&bytes[..32]);
        hi_bytes.copy_from_slice(&bytes[32..]);

        let lo = Self::from_bytes_mod_order(&lo_bytes);
        let hi = Self::from_bytes_mod_order(&hi_bytes);

        // L_extra = L - 2^252 = 27742317777372353535851937790883648493
        // hex: 0x14def9dea2f79cd65812631a5cf5d3ed (128-bit value)
        // 32-byte LE encoding:
        const L_EXTRA_LE: [u8; 32] = [
            0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58,
            0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ];
        const SIXTEEN_LE: [u8; 32] = [
            16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ];
        let l_extra = Self::from_bytes_mod_order(&L_EXTRA_LE);
        let sixteen = Self::from_bytes_mod_order(&SIXTEEN_LE);
        let c256 = l_extra.mul(&sixteen).negate();   // = -16·L_extra mod L = 2^256 mod L

        // result = hi · c256 + lo
        hi.mul(&c256).add(&lo)
    }

    /// Negate this scalar mod L.
    pub fn negate(&self) -> Self {
        let mut out = zero_mont();
        fiat_25519_scalar_opp(&mut out, &self.0);
        Self(out)
    }

    /// Add two scalars mod L.
    pub fn add(&self, other: &Self) -> Self {
        let mut out = zero_mont();
        fiat_25519_scalar_add(&mut out, &self.0, &other.0);
        Self(out)
    }

    /// Multiply two scalars mod L.
    pub fn mul(&self, other: &Self) -> Self {
        let mut out = zero_mont();
        fiat_25519_scalar_mul(&mut out, &self.0, &other.0);
        Self(out)
    }

    /// Subtract one scalar from another mod L.
    pub fn sub(&self, other: &Self) -> Self {
        let mut out = zero_mont();
        fiat_25519_scalar_sub(&mut out, &self.0, &other.0);
        Self(out)
    }

    /// Encode as 32 LE bytes (canonical form, < L).
    pub fn to_bytes(&self) -> [u8; 32] {
        let mut nm = zero_nm();
        fiat_25519_scalar_from_montgomery(&mut nm, &self.0);
        let mut out = [0u8; 32];
        fiat_25519_scalar_to_bytes(&mut out, &nm.0);
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use curve25519_dalek::scalar::Scalar;

    fn rand_bytes(seed: u64) -> [u8; 32] {
        let mut b = [0u8; 32];
        let mut x = seed.wrapping_mul(0x9E3779B97F4A7C15);
        for chunk in b.chunks_mut(8) {
            x = x.wrapping_mul(0x6A09E667F3BCC909).wrapping_add(1);
            chunk.copy_from_slice(&x.to_le_bytes());
        }
        b
    }

    fn rand_bytes_64(seed: u64) -> [u8; 64] {
        let mut b = [0u8; 64];
        b[..32].copy_from_slice(&rand_bytes(seed));
        b[32..].copy_from_slice(&rand_bytes(seed.wrapping_add(1)));
        b
    }

    #[test]
    fn from_bytes_mod_order_matches_dalek() {
        for seed in 0..8u64 {
            let bytes = rand_bytes(seed);
            let ours = Scalar25519::from_bytes_mod_order(&bytes).to_bytes();
            let theirs = Scalar::from_bytes_mod_order(bytes).to_bytes();
            assert_eq!(ours, theirs, "from_bytes_mod_order divergence at seed {seed}");
        }
    }

    #[test]
    fn from_bytes_mod_order_wide_matches_dalek() {
        for seed in 0..8u64 {
            let bytes = rand_bytes_64(seed);
            let ours = Scalar25519::from_bytes_mod_order_wide(&bytes).to_bytes();
            let theirs = Scalar::from_bytes_mod_order_wide(&bytes).to_bytes();
            assert_eq!(ours, theirs, "from_bytes_mod_order_wide divergence at seed {seed}");
        }
    }

    #[test]
    fn add_matches_dalek() {
        for seed in 0..8u64 {
            let a = rand_bytes(seed);
            let b = rand_bytes(seed.wrapping_add(99));
            let ours = Scalar25519::from_bytes_mod_order(&a)
                .add(&Scalar25519::from_bytes_mod_order(&b))
                .to_bytes();
            let theirs = (Scalar::from_bytes_mod_order(a) + Scalar::from_bytes_mod_order(b))
                .to_bytes();
            assert_eq!(ours, theirs, "add divergence at seed {seed}");
        }
    }

    #[test]
    fn mul_matches_dalek() {
        for seed in 0..8u64 {
            let a = rand_bytes(seed);
            let b = rand_bytes(seed.wrapping_add(99));
            let ours = Scalar25519::from_bytes_mod_order(&a)
                .mul(&Scalar25519::from_bytes_mod_order(&b))
                .to_bytes();
            let theirs = (Scalar::from_bytes_mod_order(a) * Scalar::from_bytes_mod_order(b))
                .to_bytes();
            assert_eq!(ours, theirs, "mul divergence at seed {seed}");
        }
    }

    #[test]
    fn negate_matches_dalek() {
        for seed in 0..8u64 {
            let a = rand_bytes(seed);
            let ours = Scalar25519::from_bytes_mod_order(&a).negate().to_bytes();
            let theirs = (-Scalar::from_bytes_mod_order(a)).to_bytes();
            assert_eq!(ours, theirs, "negate divergence at seed {seed}");
        }
    }
}
