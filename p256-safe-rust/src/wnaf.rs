//! HAND-WRITTEN GLUE around the Rocq-emitted wNAF scalar multiplication
//! in `scalar_mul_extracted.rs`.
//!
//! Verified / glue split for this path:
//!
//! | piece                            | status                          |
//! |----------------------------------|---------------------------------|
//! | the 257-iteration wNAF driver    | Rocq-emitted (`p256_wnaf_body`) |
//! | the odd-multiples table build    | Rocq-emitted (inside the driver)|
//! | the complete point addition      | Rocq-emitted (`g1_extracted.rs`)|
//! | the field leaves                 | fiat-crypto (`p256_64.rs`)      |
//! | **the digit encoder below**      | **hand-written**                |
//! | **G1 <-> [u8; 96] (de)serialise**| **hand-written**                |
//!
//! `wnaf_digits_w4` is a transcription of `wnaf_digit` / `wnaf_shift` /
//! `wnaf_digits` in `src/Bedrock/Field/Synthesis/Examples/wNAF.v` at
//! `w = 4`, `len = 257`.  It has no Rocq-side extraction certificate;
//! it is checked against the emitted driver's output by the
//! `tests/scalar_mul_diff.rs` differential test and by the
//! `digits_reconstruct_scalar` unit test below, which re-sums
//! `sum d_i 2^i` and compares with the input scalar (the Gallina
//! statement `wnaf_correct` / `P256_wNAF_Instance.p256_digits_wsum`).
//!
//! NOT CONSTANT TIME — see the header of `scalar_mul_extracted.rs`.

use crate::group::G1;
use crate::scalar_mul_extracted::p256_wnaf_scalar_mul_extracted;
use crate::Fp;

/// Digit count: `P256_wNAF_Instance.p256_num_digits`.
pub const NUM_DIGITS: usize = 257;

/// Window: `w = 4`, so digits lie in `{-7,-5,-3,-1,0,1,3,5,7}`.
pub const W: u32 = 4;

// ---------------------------------------------------------------------------
// wNAF digit expansion (hand-written)
// ---------------------------------------------------------------------------

/// `k -= d` on a 5-limb little-endian accumulator, `d` in `[-7, 7]`.
#[inline]
fn sub_small(k: &mut [u64; 5], d: i64) {
    if d >= 0 {
        let mut borrow = d as u64;
        for limb in k.iter_mut() {
            let (v, b) = limb.overflowing_sub(borrow);
            *limb = v;
            borrow = b as u64;
        }
    } else {
        let mut carry = (-d) as u64;
        for limb in k.iter_mut() {
            let (v, c) = limb.overflowing_add(carry);
            *limb = v;
            carry = c as u64;
        }
    }
}

/// `k >>= 1` on a 5-limb little-endian accumulator.
#[inline]
fn shr1(k: &mut [u64; 5]) {
    for i in 0..4 {
        k[i] = (k[i] >> 1) | (k[i + 1] << 63);
    }
    k[4] >>= 1;
}

/// `wnaf_digits 4 k 257` of `src/Bedrock/Field/Synthesis/Examples/wNAF.v`,
/// for a 256-bit big-endian scalar.
///
/// Each output word is the two's-complement 64-bit encoding of the signed
/// digit, i.e. `BLS12_wNAF_ProcessDigits.encode_digit` = `word.of_Z d`,
/// which is the representation the emitted driver's `arg2` expects.
pub fn wnaf_digits_w4(scalar_be: &[u8; 32]) -> [u64; NUM_DIGITS] {
    // 5 limbs: k stays below 2^256 + 7 throughout (a negative digit adds
    // at most 7 before the halving).
    let mut k = [0u64; 5];
    for i in 0..4 {
        let mut w = [0u8; 8];
        w.copy_from_slice(&scalar_be[24 - 8 * i..32 - 8 * i]);
        k[i] = u64::from_be_bytes(w);
    }

    let mut out = [0u64; NUM_DIGITS];
    let modulus = 1i64 << W; // 2^w = 16
    let half = 1i64 << (W - 1); // 2^(w-1) = 8
    for slot in out.iter_mut() {
        // wnaf_digit 4 k
        let d: i64 = if k[0] & 1 == 1 {
            let m = (k[0] & (modulus as u64 - 1)) as i64; // k mod 2^w
            if m >= half {
                m - modulus
            } else {
                m
            }
        } else {
            0
        };
        *slot = d as u64;
        // wnaf_shift 4 k = (k - d) / 2   (k - d is even, so exact)
        sub_small(&mut k, d);
        shr1(&mut k);
    }
    out
}

// ---------------------------------------------------------------------------
// Point serialisation (hand-written)
// ---------------------------------------------------------------------------

/// `G1 -> X || Y || Z`, 32 little-endian Montgomery bytes each — the
/// memory image of `BLS12_wNAF_ProcessDigits.TablePoint`.
pub fn point_to_bytes(p: &G1) -> [u8; 96] {
    let mut out = [0u8; 96];
    for (i, w) in p.x.0.iter().enumerate() {
        out[8 * i..8 * i + 8].copy_from_slice(&w.to_le_bytes());
    }
    for (i, w) in p.y.0.iter().enumerate() {
        out[32 + 8 * i..32 + 8 * i + 8].copy_from_slice(&w.to_le_bytes());
    }
    for (i, w) in p.z.0.iter().enumerate() {
        out[64 + 8 * i..64 + 8 * i + 8].copy_from_slice(&w.to_le_bytes());
    }
    out
}

/// Inverse of [`point_to_bytes`].
pub fn point_from_bytes(b: &[u8; 96]) -> G1 {
    let rd = |off: usize| {
        let mut limbs = [0u64; 4];
        for (i, limb) in limbs.iter_mut().enumerate() {
            let mut w = [0u8; 8];
            w.copy_from_slice(&b[off + 8 * i..off + 8 * i + 8]);
            *limb = u64::from_le_bytes(w);
        }
        Fp(limbs)
    };
    G1 {
        x: rd(0),
        y: rd(32),
        z: rd(64),
    }
}

// ---------------------------------------------------------------------------
// The public entry point
// ---------------------------------------------------------------------------

/// Variable-base scalar multiplication `k * P` through the Rocq-emitted
/// w = 4 wNAF driver.
///
/// `scalar` is 32 bytes, big-endian, and must be `< 2^256` (it always is).
///
/// **Not constant time.**  The emitted driver branches on each wNAF digit
/// and indexes its 4-entry table at a digit-derived index.  For secret
/// scalars use [`crate::group::g1_scalar_mul`], which is
/// double-and-add-always with a limb-mask select.
pub fn g1_scalar_mul_wnaf(scalar: &[u8; 32], p: &G1) -> G1 {
    let mut digits = wnaf_digits_w4(scalar);
    let mut table = [[0u8; 96]; 4];
    let mut base = point_to_bytes(p);
    let mut out = [0u8; 96];
    p256_wnaf_scalar_mul_extracted(&mut out, &mut base, &mut table, &mut digits);
    point_from_bytes(&out)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `wsum (wnaf_digits 4 k 257) = k` — the Gallina statement
    /// `P256_wNAF_Instance.p256_digits_wsum`, checked numerically.
    #[test]
    fn digits_reconstruct_scalar() {
        // Re-sum sum_i d_i 2^i in a 320-bit signed-magnitude accumulator.
        fn wsum(digits: &[u64; NUM_DIGITS]) -> [u64; 5] {
            let mut acc = [0u64; 5];
            // Horner from the top: acc = 2*acc + d_i
            for i in (0..NUM_DIGITS).rev() {
                // acc *= 2
                let mut carry = 0u64;
                for limb in acc.iter_mut() {
                    let nc = *limb >> 63;
                    *limb = (*limb << 1) | carry;
                    carry = nc;
                }
                let d = digits[i] as i64;
                if d >= 0 {
                    let mut c = d as u64;
                    for limb in acc.iter_mut() {
                        let (v, o) = limb.overflowing_add(c);
                        *limb = v;
                        c = o as u64;
                    }
                } else {
                    let mut b = (-d) as u64;
                    for limb in acc.iter_mut() {
                        let (v, o) = limb.overflowing_sub(b);
                        *limb = v;
                        b = o as u64;
                    }
                }
            }
            acc
        }

        let mut k = [0u8; 32];
        for (i, b) in k.iter_mut().enumerate() {
            *b = (i as u8).wrapping_mul(37).wrapping_add(11);
        }
        for trial in 0..64u32 {
            k[0] = (trial as u8).wrapping_mul(3);
            let digits = wnaf_digits_w4(&k);
            let got = wsum(&digits);
            let mut want = [0u64; 5];
            for i in 0..4 {
                let mut w = [0u8; 8];
                w.copy_from_slice(&k[24 - 8 * i..32 - 8 * i]);
                want[i] = u64::from_be_bytes(w);
            }
            assert_eq!(got, want, "wsum mismatch for trial {trial}");
        }
    }

    /// Digits are bounded and odd-or-zero:
    /// `P256_wNAF_Instance.p256_digits_bounded` / `p256_digits_odd`.
    #[test]
    fn digits_bounded_and_odd() {
        let mut k = [0u8; 32];
        for (i, b) in k.iter_mut().enumerate() {
            *b = (i as u8).wrapping_mul(91).wrapping_add(3);
        }
        for trial in 0..64u32 {
            k[31] = trial as u8;
            for d in wnaf_digits_w4(&k).iter() {
                let d = *d as i64;
                assert!((-7..=7).contains(&d), "digit {d} out of range");
                assert!(d == 0 || d % 2 != 0, "digit {d} nonzero and even");
            }
        }
    }
}
