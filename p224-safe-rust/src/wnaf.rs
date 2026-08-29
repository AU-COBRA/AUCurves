//! HAND-WRITTEN GLUE around the Rocq-emitted wNAF scalar multiplication
//! in `scalar_mul_extracted.rs`.
//!
//! Verified / glue split for this path:
//!
//! | piece                            | status                          |
//! |----------------------------------|---------------------------------|
//! | the 225-iteration wNAF driver    | Rocq-emitted (`p224_wnaf_body`)  |
//! | the odd-multiples table build    | Rocq-emitted (inside the driver)|
//! | the complete point addition      | Rocq-emitted (`g1_extracted.rs`)|
//! | the field leaves                 | fiat-crypto (`p224_64.rs`)       |
//! | **the digit encoder below**      | **hand-written**                |
//! | **G1 <-> [u8; 96] (de)serialise**| **hand-written**              |
//!
//! `wnaf_digits_w4` is a transcription of `wnaf_digit` / `wnaf_shift` /
//! `wnaf_digits` in `src/Bedrock/Field/Synthesis/Examples/wNAF.v` at
//! `w = 4`, `len = 225`.  It has no Rocq-side extraction certificate;
//! it is checked against the emitted driver by
//! `tests/scalar_mul_diff.rs`.
//!
//! NOT CONSTANT TIME — see the header of `scalar_mul_extracted.rs`.

use crate::group::G1;
use crate::scalar_mul_extracted::p224_wnaf_scalar_mul_extracted;
use crate::Fp;

/// Digit count: `p224_wNAF_Instance.p224_num_digits`.
pub const NUM_DIGITS: usize = 225;

/// Window: `w = 4`, so digits lie in `{-7,-5,-3,-1,0,1,3,5,7}`.
pub const W: u32 = 4;

/// Scalar limbs (little-endian u64), matching `group::g1_scalar_mul`.
pub const LIMBS: usize = 4;

const ACC: usize = LIMBS + 1;

/// `k -= d` on an `ACC`-limb little-endian accumulator, `d` in `[-7, 7]`.
#[inline]
fn sub_small(k: &mut [u64; ACC], d: i64) {
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

/// `k >>= 1` on an `ACC`-limb little-endian accumulator.
#[inline]
fn shr1(k: &mut [u64; ACC]) {
    for i in 0..ACC - 1 {
        k[i] = (k[i] >> 1) | (k[i + 1] << 63);
    }
    k[ACC - 1] >>= 1;
}

/// `wnaf_digits 4 k 225` of `src/Bedrock/Field/Synthesis/Examples/wNAF.v`.
///
/// Each output word is the two's-complement 64-bit encoding of the signed
/// digit, i.e. `BLS12_wNAF_ProcessDigits.encode_digit` = `word.of_Z d`,
/// which is the representation the emitted driver's `arg2` expects.
pub fn wnaf_digits_w4(scalar: &[u64; LIMBS]) -> [u64; NUM_DIGITS] {
    let mut k = [0u64; ACC];
    k[..LIMBS].copy_from_slice(scalar);

    let mut out = [0u64; NUM_DIGITS];
    let modulus = 1i64 << W;
    let half = 1i64 << (W - 1);
    for slot in out.iter_mut() {
        let d: i64 = if k[0] & 1 == 1 {
            let m = (k[0] & (modulus as u64 - 1)) as i64;
            if m >= half { m - modulus } else { m }
        } else {
            0
        };
        *slot = d as u64;
        sub_small(&mut k, d);
        shr1(&mut k);
    }
    out
}

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
        let mut limbs = [0u64; LIMBS];
        for (i, limb) in limbs.iter_mut().enumerate() {
            let mut w = [0u8; 8];
            w.copy_from_slice(&b[off + 8 * i..off + 8 * i + 8]);
            *limb = u64::from_le_bytes(w);
        }
        Fp(limbs)
    };
    G1 { x: rd(0), y: rd(32), z: rd(64) }
}

/// Variable-base scalar multiplication `k * P` through the Rocq-emitted
/// w = 4 wNAF driver.  `k` is `4` little-endian u64 limbs, as for
/// [`crate::group::g1_scalar_mul`].
///
/// **Not constant time.**  For secret scalars use
/// [`crate::group::g1_scalar_mul`].
pub fn g1_scalar_mul_wnaf(k: &[u64; LIMBS], p: &G1) -> G1 {
    let mut digits = wnaf_digits_w4(k);
    let mut table = [[0u8; 96]; 4];
    let mut base = point_to_bytes(p);
    let mut out = [0u8; 96];
    p224_wnaf_scalar_mul_extracted(&mut out, &mut base, &mut table, &mut digits);
    point_from_bytes(&out)
}
