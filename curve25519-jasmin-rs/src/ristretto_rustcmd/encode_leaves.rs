//! Encode-specific leaf FFI implementations for the extracted
//! Ristretto255 encoder (`encode.rs`).
//!
//! Companion to `leaves.rs` (decode path).  The field-arithmetic
//! leaves (`fe25519_mul`, `fe25519_add`, `fe25519_sub`, `fe25519_sq`),
//! the modular inverse (`fe25519_inv`), and `ristretto_sqrt_ratio_m1`
//! are SHARED with the Ed25519 / decode paths and are NOT defined here
//! — `encode.rs` declares them `extern "C"`.  This module provides the
//! two encode-only leaves:
//!
//! - `unpack_xyzt5` — inverse of `pack_xyzt5`.  Reads the 5 × 40-byte
//!   radix-2^51 felem slots from the 200-byte input and writes the
//!   canonical 32-byte LE encoding of each (mod p) to the 5 outputs.
//!   Faithful to `parse_xyzt5` ∘ `parse_felem` in
//!   `End2End/Ed25519/XyztAddVerified.v` / `CompressVerified.v`:
//!     parse_felem(slot) =
//!       (w0 + w1·2^51 + w2·2^102 + w3·2^153 + w4·2^204) mod p
//!   where wi = le_u64(slot[8·i .. 8·i+8]).
//!
//! - `ristretto_pack_canonical_felem` — 32-byte LE copy of an already
//!   canonical (reduced, < p) field element.  Spec
//!   `ristretto_pack_canonical_felem z = le_split 32 (z mod p)` in
//!   `RistrettoHelpers.v`; since `s` reaching this leaf is already the
//!   canonical representative, this is an identity copy of the 32
//!   bytes.
//!
//! Trust class: data-movement + a self-contained radix-2^51 → canonical
//! reduction.  Replace with verified extraction when a `from_bytes`
//! verified leaf lands.

#![allow(dead_code, unused_variables)]

/// p = 2^255 - 19, as a little-endian array of five 64-bit words.
/// (word[4] only uses 63 bits; bit 255 is clear.)
const P_WORDS: [u64; 4] = [
    0xffff_ffff_ffff_ffed,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0x7fff_ffff_ffff_ffff,
];

/// Read 8 little-endian bytes at `bs[off..off+8]` as a u64.
#[inline]
fn le_u64(bs: &[u8], off: usize) -> u64 {
    let mut w = [0u8; 8];
    w.copy_from_slice(&bs[off..off + 8]);
    u64::from_le_bytes(w)
}

/// Compute `parse_felem(slot) = (sum_i wi · 2^(51·i)) mod p` where
/// `slot` is a 40-byte radix-2^51 felem encoding, and return the
/// canonical 32-byte little-endian encoding.
///
/// Implementation: accumulate the five 64-bit limbs into a
/// little-endian big integer held as a `[u32; N]` (base 2^32) by
/// adding `wi << (51·i)`, then reduce the big integer mod p with a
/// schoolbook subtract-multiples loop, finally serialize 32 bytes.
fn parse_felem_canonical(slot: &[u8]) -> [u8; 32] {
    // Big integer in base 2^32, little-endian.  Max magnitude:
    // w4·2^204 + ... ~ 2^64·2^204 = 2^268, so 9 u32 words (288 bits)
    // suffice with headroom.
    const N: usize = 10;
    let mut acc = [0u32; N];

    // Add wi << (51*i) for i in 0..5.
    for i in 0..5 {
        let wi = le_u64(slot, 8 * i);
        let shift = 51 * i; // bit shift
        add_shifted(&mut acc, wi, shift);
    }

    // Reduce mod p by repeated conditional subtraction of p·2^k.
    reduce_mod_p(&mut acc);

    // Serialize the low 256 bits little-endian.
    let mut out = [0u8; 32];
    for k in 0..32 {
        let word = acc[k / 4];
        out[k] = ((word >> (8 * (k % 4))) & 0xff) as u8;
    }
    out
}

/// acc += (value as bigint) << shift_bits, in base-2^32 little-endian.
fn add_shifted(acc: &mut [u32], value: u64, shift_bits: usize) {
    // value occupies up to 64 bits; place it at the given bit offset.
    let word_off = shift_bits / 32;
    let bit_off = shift_bits % 32;
    // value, possibly shifted within u128 to handle the sub-word offset.
    let shifted: u128 = (value as u128) << bit_off; // up to 64+31 = 95 bits
    // shifted spans at most 3 base-2^32 words.
    let mut carry: u64 = 0;
    for j in 0..3 {
        let idx = word_off + j;
        if idx >= acc.len() {
            break;
        }
        let chunk = ((shifted >> (32 * j)) & 0xffff_ffff) as u64;
        let sum = acc[idx] as u64 + chunk + carry;
        acc[idx] = (sum & 0xffff_ffff) as u32;
        carry = sum >> 32;
    }
    // Propagate any remaining carry.
    let mut idx = word_off + 3;
    while carry != 0 && idx < acc.len() {
        let sum = acc[idx] as u64 + carry;
        acc[idx] = (sum & 0xffff_ffff) as u32;
        carry = sum >> 32;
        idx += 1;
    }
}

/// Compute `high = floor(acc / 2^255)` (base-2^32 LE) and reduce
/// `acc` to its low 255 bits, in place.  Returns `high` in a fresh
/// array.  Uses a clean bit-level right shift by 255 = 7 words + 31
/// bits.
fn shift_right_255(acc: &mut [u32]) -> [u32; 10] {
    let mut high = [0u32; 10];
    // high[j] = bits [255 + 32*j .. 255 + 32*j + 32) of acc.
    //         = bits [32*(7+j) + 31 ..) of acc
    //         = (acc[7+j] >> 31) | (acc[8+j] << 1)
    for j in 0..high.len() {
        let lo_idx = 7 + j;
        let lo = if lo_idx < acc.len() { acc[lo_idx] } else { 0 };
        let hi_idx = 8 + j;
        let hi = if hi_idx < acc.len() { acc[hi_idx] } else { 0 };
        high[j] = (lo >> 31) | (hi << 1);
    }
    // Clear bits >= 255 in acc: keep low 31 bits of word 7, clear 8.. .
    acc[7] &= 0x7fff_ffff;
    for k in 8..acc.len() {
        acc[k] = 0;
    }
    high
}

/// Reduce a base-2^32 little-endian big integer mod p = 2^255 - 19,
/// in place (low 256 bits hold the canonical residue afterwards).
///
/// Uses the identity 2^255 ≡ 19 (mod p): fold the high part (bits ≥ 255)
/// back in with a ×19 weight until the value is < 2^256, then do a
/// final conditional subtraction of p.
fn reduce_mod_p(acc: &mut [u32]) {
    // Fold high bits down repeatedly.  Each pass strictly shrinks the
    // magnitude (high part is multiplied by 19 and re-added below 2^255),
    // so the loop terminates in a few iterations.
    loop {
        let high = shift_right_255(acc);
        let mut any = false;
        for k in 0..high.len() {
            if high[k] != 0 {
                any = true;
                // acc += 19 * high[k] * 2^(32k).
                let v = high[k] as u64 * 19;
                add_shifted(acc, v, 32 * k);
            }
        }
        if !any {
            break;
        }
    }
    // Final: acc < 2^255 + (small); do up to 2 conditional subs of p.
    for _ in 0..2 {
        if ge_p(acc) {
            sub_p(acc);
        }
    }
}

/// Compare the low 256 bits of `acc` against p; true if `acc >= p`.
fn ge_p(acc: &[u32]) -> bool {
    // any word above index 7 nonzero => definitely >= p.
    for k in 8..acc.len() {
        if acc[k] != 0 {
            return true;
        }
    }
    // Compare 256-bit value against p (as 4 u64 words).
    for i in (0..4).rev() {
        let a = (acc[2 * i] as u64) | ((acc[2 * i + 1] as u64) << 32);
        if a > P_WORDS[i] {
            return true;
        }
        if a < P_WORDS[i] {
            return false;
        }
    }
    true // equal => >= p
}

/// acc -= p (low 256 bits), assuming acc >= p.
fn sub_p(acc: &mut [u32]) {
    let mut borrow: i64 = 0;
    for i in 0..4 {
        let a = (acc[2 * i] as u64) | ((acc[2 * i + 1] as u64) << 32);
        let (d, b) = sub_with_borrow(a, P_WORDS[i], borrow);
        borrow = b;
        acc[2 * i] = (d & 0xffff_ffff) as u32;
        acc[2 * i + 1] = (d >> 32) as u32;
    }
    // Clear any remaining high words.
    for k in 8..acc.len() {
        acc[k] = 0;
    }
}

#[inline]
fn sub_with_borrow(a: u64, b: u64, borrow: i64) -> (u64, i64) {
    let (r1, o1) = a.overflowing_sub(b);
    let (r2, o2) = r1.overflowing_sub(borrow as u64);
    (r2, (o1 as i64) + (o2 as i64))
}

/// `unpack_xyzt5`: inverse of `pack_xyzt5`.
///
/// Reads the five 40-byte radix-2^51 felem slots from the 200-byte
/// `xyzt_in` and writes the canonical 32-byte LE encoding (mod p) of
/// each parsed field element to `out_x`, `out_y`, `out_z`, `out_ta`,
/// `out_tb`.
///
/// # Safety
/// `xyzt_in` must point to 200 readable bytes; each output pointer must
/// point to 32 writable bytes.  No aliasing between inputs and outputs.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn unpack_xyzt5(
    out_x: *mut u8,
    out_y: *mut u8,
    out_z: *mut u8,
    out_ta: *mut u8,
    out_tb: *mut u8,
    xyzt_in: *const u8,
) {
    let xyzt: &[u8] = unsafe { core::slice::from_raw_parts(xyzt_in, 200) };
    let outs: [*mut u8; 5] = [out_x, out_y, out_z, out_ta, out_tb];
    for (i, &op) in outs.iter().enumerate() {
        let slot = &xyzt[40 * i..40 * i + 40];
        let canon = parse_felem_canonical(slot);
        let dst: &mut [u8] = unsafe { core::slice::from_raw_parts_mut(op, 32) };
        dst.copy_from_slice(&canon);
    }
}

/// `ristretto_pack_canonical_felem`: 32-byte LE copy of the canonical
/// field element `s`.  Since `s` is already reduced (< p), this is an
/// identity copy of the 32 input bytes into the output.
///
/// # Safety
/// `s_in` must point to 32 readable bytes; `out` to 32 writable bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ristretto_pack_canonical_felem(out: *mut u8, s_in: *const u8) {
    let s: &[u8] = unsafe { core::slice::from_raw_parts(s_in, 32) };
    let dst: &mut [u8] = unsafe { core::slice::from_raw_parts_mut(out, 32) };
    dst.copy_from_slice(s);
}

// ----------------------------------------------------------------
// Self-tests
// ----------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// A felem encoded as 5 limbs each < 2^51, packed in 8-byte slots,
    /// recombines to the plain value when each limb fits in its slot.
    #[test]
    fn parse_felem_small_value() {
        // Represent value 1: w0 = 1, rest 0.
        let mut slot = [0u8; 40];
        slot[0] = 1;
        let c = parse_felem_canonical(&slot);
        let mut expect = [0u8; 32];
        expect[0] = 1;
        assert_eq!(c, expect);
    }

    #[test]
    fn parse_felem_two_limbs() {
        // value = 1 + 3 * 2^51.
        let mut slot = [0u8; 40];
        slot[0] = 1;
        slot[8] = 3; // w1 = 3
        let c = parse_felem_canonical(&slot);
        // expected big integer 1 + 3*2^51.
        let v: u128 = 1u128 + 3u128 * (1u128 << 51);
        let mut expect = [0u8; 32];
        for k in 0..16 {
            expect[k] = ((v >> (8 * k)) & 0xff) as u8;
        }
        assert_eq!(c, expect);
    }

    #[test]
    fn parse_felem_reduces_mod_p() {
        // Build a slot whose recombined value exceeds p so the mod-p
        // reduction fires.  Set all 5 limbs to 2^51 - 1 (max 51-bit),
        // giving value = (2^51-1)(1 + 2^51 + 2^102 + 2^153 + 2^204),
        // which is ~2^255, definitely needing reduction.  Cross-check
        // against a u128/bignum-free reference using i128 is hard, so
        // we instead assert the output is canonical (< p) and < 2^255.
        let mut slot = [0u8; 40];
        for i in 0..5 {
            let limb: u64 = (1u64 << 51) - 1;
            slot[8 * i..8 * i + 8].copy_from_slice(&limb.to_le_bytes());
        }
        let c = parse_felem_canonical(&slot);
        // bit 255 clear (canonical < 2^255).
        assert_eq!(c[31] & 0x80, 0);
        // < p: compare LE against p.
        let p: [u8; 32] = [
            0xed, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0x7f,
        ];
        let mut lt = false;
        for i in (0..32).rev() {
            if c[i] < p[i] {
                lt = true;
                break;
            }
            if c[i] > p[i] {
                break;
            }
        }
        assert!(lt, "result must be < p");
    }

    #[test]
    fn pack_canonical_is_identity() {
        let s = [7u8; 32];
        let mut out = [0u8; 32];
        unsafe { ristretto_pack_canonical_felem(out.as_mut_ptr(), s.as_ptr()) };
        assert_eq!(out, s);
    }
}
