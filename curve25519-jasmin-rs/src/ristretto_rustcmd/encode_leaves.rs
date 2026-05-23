//! Encode-specific leaf FFI implementations for the extracted
//! Ristretto255 encoder (`encode.rs`).
//!
//! Companion to `leaves.rs` (decode path).  The field-arithmetic
//! leaves (`fe25519_mul`, `fe25519_add`, `fe25519_sub`, `fe25519_sq`),
//! the modular inverse (`fe25519_inv`), and `ristretto_sqrt_ratio_m1`
//! are SHARED with the decode path (defined in `leaves.rs`) — here we
//! provide the two encode-only leaves.  Felems are 40-byte (the
//! fe25519 byte-ABI convention: 32 value bytes + 8 zero pad).
//!
//! - `unpack_xyzt5` — inverse of the DECODER's `pack_xyzt5`, which
//!   writes `le_split 40` (plain little-endian) of each field element.
//!   Each 40-byte slot already IS the canonical plain-LE felem that the
//!   fe25519 byte-ABI expects, so `unpack_xyzt5` just splits the
//!   200-byte input into five 40-byte felems and copies them out.
//!
//!   This is plain-LE, NOT the radix-2^51 `parse_felem` of the Gallina
//!   `parse_xyzt5` (`XyztAddVerified.v`).  The decoder's `pack_xyzt5`
//!   is plain-LE and is the validated (dalek-equivalent) format, so the
//!   encoder must read plain-LE to round-trip.  The Gallina-level
//!   `parse_xyzt5`/`pack_xyzt5` inverse is *admitted*
//!   (`Ristretto255_Canonicality.ristretto_decode_encode_roundtrip`);
//!   the radix-2^51-vs-plain-LE discrepancy is why.  The encoder Gallina
//!   spec should be reconciled to plain-LE when the encoder is
//!   verified-extracted; until then this Rust leaf matches the
//!   decoder's format (KAT-validated against dalek).
//!
//! - `ristretto_pack_canonical_felem` — 32-byte LE encoding of the
//!   canonical (reduced, < p) field element `s` held in a 40-byte
//!   felem slot: copies the low 32 bytes.
//!
//! Trust class: pure data-movement.  Replace with verified extraction
//! when the encoder is decomposed.

#![allow(dead_code, unused_variables)]

/// `unpack_xyzt5`: inverse of `pack_xyzt5`.  Splits the 200-byte
/// `xyzt_in` into five 40-byte plain-LE felem slots and copies each to
/// `out_x`, `out_y`, `out_z`, `out_ta`, `out_tb` (40 bytes each).
///
/// # Safety
/// `xyzt_in` must point to 200 readable bytes; each output pointer must
/// point to 40 writable bytes.  No aliasing between inputs and outputs.
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
        let dst: &mut [u8] = unsafe { core::slice::from_raw_parts_mut(op, 40) };
        dst.copy_from_slice(&xyzt[40 * i..40 * i + 40]);
    }
}

/// `ristretto_pack_canonical_felem`: 32-byte LE encoding of the
/// canonical field element `s` (held in a 40-byte felem slot).  Copies
/// the low 32 bytes (the value; high 8 are zero pad).
///
/// # Safety
/// `s_in` must point to 40 readable bytes; `out` to 32 writable bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ristretto_pack_canonical_felem(out: *mut u8, s_in: *const u8) {
    let s: &[u8] = unsafe { core::slice::from_raw_parts(s_in, 40) };
    let dst: &mut [u8] = unsafe { core::slice::from_raw_parts_mut(out, 32) };
    dst.copy_from_slice(&s[0..32]);
}

// ----------------------------------------------------------------
// Self-tests
// ----------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unpack_splits_five_40byte_slots() {
        let mut xyzt = [0u8; 200];
        for i in 0..5 {
            for j in 0..40 {
                xyzt[40 * i + j] = (10 * (i as u8 + 1)) + (j as u8 & 0x0f);
            }
        }
        let (mut x, mut y, mut z, mut ta, mut tb) =
            ([0u8; 40], [0u8; 40], [0u8; 40], [0u8; 40], [0u8; 40]);
        unsafe {
            unpack_xyzt5(
                x.as_mut_ptr(), y.as_mut_ptr(), z.as_mut_ptr(),
                ta.as_mut_ptr(), tb.as_mut_ptr(), xyzt.as_ptr(),
            );
        }
        assert_eq!(&x, &xyzt[0..40]);
        assert_eq!(&y, &xyzt[40..80]);
        assert_eq!(&z, &xyzt[80..120]);
        assert_eq!(&ta, &xyzt[120..160]);
        assert_eq!(&tb, &xyzt[160..200]);
    }

    #[test]
    fn pack_canonical_copies_low_32() {
        let mut s = [0u8; 40];
        for j in 0..40 { s[j] = j as u8; }
        let mut out = [0u8; 32];
        unsafe { ristretto_pack_canonical_felem(out.as_mut_ptr(), s.as_ptr()) };
        assert_eq!(&out[..], &s[0..32]);
    }
}
