//! Leaf FFI implementations for the extracted Ristretto255
//! decode/encode (B.5b path b — hand-written constant setters +
//! pack_xyzt5).
//!
//! Companion to [`leaves.rs`](../ed25519_rustcmd/leaves.rs) of the
//! Ed25519 path.  Most field-arithmetic leaves (`fe25519_mul`,
//! `fe25519_add`, `fe25519_sub`, `fe25519_sq`) are SHARED with the
//! Ed25519 leaves module — no need to redeclare here.
//!
//! What this module adds, per the sub-blocker analysis in
//! `AUCurves/.../Ristretto_RustCmd.v` §"PROGRESS (2026-05-23)":
//!
//! - **Constant setters** (sub-blocker #2 fix (b)):
//!     - `fe25519_const_one(out: *mut u8)` — writes the 32-byte LE
//!       encoding of `1`.
//!     - `fe25519_const_two(out: *mut u8)` — writes the 32-byte LE
//!       encoding of `2`.
//!     - `fe25519_const_d(out: *mut u8)` — writes the 32-byte LE
//!       encoding of Curve25519's `d = -121665/121666 mod p`.
//!
//! - **5-felem packer** (sub-blocker #3 fix, matches
//!   `End2End/Ed25519/XyztAddVerified.v:pack_xyzt5`):
//!     - `pack_xyzt5(out: *mut u8, x, y, z, ta, tb: *const u8)` —
//!       writes 5 × 40 bytes (each felem padded with 8 zero bytes)
//!       into the 200-byte output slot.
//!
//! All five are leaf primitives consumed by the extracted
//! `decode.rs` / `encode.rs`.  Each has a matching
//! `strong_callee_post` entry in
//! `src/Bedrock/End2End/Ristretto/RistrettoBridges.v` (the verified
//! spec).
//!
//! These primitives are TRIVIAL (no field arithmetic, no
//! side-channel concerns) — they're just byte-array I/O.  The
//! verification chain is:
//!   AST [REdCall "fe25519_const_one" dst []]
//!     → strong_callee_post_fe25519_const_one (Coq spec)
//!     → fe25519_const_one (this file, hand-written, trivially
//!                          matches the spec by construction)

#![allow(dead_code, unused_variables)]

// ----------------------------------------------------------------
// Constant setters
// ----------------------------------------------------------------

/// 32-byte LE encoding of `1` in F_{2^255-19}.
const FE25519_ONE_LE: [u8; 32] = {
    let mut bs = [0u8; 32];
    bs[0] = 1;
    bs
};

/// 32-byte LE encoding of `2` in F_{2^255-19}.
const FE25519_TWO_LE: [u8; 32] = {
    let mut bs = [0u8; 32];
    bs[0] = 2;
    bs
};

/// 32-byte LE encoding of Curve25519's `d = -121665/121666 mod p`.
///
/// Hex (big-endian): `52036cee2b6ffe738cc740797779e89800700a4d4141d8ab75eb4dca135978a3`.
/// LE bytes (low-to-high): `a3 78 59 13 ca 4d eb 75 ab d8 41 41 4d 0a 70 00 98 e8 79 77 79 40 c7 8c 73 fe 6f 2b ee 6c 03 52`.
///
/// Source: RFC 8032 §5.1 (Ed25519 curve parameters) — d is the same
/// constant used by Ed25519's twisted-Edwards form.  Cross-checked
/// with `Curve25519.E.d = F.div (F.opp (F.of_Z _ 121665)) (F.of_Z _ 121666)`
/// in `fiat-crypto/src/Spec/Curve25519.v` via `vm_compute`.
const FE25519_D_LE: [u8; 32] = [
    0xa3, 0x78, 0x59, 0x13, 0xca, 0x4d, 0xeb, 0x75,
    0xab, 0xd8, 0x41, 0x41, 0x4d, 0x0a, 0x70, 0x00,
    0x98, 0xe8, 0x79, 0x77, 0x79, 0x40, 0xc7, 0x8c,
    0x73, 0xfe, 0x6f, 0x2b, 0xee, 0x6c, 0x03, 0x52,
];

/// Write the 32-byte LE encoding of `1` to `out[0..32]`.
///
/// # Safety
/// `out` must point to at least 32 writable bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fe25519_const_one(out: *mut u8) {
    let dst: &mut [u8] = unsafe { core::slice::from_raw_parts_mut(out, 32) };
    dst.copy_from_slice(&FE25519_ONE_LE);
}

/// Write the 32-byte LE encoding of `2` to `out[0..32]`.
///
/// # Safety
/// `out` must point to at least 32 writable bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fe25519_const_two(out: *mut u8) {
    let dst: &mut [u8] = unsafe { core::slice::from_raw_parts_mut(out, 32) };
    dst.copy_from_slice(&FE25519_TWO_LE);
}

/// Write the 32-byte LE encoding of Curve25519's `d` constant to
/// `out[0..32]`.
///
/// # Safety
/// `out` must point to at least 32 writable bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fe25519_const_d(out: *mut u8) {
    let dst: &mut [u8] = unsafe { core::slice::from_raw_parts_mut(out, 32) };
    dst.copy_from_slice(&FE25519_D_LE);
}

// ----------------------------------------------------------------
// pack_xyzt5: 5-felem packer
// ----------------------------------------------------------------

/// Write the concatenation of 5 felems (32 bytes each, LE) as a
/// 200-byte buffer, padding each to 40 bytes with 8 trailing zero
/// bytes.  Matches `XyztAddVerified.pack_xyzt5` exactly:
///
/// ```text
/// out[0..40]    := x  ‖ [0u8; 8]
/// out[40..80]   := y  ‖ [0u8; 8]
/// out[80..120]  := z  ‖ [0u8; 8]
/// out[120..160] := ta ‖ [0u8; 8]
/// out[160..200] := tb ‖ [0u8; 8]
/// ```
///
/// # Safety
/// All input pointers must point to 32 readable bytes.  `out` must
/// point to 200 writable bytes.  Aliasing between any input and `out`
/// is undefined behaviour.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn pack_xyzt5(
    out: *mut u8,
    x: *const u8,
    y: *const u8,
    z: *const u8,
    ta: *const u8,
    tb: *const u8,
) {
    let dst: &mut [u8] = unsafe { core::slice::from_raw_parts_mut(out, 200) };
    let src_x: &[u8] = unsafe { core::slice::from_raw_parts(x, 32) };
    let src_y: &[u8] = unsafe { core::slice::from_raw_parts(y, 32) };
    let src_z: &[u8] = unsafe { core::slice::from_raw_parts(z, 32) };
    let src_ta: &[u8] = unsafe { core::slice::from_raw_parts(ta, 32) };
    let src_tb: &[u8] = unsafe { core::slice::from_raw_parts(tb, 32) };
    // Zero the whole buffer first so the high-8 of each 40-byte slot
    // is guaranteed zero.
    for byte in dst.iter_mut() {
        *byte = 0;
    }
    dst[0..32].copy_from_slice(src_x);
    dst[40..72].copy_from_slice(src_y);
    dst[80..112].copy_from_slice(src_z);
    dst[120..152].copy_from_slice(src_ta);
    dst[160..192].copy_from_slice(src_tb);
}

// ----------------------------------------------------------------
// Self-tests
// ----------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn const_one_is_le_one() {
        let mut out = [0u8; 32];
        unsafe { fe25519_const_one(out.as_mut_ptr()); }
        assert_eq!(out[0], 1);
        assert!(out[1..].iter().all(|&b| b == 0));
    }

    #[test]
    fn const_two_is_le_two() {
        let mut out = [0u8; 32];
        unsafe { fe25519_const_two(out.as_mut_ptr()); }
        assert_eq!(out[0], 2);
        assert!(out[1..].iter().all(|&b| b == 0));
    }

    #[test]
    fn const_d_matches_rfc8032() {
        let mut out = [0u8; 32];
        unsafe { fe25519_const_d(out.as_mut_ptr()); }
        // First byte and last byte spot-check.
        assert_eq!(out[0], 0xa3);
        assert_eq!(out[31], 0x52);
        // Full match against the static constant.
        assert_eq!(out, FE25519_D_LE);
    }

    #[test]
    fn pack_xyzt5_lays_out_with_padding() {
        let x = [0x11u8; 32];
        let y = [0x22u8; 32];
        let z = [0x33u8; 32];
        let ta = [0x44u8; 32];
        let tb = [0x55u8; 32];
        let mut out = [0xFFu8; 200];
        unsafe {
            pack_xyzt5(
                out.as_mut_ptr(),
                x.as_ptr(), y.as_ptr(), z.as_ptr(),
                ta.as_ptr(), tb.as_ptr(),
            );
        }
        // Each 40-byte slot: first 32 bytes are the felem, last 8 are zero.
        for i in 0..32 { assert_eq!(out[i], 0x11); }
        for i in 32..40 { assert_eq!(out[i], 0); }
        for i in 40..72 { assert_eq!(out[i], 0x22); }
        for i in 72..80 { assert_eq!(out[i], 0); }
        for i in 80..112 { assert_eq!(out[i], 0x33); }
        for i in 112..120 { assert_eq!(out[i], 0); }
        for i in 120..152 { assert_eq!(out[i], 0x44); }
        for i in 152..160 { assert_eq!(out[i], 0); }
        for i in 160..192 { assert_eq!(out[i], 0x55); }
        for i in 192..200 { assert_eq!(out[i], 0); }
    }
}
