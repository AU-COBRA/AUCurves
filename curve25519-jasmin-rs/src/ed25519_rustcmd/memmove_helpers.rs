//! Slice-based implementations of the `memmove_*` helpers that
//! `rust_cmd_ed`'s emitter references.  Each one corresponds to a
//! single fixed-offset region copy in the Ed25519 sign / verify
//! source AST (see `Sign_Verify_RustCmd.v`).
//!
//! Defined as `extern "C"` so the linker resolves the same symbol
//! that the auto-generated `sign.rs` / `verify.rs` modules import.
//! Bodies are pure safe-Rust slice copies once a `&[u8]` /
//! `&mut [u8]` view is reconstructed; the only `unsafe` is the
//! pointer-to-slice reconstruction at the FFI boundary.
//!
//! **FFI centralization (status doc §6.3, Phase B) — EXEMPT.**  Each
//! `pub unsafe extern "C" fn memmove_*` *is* an FFI symbol surface
//! (called from the auto-generated `sign.rs` / `verify.rs`); the
//! `unsafe { slice::from_raw_parts(_mut) }` blocks inside cannot
//! move into `ffi_safe.rs` without also rewriting the IR emitter to
//! call safe wrappers directly.  These blocks will collapse when
//! the emitter targets `ffi_safe::*`.

#![cfg(feature = "ed25519_rustcmd")]

use core::slice;

// ---------- sign ----------

/// `a := h_full[0..32]`
#[unsafe(no_mangle)]
pub unsafe extern "C" fn memmove_a_from_h(out: *mut u8, h: *const u8) {
    let dst = unsafe { slice::from_raw_parts_mut(out, 32) };
    let src = unsafe { slice::from_raw_parts(h, 32) };
    dst.copy_from_slice(src);
}

/// `prefix := h_full[32..64]`
#[unsafe(no_mangle)]
pub unsafe extern "C" fn memmove_prefix_from_h(out: *mut u8, h: *const u8) {
    let dst = unsafe { slice::from_raw_parts_mut(out, 32) };
    let src = unsafe { slice::from_raw_parts(h, 64) };
    dst.copy_from_slice(&src[32..64]);
}

/// `nonce_buf[0..32] := prefix[..]`
#[unsafe(no_mangle)]
pub unsafe extern "C" fn memmove_nonce_prefix(buf: *mut u8, prefix: *const u8) {
    let dst = unsafe { slice::from_raw_parts_mut(buf, 4128) };
    let src = unsafe { slice::from_raw_parts(prefix, 32) };
    dst[0..32].copy_from_slice(src);
}

/// `nonce_buf[32..32+4096] := msg[..]`
#[unsafe(no_mangle)]
pub unsafe extern "C" fn memmove_nonce_msg(buf: *mut u8, msg: *const u8) {
    let dst = unsafe { slice::from_raw_parts_mut(buf, 4128) };
    let src = unsafe { slice::from_raw_parts(msg, 4096) };
    dst[32..32 + 4096].copy_from_slice(src);
}

/// `chal_buf[0..32] := R[..]`
#[unsafe(no_mangle)]
pub unsafe extern "C" fn memmove_chal_R(buf: *mut u8, r: *const u8) {
    let dst = unsafe { slice::from_raw_parts_mut(buf, 4160) };
    let src = unsafe { slice::from_raw_parts(r, 32) };
    dst[0..32].copy_from_slice(src);
}

/// `chal_buf[32..64] := A[..]`
#[unsafe(no_mangle)]
pub unsafe extern "C" fn memmove_chal_A(buf: *mut u8, a: *const u8) {
    let dst = unsafe { slice::from_raw_parts_mut(buf, 4160) };
    let src = unsafe { slice::from_raw_parts(a, 32) };
    dst[32..64].copy_from_slice(src);
}

/// `chal_buf[64..64+4096] := M[..]`
#[unsafe(no_mangle)]
pub unsafe extern "C" fn memmove_chal_M(buf: *mut u8, m: *const u8) {
    let dst = unsafe { slice::from_raw_parts_mut(buf, 4160) };
    let src = unsafe { slice::from_raw_parts(m, 4096) };
    dst[64..64 + 4096].copy_from_slice(src);
}

/// `sig_out[0..32] := R[..]`  (S-half is filled by [scalar_muladd] at
/// offset 32; per RFC 8032 §5.1.6, signature = R ‖ S).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn memmove_sig_R(sig: *mut u8, r: *const u8) {
    let dst = unsafe { slice::from_raw_parts_mut(sig, 64) };
    let src = unsafe { slice::from_raw_parts(r, 32) };
    dst[0..32].copy_from_slice(src);
}

// ---------- verify ----------

/// `R_bytes := sig_in[0..32]`
#[unsafe(no_mangle)]
pub unsafe extern "C" fn memmove_R_from_sig(out: *mut u8, sig: *const u8) {
    let dst = unsafe { slice::from_raw_parts_mut(out, 32) };
    let src = unsafe { slice::from_raw_parts(sig, 64) };
    dst.copy_from_slice(&src[0..32]);
}

/// `S_bytes := sig_in[32..64]`
#[unsafe(no_mangle)]
pub unsafe extern "C" fn memmove_S_from_sig(out: *mut u8, sig: *const u8) {
    let dst = unsafe { slice::from_raw_parts_mut(out, 32) };
    let src = unsafe { slice::from_raw_parts(sig, 64) };
    dst.copy_from_slice(&src[32..64]);
}
