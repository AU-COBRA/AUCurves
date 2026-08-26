//! Raw-pointer leaf shims for the extracted G1 addition.
//!
//! The Rocq-emitted body (`src/Bedrock/Curve/NistG1AddRustCmd.v`,
//! printed via `RustCmdToRust.rs_body_extract`) calls field leaves as
//! `unsafe { p384_fp_mul(dest.as_mut_ptr(), a.as_ptr(), b.as_ptr()) }`
//! over `[u8; 48]` buffers holding the 6 little-endian u64 Montgomery
//! limbs.  These shims adapt that byte-buffer ABI to the verified
//! fiat-rust field functions.  Little-endian host assumed.

use crate::{fp_add, fp_mul, fp_sub, Fp};

#[inline]
unsafe fn load_fp(p: *const u8) -> Fp {
    let mut limbs = [0u64; 6];
    core::ptr::copy_nonoverlapping(p, limbs.as_mut_ptr() as *mut u8, 48);
    Fp(limbs)
}

#[inline]
unsafe fn store_fp(p: *mut u8, v: &Fp) {
    core::ptr::copy_nonoverlapping(v.0.as_ptr() as *const u8, p, 48);
}

/// # Safety
/// `out` must point to 48 writable bytes; `a`, `b` to 48 readable bytes.
pub unsafe fn p384_fp_mul(out: *mut u8, a: *const u8, b: *const u8) {
    let (a, b) = (load_fp(a), load_fp(b));
    let mut o = Fp([0u64; 6]);
    fp_mul(&mut o, &a, &b);
    store_fp(out, &o);
}

/// # Safety
/// `out` must point to 48 writable bytes; `a`, `b` to 48 readable bytes.
pub unsafe fn p384_fp_add(out: *mut u8, a: *const u8, b: *const u8) {
    let (a, b) = (load_fp(a), load_fp(b));
    let mut o = Fp([0u64; 6]);
    fp_add(&mut o, &a, &b);
    store_fp(out, &o);
}

/// # Safety
/// `out` must point to 48 writable bytes; `a`, `b` to 48 readable bytes.
pub unsafe fn p384_fp_sub(out: *mut u8, a: *const u8, b: *const u8) {
    let (a, b) = (load_fp(a), load_fp(b));
    let mut o = Fp([0u64; 6]);
    fp_sub(&mut o, &a, &b);
    store_fp(out, &o);
}
