//! Raw-pointer leaf shims for the Rocq-emitted G1 bodies.
//!
//! The emitted body (`src/Bedrock/Curve/CurveDoubleA0RustCmd.v`,
//! printed via `RustCmdToRust.rs_body_extract`) calls field leaves as
//! `unsafe { bls12_fp_mul(dest.as_mut_ptr(), a.as_ptr(), b.as_ptr()) }`
//! over `[u8; 48]` buffers holding the 6 little-endian u64 Montgomery
//! limbs.  These shims adapt that byte-buffer ABI to the crate's own
//! leaves `tower::bls12_{mul,add,sub}`, i.e. to the same `_bls12_*`
//! extern symbols the rest of the crate goes through.  Little-endian
//! host assumed (as for the rest of the workspace).
//!
//! Shim-name convention follows `p256-safe-rust/src/extracted_leaves.rs`.
//! Curve: BLS12-381.

use crate::tower::{bls12_add, bls12_mul, bls12_sub, Fp};

pub const FBYTES: usize = 48;
pub const LIMBS: usize = 6;

#[inline]
unsafe fn load_fp(p: *const u8) -> Fp {
    let mut limbs = [0u64; LIMBS];
    core::ptr::copy_nonoverlapping(p, limbs.as_mut_ptr() as *mut u8, FBYTES);
    Fp(limbs)
}

#[inline]
unsafe fn store_fp(p: *mut u8, v: &Fp) {
    core::ptr::copy_nonoverlapping(v.0.as_ptr() as *const u8, p, FBYTES);
}

/// # Safety
/// `out` must point to 48 writable bytes; `a`, `b` to 48 readable bytes.
#[inline]
pub unsafe fn bls12_fp_mul(out: *mut u8, a: *const u8, b: *const u8) {
    let (a, b) = (load_fp(a), load_fp(b));
    let mut o = Fp([0u64; LIMBS]);
    bls12_mul(&mut o, &a, &b);
    store_fp(out, &o);
}

/// # Safety
/// `out` must point to 48 writable bytes; `a`, `b` to 48 readable bytes.
#[inline]
pub unsafe fn bls12_fp_add(out: *mut u8, a: *const u8, b: *const u8) {
    let (a, b) = (load_fp(a), load_fp(b));
    let mut o = Fp([0u64; LIMBS]);
    bls12_add(&mut o, &a, &b);
    store_fp(out, &o);
}

/// # Safety
/// `out` must point to 48 writable bytes; `a`, `b` to 48 readable bytes.
#[inline]
pub unsafe fn bls12_fp_sub(out: *mut u8, a: *const u8, b: *const u8) {
    let (a, b) = (load_fp(a), load_fp(b));
    let mut o = Fp([0u64; LIMBS]);
    bls12_sub(&mut o, &a, &b);
    store_fp(out, &o);
}
