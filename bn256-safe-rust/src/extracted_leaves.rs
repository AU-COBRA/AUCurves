//! Raw-pointer leaf shims for the Rocq-emitted G1 bodies.
//!
//! The emitted body (`src/Bedrock/Curve/CurveDoubleA0RustCmd.v`,
//! printed via `RustCmdToRust.rs_body_extract`) calls field leaves as
//! `unsafe { bn256_fp_mul(dest.as_mut_ptr(), a.as_ptr(), b.as_ptr()) }`
//! over `[u8; 32]` buffers holding the 4 little-endian u64 Montgomery
//! limbs.  These shims adapt that byte-buffer ABI to the crate's own
//! leaves `tower::bn256_{mul,add,sub}`, i.e. to the same `_bn256_*`
//! extern symbols the rest of the crate goes through.  Little-endian
//! host assumed (as for the rest of the workspace).
//!
//! Shim-name convention follows `p256-safe-rust/src/extracted_leaves.rs`.
//! Curve: BN256.

use crate::tower::{bn256_add, bn256_mul, bn256_sub, Fp};

pub const FBYTES: usize = 32;
pub const LIMBS: usize = 4;

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
/// `out` must point to 32 writable bytes; `a`, `b` to 32 readable bytes.
#[inline]
pub unsafe fn bn256_fp_mul(out: *mut u8, a: *const u8, b: *const u8) {
    let (a, b) = (load_fp(a), load_fp(b));
    let mut o = Fp([0u64; LIMBS]);
    bn256_mul(&mut o, &a, &b);
    store_fp(out, &o);
}

/// # Safety
/// `out` must point to 32 writable bytes; `a`, `b` to 32 readable bytes.
#[inline]
pub unsafe fn bn256_fp_add(out: *mut u8, a: *const u8, b: *const u8) {
    let (a, b) = (load_fp(a), load_fp(b));
    let mut o = Fp([0u64; LIMBS]);
    bn256_add(&mut o, &a, &b);
    store_fp(out, &o);
}

/// # Safety
/// `out` must point to 32 writable bytes; `a`, `b` to 32 readable bytes.
#[inline]
pub unsafe fn bn256_fp_sub(out: *mut u8, a: *const u8, b: *const u8) {
    let (a, b) = (load_fp(a), load_fp(b));
    let mut o = Fp([0u64; LIMBS]);
    bn256_sub(&mut o, &a, &b);
    store_fp(out, &o);
}
