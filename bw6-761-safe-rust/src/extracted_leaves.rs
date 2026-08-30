//! Raw-pointer leaf shims for the Rocq-emitted G1 bodies.
//!
//! The emitted body (`src/Bedrock/Curve/CurveDoubleA0RustCmd.v`,
//! printed via `RustCmdToRust.rs_body_extract`) calls field leaves as
//! `unsafe { bw6_761_fp_mul(dest.as_mut_ptr(), a.as_ptr(), b.as_ptr()) }`
//! over `[u8; 96]` buffers holding the 12 little-endian u64 Montgomery
//! limbs.  These shims adapt that byte-buffer ABI to the crate's own
//! verified leaves.  Little-endian host assumed (as for the rest of
//! the workspace).
//!
//! The leaves called here are `tower::bw6_761_{mul,add,sub}`, i.e. the
//! SAME `_bw6_761_*` extern symbols that `group::g1_proj_double` and
//! `group::g1_proj_add` go through, so a benchmark of the emitted body
//! against the hand-written one differs only in the point-level code.
//!
//! Shim-name convention follows `p256-safe-rust/src/extracted_leaves.rs`.

use crate::tower::{bw6_761_add, bw6_761_mul, bw6_761_sub, Fp};

pub const FBYTES: usize = 96;
pub const LIMBS: usize = 12;

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
/// `out` must point to 96 writable bytes; `a`, `b` to 96 readable bytes.
#[inline]
pub unsafe fn bw6_761_fp_mul(out: *mut u8, a: *const u8, b: *const u8) {
    let (a, b) = (load_fp(a), load_fp(b));
    let mut o = Fp([0u64; LIMBS]);
    bw6_761_mul(&mut o, &a, &b);
    store_fp(out, &o);
}

/// # Safety
/// `out` must point to 96 writable bytes; `a`, `b` to 96 readable bytes.
#[inline]
pub unsafe fn bw6_761_fp_add(out: *mut u8, a: *const u8, b: *const u8) {
    let (a, b) = (load_fp(a), load_fp(b));
    let mut o = Fp([0u64; LIMBS]);
    bw6_761_add(&mut o, &a, &b);
    store_fp(out, &o);
}

/// # Safety
/// `out` must point to 96 writable bytes; `a`, `b` to 96 readable bytes.
#[inline]
pub unsafe fn bw6_761_fp_sub(out: *mut u8, a: *const u8, b: *const u8) {
    let (a, b) = (load_fp(a), load_fp(b));
    let mut o = Fp([0u64; LIMBS]);
    bw6_761_sub(&mut o, &a, &b);
    store_fp(out, &o);
}
