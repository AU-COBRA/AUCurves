//! Raw-pointer leaf shims for the extracted G1 addition.
//!
//! The Rocq-emitted body (`src/Bedrock/Curve/NistG1AddRustCmd.v`,
//! printed via `RustCmdToRust.rs_body_extract`) calls field leaves as
//! `unsafe { p521_fp_mul(dest.as_mut_ptr(), a.as_ptr(), b.as_ptr()) }`
//! over `[u8; 66]` buffers holding CANONICAL little-endian field
//! bytes (P-521 has no Montgomery form; the Solinas tight/loose limb
//! representation stays inside these shims).  Every shim goes
//! bytes → tight limbs → op (+carry) → canonical bytes, so buffer
//! contents are always canonical between calls.

use crate::{fp_add, fp_carry, fp_carry_mul, fp_from_bytes, fp_relax, fp_sub, fp_to_bytes, FpL, FpT};

#[inline]
unsafe fn load_fp(p: *const u8) -> FpT {
    let mut bs = [0u8; 66];
    core::ptr::copy_nonoverlapping(p, bs.as_mut_ptr(), 66);
    let mut t = FpT([0u64; 9]);
    fp_from_bytes(&mut t, &bs);
    t
}

#[inline]
unsafe fn store_fp(p: *mut u8, v: &FpT) {
    let mut bs = [0u8; 66];
    fp_to_bytes(&mut bs, v);
    core::ptr::copy_nonoverlapping(bs.as_ptr(), p, 66);
}

/// # Safety
/// `out` must point to 66 writable bytes; `a`, `b` to 66 readable bytes.
pub unsafe fn p521_fp_mul(out: *mut u8, a: *const u8, b: *const u8) {
    let (a, b) = (load_fp(a), load_fp(b));
    let mut al = FpL([0u64; 9]);
    let mut bl = FpL([0u64; 9]);
    fp_relax(&mut al, &a);
    fp_relax(&mut bl, &b);
    let mut o = FpT([0u64; 9]);
    fp_carry_mul(&mut o, &al, &bl);
    store_fp(out, &o);
}

/// # Safety
/// `out` must point to 66 writable bytes; `a`, `b` to 66 readable bytes.
pub unsafe fn p521_fp_add(out: *mut u8, a: *const u8, b: *const u8) {
    let (a, b) = (load_fp(a), load_fp(b));
    let mut l = FpL([0u64; 9]);
    fp_add(&mut l, &a, &b);
    let mut o = FpT([0u64; 9]);
    fp_carry(&mut o, &l);
    store_fp(out, &o);
}

/// # Safety
/// `out` must point to 66 writable bytes; `a`, `b` to 66 readable bytes.
pub unsafe fn p521_fp_sub(out: *mut u8, a: *const u8, b: *const u8) {
    let (a, b) = (load_fp(a), load_fp(b));
    let mut l = FpL([0u64; 9]);
    fp_sub(&mut l, &a, &b);
    let mut o = FpT([0u64; 9]);
    fp_carry(&mut o, &l);
    store_fp(out, &o);
}
