//! Limb-typed `fe25519_*` shim — prototype of the TFp25519_64 plumbing
//! (see `docs/perf-gap-analysis.md` + `docs/tfp25519-plumbing-plan.md`).
//!
//! ## Why a parallel shim
//!
//! The byte-canonical shim in `fe25519_portable.rs` pays ~30 ns per
//! field op converting between the 40-byte canonical encoding and
//! fiat's 5×u64 51-bit limb representation.  Measured at the
//! `fe25519_micro` microbench: 12.2 ns bare `carry_mul` vs 42.1 ns
//! through the byte shim (3.5× slowdown).
//!
//! When the verified rust_cmd_ed AST is refactored to use `TFp25519`
//! typed slots (5×u64 limbs) instead of `TBytes 40` byte slots, the
//! field-op leaves will receive `*const u64` / `*mut u64` pointers
//! directly to limb arrays.  At that point the conversion can be
//! omitted entirely — that's what this shim demonstrates.
//!
//! ## Representation
//!
//! Each slot stores a fiat **tight** field element: 5 × u64 limbs,
//! each ≤ 2^51 + ε.  No byte-canonical reduction between ops.
//!
//! Verbatim slot layout: `[u64; 5]` little-endian, no padding.

#![cfg(feature = "tfp25519_limbs")]
#![allow(non_snake_case)]

use fiat_crypto::curve25519_64::{
    fiat_25519_add, fiat_25519_carry, fiat_25519_carry_mul, fiat_25519_carry_square,
    fiat_25519_loose_field_element, fiat_25519_relax, fiat_25519_sub,
    fiat_25519_tight_field_element,
};

// 2d_25519 in radix-2^51 limbs (same as fe25519_portable.rs).
const TWO_D_LIMBS: [u64; 5] = [
    1859910466990425u64,
    932731440258426u64,
    1072319116312658u64,
    1815898335770999u64,
    633789495995903u64,
];

#[inline(always)]
unsafe fn read_tight_limbs(p: *const u64) -> fiat_25519_tight_field_element {
    let a = unsafe { *(p as *const [u64; 5]) };
    fiat_25519_tight_field_element(a)
}

#[inline(always)]
unsafe fn write_tight_limbs(p: *mut u64, fe: &fiat_25519_tight_field_element) {
    let dst = unsafe { &mut *(p as *mut [u64; 5]) };
    *dst = fe.0;
}

#[inline(always)]
fn relax(fe: &fiat_25519_tight_field_element) -> fiat_25519_loose_field_element {
    let mut out = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_relax(&mut out, fe);
    out
}

// ---------------------------------------------------------------------------
// Primitive field ops — limb-typed FFI surface.

/// out := a + b   (mod p), stored tight.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fe25519_add(out: *mut u64, a: *const u64, b: *const u64) {
    let at = unsafe { read_tight_limbs(a) };
    let bt = unsafe { read_tight_limbs(b) };
    let mut sum = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_add(&mut sum, &at, &bt);
    let mut r = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry(&mut r, &sum);
    unsafe { write_tight_limbs(out, &r) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn fe25519_sub(out: *mut u64, a: *const u64, b: *const u64) {
    let at = unsafe { read_tight_limbs(a) };
    let bt = unsafe { read_tight_limbs(b) };
    let mut diff = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_sub(&mut diff, &at, &bt);
    let mut r = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry(&mut r, &diff);
    unsafe { write_tight_limbs(out, &r) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn fe25519_mul(out: *mut u64, a: *const u64, b: *const u64) {
    let at = unsafe { read_tight_limbs(a) };
    let bt = unsafe { read_tight_limbs(b) };
    let al = relax(&at);
    let bl = relax(&bt);
    let mut r = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry_mul(&mut r, &al, &bl);
    unsafe { write_tight_limbs(out, &r) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn fe25519_sqr(out: *mut u64, a: *const u64) {
    let at = unsafe { read_tight_limbs(a) };
    let al = relax(&at);
    let mut r = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry_square(&mut r, &al);
    unsafe { write_tight_limbs(out, &r) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn fe25519_mul_2(out: *mut u64, a: *const u64) {
    let at = unsafe { read_tight_limbs(a) };
    let mut sum = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_add(&mut sum, &at, &at);
    let mut r = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry(&mut r, &sum);
    unsafe { write_tight_limbs(out, &r) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn fe25519_mul_d2(out: *mut u64, a: *const u64) {
    let at = unsafe { read_tight_limbs(a) };
    let al = relax(&at);
    let two_d_tight = fiat_25519_tight_field_element(TWO_D_LIMBS);
    let two_d_loose = relax(&two_d_tight);
    let mut r = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry_mul(&mut r, &al, &two_d_loose);
    unsafe { write_tight_limbs(out, &r) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn fe25519_sqr_scale2(out: *mut u64, a: *const u64) {
    let at = unsafe { read_tight_limbs(a) };
    let al = relax(&at);
    let mut sq = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry_square(&mut sq, &al);
    let mut twice = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_add(&mut twice, &sq, &sq);
    let mut r = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry(&mut r, &twice);
    unsafe { write_tight_limbs(out, &r) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn fe25519_sqr_sub2(
    out: *mut u64, a: *const u64, b: *const u64, c: *const u64,
) {
    let at = unsafe { read_tight_limbs(a) };
    let al = relax(&at);
    let mut sq = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry_square(&mut sq, &al);

    let bt = unsafe { read_tight_limbs(b) };
    let mut diff1_loose = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_sub(&mut diff1_loose, &sq, &bt);
    let mut diff1 = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry(&mut diff1, &diff1_loose);

    let ct = unsafe { read_tight_limbs(c) };
    let mut diff2_loose = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_sub(&mut diff2_loose, &diff1, &ct);
    let mut r = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry(&mut r, &diff2_loose);
    unsafe { write_tight_limbs(out, &r) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn fe25519_neg_add(out: *mut u64, a: *const u64, b: *const u64) {
    let at = unsafe { read_tight_limbs(a) };
    let bt = unsafe { read_tight_limbs(b) };
    let mut sum_loose = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_add(&mut sum_loose, &at, &bt);
    let mut sum = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry(&mut sum, &sum_loose);

    let zero = fiat_25519_tight_field_element([0; 5]);
    let mut neg_loose = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_sub(&mut neg_loose, &zero, &sum);
    let mut r = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry(&mut r, &neg_loose);
    unsafe { write_tight_limbs(out, &r) };
}
