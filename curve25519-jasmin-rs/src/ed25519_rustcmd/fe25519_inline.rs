//! Rust-level (non-extern-C) `#[inline(always)]` field-op shim over
//! `[u64; 5]` tight-limb slots.
//!
//! Sibling to `fe25519_limbs.rs`'s `extern "C"` exports, but designed
//! to be **inlined** by LLVM into a caller body so limbs stay in
//! registers across many ops.  The `fe25519_limbs.rs` exports cross a
//! static-lib boundary, forcing limbs to spill to memory between calls
//! — see `docs/perf-gap-analysis.md` for measurements.
//!
//! Used by `decomposed_bodies_limbs_inline.rs` to close the remaining
//! ~2× sign / ~4× verify gap to dalek-native.

#![cfg(feature = "tfp25519_inline_limbs")]
#![allow(non_snake_case)]

use fiat_crypto::curve25519_64::{
    fiat_25519_add, fiat_25519_carry, fiat_25519_carry_mul, fiat_25519_carry_square,
    fiat_25519_loose_field_element, fiat_25519_relax, fiat_25519_sub,
    fiat_25519_tight_field_element,
};

pub type Fe5 = [u64; 5];

// 2d_25519 in radix-2^51 limbs (same as fe25519_portable.rs).
const TWO_D_LIMBS: Fe5 = [
    1859910466990425u64,
    932731440258426u64,
    1072319116312658u64,
    1815898335770999u64,
    633789495995903u64,
];

#[inline(always)]
fn relax(fe: &fiat_25519_tight_field_element) -> fiat_25519_loose_field_element {
    let mut out = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_relax(&mut out, fe);
    out
}

#[inline(always)]
pub fn fe25519_add(out: &mut Fe5, a: &Fe5, b: &Fe5) {
    let at = fiat_25519_tight_field_element(*a);
    let bt = fiat_25519_tight_field_element(*b);
    let mut sum = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_add(&mut sum, &at, &bt);
    let mut r = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry(&mut r, &sum);
    *out = r.0;
}

#[inline(always)]
pub fn fe25519_sub(out: &mut Fe5, a: &Fe5, b: &Fe5) {
    let at = fiat_25519_tight_field_element(*a);
    let bt = fiat_25519_tight_field_element(*b);
    let mut diff = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_sub(&mut diff, &at, &bt);
    let mut r = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry(&mut r, &diff);
    *out = r.0;
}

#[inline(always)]
pub fn fe25519_mul(out: &mut Fe5, a: &Fe5, b: &Fe5) {
    let at = fiat_25519_tight_field_element(*a);
    let bt = fiat_25519_tight_field_element(*b);
    let al = relax(&at);
    let bl = relax(&bt);
    let mut r = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry_mul(&mut r, &al, &bl);
    *out = r.0;
}

#[inline(always)]
pub fn fe25519_sqr(out: &mut Fe5, a: &Fe5) {
    let at = fiat_25519_tight_field_element(*a);
    let al = relax(&at);
    let mut r = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry_square(&mut r, &al);
    *out = r.0;
}

#[inline(always)]
pub fn fe25519_mul_2(out: &mut Fe5, a: &Fe5) {
    let at = fiat_25519_tight_field_element(*a);
    let mut sum = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_add(&mut sum, &at, &at);
    let mut r = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry(&mut r, &sum);
    *out = r.0;
}

#[inline(always)]
pub fn fe25519_mul_d2(out: &mut Fe5, a: &Fe5) {
    let at = fiat_25519_tight_field_element(*a);
    let al = relax(&at);
    let two_d_tight = fiat_25519_tight_field_element(TWO_D_LIMBS);
    let two_d_loose = relax(&two_d_tight);
    let mut r = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry_mul(&mut r, &al, &two_d_loose);
    *out = r.0;
}

#[inline(always)]
pub fn fe25519_sqr_scale2(out: &mut Fe5, a: &Fe5) {
    let at = fiat_25519_tight_field_element(*a);
    let al = relax(&at);
    let mut sq = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry_square(&mut sq, &al);
    let mut twice = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_add(&mut twice, &sq, &sq);
    let mut r = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry(&mut r, &twice);
    *out = r.0;
}

#[inline(always)]
pub fn fe25519_sqr_sub2(out: &mut Fe5, a: &Fe5, b: &Fe5, c: &Fe5) {
    let at = fiat_25519_tight_field_element(*a);
    let al = relax(&at);
    let mut sq = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry_square(&mut sq, &al);

    let bt = fiat_25519_tight_field_element(*b);
    let mut diff1_loose = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_sub(&mut diff1_loose, &sq, &bt);
    let mut diff1 = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry(&mut diff1, &diff1_loose);

    let ct = fiat_25519_tight_field_element(*c);
    let mut diff2_loose = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_sub(&mut diff2_loose, &diff1, &ct);
    let mut r = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry(&mut r, &diff2_loose);
    *out = r.0;
}

#[inline(always)]
pub fn fe25519_neg_add(out: &mut Fe5, a: &Fe5, b: &Fe5) {
    let at = fiat_25519_tight_field_element(*a);
    let bt = fiat_25519_tight_field_element(*b);
    let mut sum_loose = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_add(&mut sum_loose, &at, &bt);
    let mut sum = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry(&mut sum, &sum_loose);

    let zero = fiat_25519_tight_field_element([0; 5]);
    let mut neg_loose = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_sub(&mut neg_loose, &zero, &sum);
    let mut r = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry(&mut r, &neg_loose);
    *out = r.0;
}

/// Unpack 200-byte slot (5 × LE u64 limb chunks at offsets 0/40/80/120/160).
#[inline(always)]
pub fn unpack_xyzt5(p: &[u8; 200]) -> [Fe5; 5] {
    let mut out = [[0u64; 5]; 5];
    for i in 0..5 {
        unsafe {
            let src = p.as_ptr().add(i * 40) as *const Fe5;
            out[i] = core::ptr::read_unaligned(src);
        }
    }
    out
}

#[inline(always)]
pub fn pack_xyzt5(p: &mut [u8; 200], limbs: &[Fe5; 5]) {
    for i in 0..5 {
        unsafe {
            let dst = p.as_mut_ptr().add(i * 40) as *mut Fe5;
            core::ptr::write_unaligned(dst, limbs[i]);
        }
    }
}
