//! Inline limb-typed `xyzt_{add,double}_decomposed` — Rust-level
//! `#[inline(always)]` bodies that call `fe25519_inline::*`
//! `#[inline(always)]` field ops over `[u64; 5]` limb slots.
//!
//! Closes the remaining static-lib boundary cost: LLVM inlines the
//! 18 field ops in `xyzt_add_decomposed` (11 in `xyzt_double_decomposed`)
//! into one function body so limbs stay in registers across the
//! whole sequence.  The exported `#[unsafe(no_mangle)]` extern "C"
//! wrappers preserve the symbol surface the `wnaf_comb` body
//! extern-calls.
//!
//! Activated by `--features tfp25519_inline_limbs` (which implies
//! `tfp25519_limbs` and through it `xyzt_limb_abi`).  When active,
//! the auto-extracted `decomposed_bodies_limbs.rs` exports are
//! suppressed and the linker picks these up instead.

#![cfg(feature = "tfp25519_inline_limbs")]
#![allow(non_snake_case)]

use super::fe25519_inline::{
    Fe5, fe25519_add, fe25519_mul, fe25519_mul_2, fe25519_mul_d2, fe25519_neg_add,
    fe25519_sqr, fe25519_sqr_scale2, fe25519_sqr_sub2, fe25519_sub,
    pack_xyzt5, unpack_xyzt5,
};

#[inline(always)]
fn xyzt_add_inline(out: &mut [u8; 200], arg0: &[u8; 200], arg1: &[u8; 200]) {
    let [X1, Y1, Z1, Ta1, Tb1] = unpack_xyzt5(arg0);
    let [X2, Y2, Z2, Ta2, Tb2] = unpack_xyzt5(arg1);

    let mut T1: Fe5 = [0; 5];
    let mut T2: Fe5 = [0; 5];
    let mut A: Fe5 = [0; 5];
    let mut B: Fe5 = [0; 5];
    let mut C: Fe5 = [0; 5];
    let mut D: Fe5 = [0; 5];
    let mut E: Fe5 = [0; 5];
    let mut F: Fe5 = [0; 5];
    let mut G: Fe5 = [0; 5];
    let mut H: Fe5 = [0; 5];
    let mut X3: Fe5 = [0; 5];
    let mut Y3: Fe5 = [0; 5];
    let mut Z3: Fe5 = [0; 5];
    let mut tmp1: Fe5 = [0; 5];
    let mut tmp2: Fe5 = [0; 5];

    fe25519_mul(&mut T1, &Ta1, &Tb1);
    fe25519_mul(&mut T2, &Ta2, &Tb2);
    fe25519_sub(&mut tmp1, &Y1, &X1);
    fe25519_sub(&mut tmp2, &Y2, &X2);
    fe25519_mul(&mut A, &tmp1, &tmp2);
    fe25519_add(&mut tmp1, &Y1, &X1);
    fe25519_add(&mut tmp2, &Y2, &X2);
    fe25519_mul(&mut B, &tmp1, &tmp2);
    fe25519_mul_d2(&mut tmp1, &T1);
    fe25519_mul(&mut C, &tmp1, &T2);
    fe25519_mul(&mut tmp1, &Z1, &Z2);
    fe25519_mul_2(&mut D, &tmp1);
    fe25519_sub(&mut E, &B, &A);
    fe25519_sub(&mut F, &D, &C);
    fe25519_add(&mut G, &D, &C);
    fe25519_add(&mut H, &B, &A);
    fe25519_mul(&mut X3, &E, &F);
    fe25519_mul(&mut Y3, &G, &H);
    fe25519_mul(&mut Z3, &F, &G);

    pack_xyzt5(out, &[X3, Y3, Z3, E, H]);
}

#[inline(always)]
fn xyzt_double_inline(out: &mut [u8; 200], arg0: &[u8; 200]) {
    let [X, Y, Z, _Ta, _Tb] = unpack_xyzt5(arg0);

    let mut A: Fe5 = [0; 5];
    let mut B: Fe5 = [0; 5];
    let mut C: Fe5 = [0; 5];
    let mut E: Fe5 = [0; 5];
    let mut F: Fe5 = [0; 5];
    let mut G: Fe5 = [0; 5];
    let mut H: Fe5 = [0; 5];
    let mut XpY: Fe5 = [0; 5];
    let mut Xo: Fe5 = [0; 5];
    let mut Yo: Fe5 = [0; 5];
    let mut Zo: Fe5 = [0; 5];

    fe25519_sqr(&mut A, &X);
    fe25519_sqr(&mut B, &Y);
    fe25519_sqr_scale2(&mut C, &Z);
    fe25519_add(&mut XpY, &X, &Y);
    fe25519_sqr_sub2(&mut E, &XpY, &A, &B);
    fe25519_sub(&mut G, &B, &A);
    fe25519_neg_add(&mut H, &A, &B);
    fe25519_sub(&mut F, &G, &C);
    fe25519_mul(&mut Xo, &E, &F);
    fe25519_mul(&mut Yo, &G, &H);
    fe25519_mul(&mut Zo, &F, &G);

    pack_xyzt5(out, &[Xo, Yo, Zo, E, H]);
}

/// extern "C" symbol surface — `wnaf_comb` body and other extern callers
/// see the same name; LLVM inlines `xyzt_add_inline`'s 18 ops into here.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn xyzt_add_decomposed(
    out_raw: *mut u8, arg0_raw: *const u8, arg1_raw: *const u8,
) {
    let out: &mut [u8; 200] = unsafe { &mut *(out_raw as *mut [u8; 200]) };
    let arg0: &[u8; 200] = unsafe { &*(arg0_raw as *const [u8; 200]) };
    let arg1: &[u8; 200] = unsafe { &*(arg1_raw as *const [u8; 200]) };
    xyzt_add_inline(out, arg0, arg1);
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xyzt_double_decomposed(
    out_raw: *mut u8, arg0_raw: *const u8,
) {
    let out: &mut [u8; 200] = unsafe { &mut *(out_raw as *mut [u8; 200]) };
    let arg0: &[u8; 200] = unsafe { &*(arg0_raw as *const [u8; 200]) };
    xyzt_double_inline(out, arg0);
}
