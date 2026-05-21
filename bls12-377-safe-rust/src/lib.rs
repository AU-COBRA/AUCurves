//! BLS12-377 field arithmetic — fiat-rust leaves + Bernstein-Yang inverse.
//!
//! Field operations (add, sub, mul, square, opp, to/from Montgomery,
//! to/from bytes) come from the auto-generated, machine-checked
//! `fiat-crypto/fiat-rust/src/bls12_377_64.rs`.  Constant-time modular
//! inversion comes from the Bernstein-Yang divstep port in
//! `safegcd-rs/src/safegcd_bls12_377.rs` (BLS12-377-specific prime
//! constant; convergence cert in
//! `src/Arithmetic/safegcd/divsteps_bls12_377_half.v`).
//!
//! 377-bit prime, 6×u64 saturated limb representation.
//! Curve seed u = 0x8508c00000000001 (positive, unlike BLS12-381's
//! negative u).

#![allow(non_snake_case, non_camel_case_types)]
#![allow(unused_assignments, unused_variables, unused_mut, unused_parens, dead_code)]

pub use fiat_crypto::bls12_377_64::fiat_bls12_377_montgomery_domain_field_element as Fp;
pub use fiat_crypto::bls12_377_64::fiat_bls12_377_non_montgomery_domain_field_element as FpRaw;

use fiat_crypto::bls12_377_64::*;

#[inline] pub fn fp_add(out: &mut Fp, x: &Fp, y: &Fp)     { fiat_bls12_377_add(out, x, y) }
#[inline] pub fn fp_sub(out: &mut Fp, x: &Fp, y: &Fp)     { fiat_bls12_377_sub(out, x, y) }
#[inline] pub fn fp_mul(out: &mut Fp, x: &Fp, y: &Fp)     { fiat_bls12_377_mul(out, x, y) }
#[inline] pub fn fp_square(out: &mut Fp, x: &Fp)          { fiat_bls12_377_square(out, x) }
#[inline] pub fn fp_opp(out: &mut Fp, x: &Fp)             { fiat_bls12_377_opp(out, x) }
#[inline] pub fn fp_to_bytes(out: &mut [u8; 377/8 + (377%8>0) as usize], x: &Fp) {
    fiat_bls12_377_to_bytes(out, &x.0)
}
#[inline] pub fn fp_from_bytes(out: &mut FpRaw, bs: &[u8; 377/8 + (377%8>0) as usize]) {
    fiat_bls12_377_from_bytes(&mut out.0, bs)
}
#[inline] pub fn fp_to_montgomery(out: &mut Fp, x: &FpRaw)    { fiat_bls12_377_to_montgomery(out, x) }
#[inline] pub fn fp_from_montgomery(out: &mut FpRaw, x: &Fp)  { fiat_bls12_377_from_montgomery(out, x) }

/// Constant-time modular inverse via the Bernstein–Yang divstep port.
/// Input/output are in Montgomery form.  Convert out → invert → convert in.
pub fn fp_inv(out: &mut Fp, x: &Fp) {
    let mut raw_in = FpRaw([0u64; 6]);
    fp_from_montgomery(&mut raw_in, x);
    let mut raw_inv = [0u64; 6];
    safegcd::safegcd_bls12_377::bls12_377_invert_divstep_sat(&mut raw_inv, &raw_in.0);
    fp_to_montgomery(out, &FpRaw(raw_inv));
}

/// Bernstein–Yang raw inverse on canonical 6×u64 limbs (NOT in
/// Montgomery form).  Kept for callers that want to operate outside
/// the Montgomery domain.
pub fn invert_raw(out: &mut [u64; 6], x: &[u64; 6]) {
    safegcd::safegcd_bls12_377::bls12_377_invert_divstep_sat(out, x);
}

// ─── extern "C" shim: provide the `_bls377_*` symbols the tower
// expects.  Each shim copies its arguments into Fp records, calls the
// fiat-rust wrapper from this same crate, and copies the result back.
// Tuple-struct repr is not guaranteed equivalent to its inner array
// without `#[repr(transparent)]`, so we go through explicit copies
// rather than pointer casts.  All 9 leaves the tower's extern block
// declares are covered here.
mod extern_shim {
    use super::*;
    use core::ptr::copy_nonoverlapping;

    #[inline] fn rd6(p: *const u64) -> [u64; 6] {
        let mut a = [0u64; 6]; unsafe { copy_nonoverlapping(p, a.as_mut_ptr(), 6) }; a
    }
    #[inline] fn wr6(p: *mut u64, a: &[u64; 6]) {
        unsafe { copy_nonoverlapping(a.as_ptr(), p, 6) }
    }

    // When the `jasmin_leaves` feature is on, `_bls377_add` and
    // `_bls377_sub` are provided by the assembled Jasmin .s in
    // asm/ (see ../build.rs).  Otherwise they fall back to the
    // fiat-rust Rust shim below.
    #[cfg(not(feature = "jasmin_leaves"))]
    #[no_mangle] pub unsafe extern "C" fn _bls377_add(o: *mut u64, x: *const u64, y: *const u64) {
        let mut out = Fp([0u64; 6]);
        fp_add(&mut out, &Fp(rd6(x)), &Fp(rd6(y)));
        wr6(o, &out.0);
    }
    #[cfg(not(feature = "jasmin_leaves"))]
    #[no_mangle] pub unsafe extern "C" fn _bls377_sub(o: *mut u64, x: *const u64, y: *const u64) {
        let mut out = Fp([0u64; 6]);
        fp_sub(&mut out, &Fp(rd6(x)), &Fp(rd6(y)));
        wr6(o, &out.0);
    }
    #[no_mangle] pub unsafe extern "C" fn _bls377_mul(o: *mut u64, x: *const u64, y: *const u64) {
        let mut out = Fp([0u64; 6]);
        fp_mul(&mut out, &Fp(rd6(x)), &Fp(rd6(y)));
        wr6(o, &out.0);
    }
    #[no_mangle] pub unsafe extern "C" fn _bls377_square(o: *mut u64, x: *const u64) {
        let mut out = Fp([0u64; 6]);
        fp_square(&mut out, &Fp(rd6(x)));
        wr6(o, &out.0);
    }
    #[no_mangle] pub unsafe extern "C" fn _bls377_opp(o: *mut u64, x: *const u64) {
        let mut out = Fp([0u64; 6]);
        fp_opp(&mut out, &Fp(rd6(x)));
        wr6(o, &out.0);
    }
    #[no_mangle] pub unsafe extern "C" fn _bls377_felem_copy(o: *mut u64, x: *const u64) {
        wr6(o, &rd6(x));
    }
    #[no_mangle] pub unsafe extern "C" fn _bls377_from_word(o: *mut u64, w: u64) {
        // Word w → Montgomery domain via to_montgomery(non-montgomery(w)).
        let mut raw = FpRaw([0u64; 6]);
        raw.0[0] = w;
        let mut out = Fp([0u64; 6]);
        fp_to_montgomery(&mut out, &raw);
        wr6(o, &out.0);
    }
    #[cfg(not(feature = "jasmin_leaves"))]
    #[no_mangle] pub unsafe extern "C" fn _bls377_select_znz(
        o: *mut u64, c: u64, x: *const u64, y: *const u64,
    ) {
        // Constant-time select: c == 0 picks x, else picks y.
        let x_a = rd6(x);
        let y_a = rd6(y);
        let mut out = [0u64; 6];
        let mask = (!(c == 0) as u64).wrapping_neg();  // 0 → 0, !=0 → all-ones
        for i in 0..6 { out[i] = (mask & y_a[i]) | (!mask & x_a[i]); }
        wr6(o, &out);
    }
    #[no_mangle] pub unsafe extern "C" fn _bls377_inv(o: *mut u64, x: *const u64) {
        let mut out = Fp([0u64; 6]);
        fp_inv(&mut out, &Fp(rd6(x)));
        wr6(o, &out.0);
    }
}

// Safe tower generated by ToSafeRustBody.v (Coq-verified translation:
// SafeRustSimulation.safe_cmd_correct).  51 functions across Fp2/Fp6/
// Fp12 + Miller loop + final exponentiation + pairing.  Now fully
// linkable thanks to the `extern_shim` module above (which provides
// the `_bls377_*` C-ABI symbols by re-routing into the fiat-rust
// wrappers).
pub mod tower {
    include!(concat!(env!("CARGO_MANIFEST_DIR"), "/generated/bls12_377_safe_tower.rs"));
}

pub use tower::{Fp2, Fp6, Fp12};

#[cfg(test)]
mod kat;
