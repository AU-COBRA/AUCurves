//! secp256k1 field arithmetic — fiat-rust leaves + Bernstein-Yang inverse.
//!
//! Field operations (add, sub, mul, square, opp, to/from Montgomery,
//! to/from bytes) come from the auto-generated, machine-checked
//! `fiat-crypto/fiat-rust/src/secp256k1_montgomery_64.rs`.  Constant-time modular
//! inversion comes from the Bernstein-Yang divstep port in
//! `safegcd-rs/src/safegcd_secp256k1.rs` (verified against the
//! convergence certificate in
//! `src/Arithmetic/safegcd/divsteps_secp256k1_half.v`).
//!
//! 256-bit prime, 4×u64 saturated limb representation.
//!
//! # The multiplication and squaring leaves
//!
//! On x86-64 with BMI2 and ADX, [`fp_mul`] and [`fp_square`] route to the
//! CryptOpt-superoptimized assembly in `generated/`, which implements the
//! *same function* as `fiat_secp256k1_montgomery_mul` /
//! `fiat_secp256k1_montgomery_square` — CryptOpt's search is over
//! instruction schedules for a fixed fiat-crypto dataflow graph, and every
//! candidate it emits has passed its `check_equivalence` pass against the
//! fiat reference.  `tests/cryptopt_diff.rs` re-establishes that numerically
//! here: the assembly and the fiat function must return identical limbs on
//! random inputs and on the boundary cases.
//!
//! The assembly comes from CryptOpt's `fiat_secp256k1_montgomery_*` seeds,
//! matching this crate's word-by-word Montgomery representation.  CryptOpt
//! also ships `fiat_secp256k1_dettman_*` leaves; those implement an
//! unsaturated representation and are NOT interchangeable with these.
//!
//! `build.rs` links the assembly only when the build host has both CPU
//! features and is not cross-compiling; otherwise, and when
//! `SECP256K1_NO_CRYPTOPT=1` is set, the fiat leaves are used unchanged.
//! [`fp_mul_fiat`] and [`fp_square_fiat`] always name the fiat versions, so
//! the two paths can be compared in the same binary.

#![allow(non_snake_case, non_camel_case_types)]

pub use fiat_crypto::secp256k1_montgomery_64::fiat_secp256k1_montgomery_montgomery_domain_field_element as Fp;
pub use fiat_crypto::secp256k1_montgomery_64::fiat_secp256k1_montgomery_non_montgomery_domain_field_element as FpRaw;

use fiat_crypto::secp256k1_montgomery_64::*;

#[cfg(secp256k1_cryptopt_asm)]
unsafe extern "C" {
    /// `out = x * y * R^-1 mod p`.  See `generated/secp256k1_mul_cryptopt.asm`.
    fn secp256k1_cryptopt_mul(out: *mut u64, x: *const u64, y: *const u64);
    /// `out = x * x * R^-1 mod p`.  See `generated/secp256k1_square_cryptopt.asm`.
    fn secp256k1_cryptopt_square(out: *mut u64, x: *const u64);
}

/// Whether this build calls the CryptOpt assembly for [`fp_mul`] and
/// [`fp_square`].  `false` means the fiat-rust leaves are in use.
pub const CRYPTOPT_ASM: bool = cfg!(secp256k1_cryptopt_asm);

#[inline] pub fn fp_add(out: &mut Fp, x: &Fp, y: &Fp)     { fiat_secp256k1_montgomery_add(out, x, y) }
#[inline] pub fn fp_sub(out: &mut Fp, x: &Fp, y: &Fp)     { fiat_secp256k1_montgomery_sub(out, x, y) }

/// `out = x * y * R^-1 mod p`, the Montgomery product.
#[inline]
pub fn fp_mul(out: &mut Fp, x: &Fp, y: &Fp) {
    // SAFETY: the three pointers come from live `&mut Fp` / `&Fp`
    // references, so each is aligned and points to 32 readable (resp.
    // writable) bytes, which is exactly what the callee touches; it retains
    // nothing.  `out` cannot alias `x` or `y`, because holding `&mut Fp` and
    // `&Fp` to the same element at once is not expressible in safe Rust and
    // this function is safe.
    #[cfg(secp256k1_cryptopt_asm)]
    unsafe {
        secp256k1_cryptopt_mul(out.0.as_mut_ptr(), x.0.as_ptr(), y.0.as_ptr())
    }
    #[cfg(not(secp256k1_cryptopt_asm))]
    fiat_secp256k1_montgomery_mul(out, x, y)
}

/// `out = x * x * R^-1 mod p`.
#[inline]
pub fn fp_square(out: &mut Fp, x: &Fp) {
    // SAFETY: as for `fp_mul`.
    #[cfg(secp256k1_cryptopt_asm)]
    unsafe {
        secp256k1_cryptopt_square(out.0.as_mut_ptr(), x.0.as_ptr())
    }
    #[cfg(not(secp256k1_cryptopt_asm))]
    fiat_secp256k1_montgomery_square(out, x)
}

/// The fiat-rust multiplication, whatever [`fp_mul`] is bound to.
/// Kept public so `tests/cryptopt_diff.rs` can compare the two paths.
#[inline] pub fn fp_mul_fiat(out: &mut Fp, x: &Fp, y: &Fp) {
    fiat_secp256k1_montgomery_mul(out, x, y)
}

/// The fiat-rust squaring, whatever [`fp_square`] is bound to.
#[inline] pub fn fp_square_fiat(out: &mut Fp, x: &Fp) {
    fiat_secp256k1_montgomery_square(out, x)
}

#[inline] pub fn fp_opp(out: &mut Fp, x: &Fp)             { fiat_secp256k1_montgomery_opp(out, x) }
#[inline] pub fn fp_to_bytes(out: &mut [u8; 256/8 + (256%8>0) as usize], x: &Fp) {
    fiat_secp256k1_montgomery_to_bytes(out, &x.0)
}
#[inline] pub fn fp_from_bytes(out: &mut FpRaw, bs: &[u8; 256/8 + (256%8>0) as usize]) {
    fiat_secp256k1_montgomery_from_bytes(&mut out.0, bs)
}
#[inline] pub fn fp_to_montgomery(out: &mut Fp, x: &FpRaw)    { fiat_secp256k1_montgomery_to_montgomery(out, x) }
#[inline] pub fn fp_from_montgomery(out: &mut FpRaw, x: &Fp)  { fiat_secp256k1_montgomery_from_montgomery(out, x) }

/// Constant-time modular inverse via the Bernstein–Yang divstep port.
/// Input/output are in Montgomery form.  Convert out → invert → convert in.
pub fn fp_inv(out: &mut Fp, x: &Fp) {
    let mut raw_in = FpRaw([0u64; 4]);
    fp_from_montgomery(&mut raw_in, x);
    let mut raw_inv = [0u64; 4];
    safegcd::safegcd_secp256k1::secp_invert_divstep_sat(&mut raw_inv, &raw_in.0);
    fp_to_montgomery(out, &FpRaw(raw_inv));
}

#[cfg(test)]
mod kat;
