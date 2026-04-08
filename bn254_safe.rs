//! Safe Rust wrappers for verified BN254 arithmetic.
//!
//! Generated from bedrock2 separation logic specifications.
//! - Read-only buffers map to `&T` (shared references).
//! - Mutated buffers map to `&mut T` (mutable references).
//! - Separating conjunction (⋆) maps to Rust's aliasing XOR mutability.
//!
//! All `unsafe` is confined to the wrapper bodies; the API is safe.
#![allow(non_camel_case_types)]

#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp(pub [u64; 4]);

impl Fp {
    /// Create from raw little-endian limbs (Montgomery form).
    #[inline] pub const fn from_limbs(limbs: [u64; 4]) -> Self { Fp(limbs) }
    /// Zero element.
    #[inline] pub const fn zero() -> Self { Fp([0u64; 4]) }
    /// Borrow as raw limb array.
    #[inline] pub fn as_limbs(&self) -> &[u64; 4] { &self.0 }
    /// Mutably borrow as raw limb array.
    #[inline] pub fn as_limbs_mut(&mut self) -> &mut [u64; 4] { &mut self.0 }
}

#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp2(pub [u64; 8]);

impl Fp2 {
    /// Create from raw little-endian limbs (Montgomery form).
    #[inline] pub const fn from_limbs(limbs: [u64; 8]) -> Self { Fp2(limbs) }
    /// Zero element.
    #[inline] pub const fn zero() -> Self { Fp2([0u64; 8]) }
    /// Borrow as raw limb array.
    #[inline] pub fn as_limbs(&self) -> &[u64; 8] { &self.0 }
    /// Mutably borrow as raw limb array.
    #[inline] pub fn as_limbs_mut(&mut self) -> &mut [u64; 8] { &mut self.0 }
}

#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp6(pub [u64; 24]);

impl Fp6 {
    /// Create from raw little-endian limbs (Montgomery form).
    #[inline] pub const fn from_limbs(limbs: [u64; 24]) -> Self { Fp6(limbs) }
    /// Zero element.
    #[inline] pub const fn zero() -> Self { Fp6([0u64; 24]) }
    /// Borrow as raw limb array.
    #[inline] pub fn as_limbs(&self) -> &[u64; 24] { &self.0 }
    /// Mutably borrow as raw limb array.
    #[inline] pub fn as_limbs_mut(&mut self) -> &mut [u64; 24] { &mut self.0 }
}

#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp12(pub [u64; 48]);

impl Fp12 {
    /// Create from raw little-endian limbs (Montgomery form).
    #[inline] pub const fn from_limbs(limbs: [u64; 48]) -> Self { Fp12(limbs) }
    /// Zero element.
    #[inline] pub const fn zero() -> Self { Fp12([0u64; 48]) }
    /// Borrow as raw limb array.
    #[inline] pub fn as_limbs(&self) -> &[u64; 48] { &self.0 }
    /// Mutably borrow as raw limb array.
    #[inline] pub fn as_limbs_mut(&mut self) -> &mut [u64; 48] { &mut self.0 }
}

extern "C" {
    fn bn254_add(out: usize, x: usize, y: usize);
    fn bn254_mul(out: usize, x: usize, y: usize);
    fn bn254_square(out: usize, x: usize);
    fn bn254_pairing(out: usize, p_x: usize, p_y: usize, q_x: usize, q_y: usize);
}

/// Safe wrapper for `bn254_add`.
///
/// Non-aliasing of `&mut` arguments is enforced by Rust's borrow checker.
/// Safety follows from the bedrock2 separation logic proof of `bn254_add`.
#[inline]
pub fn fp_add(out: &mut Fp, x: &Fp, y: &Fp) {
    unsafe { bn254_add(out.as_limbs_mut().as_mut_ptr() as usize, x.as_limbs().as_ptr() as usize, y.as_limbs().as_ptr() as usize) }
}

/// Safe wrapper for `bn254_mul`.
///
/// Non-aliasing of `&mut` arguments is enforced by Rust's borrow checker.
/// Safety follows from the bedrock2 separation logic proof of `bn254_mul`.
#[inline]
pub fn fp_mul(out: &mut Fp, x: &Fp, y: &Fp) {
    unsafe { bn254_mul(out.as_limbs_mut().as_mut_ptr() as usize, x.as_limbs().as_ptr() as usize, y.as_limbs().as_ptr() as usize) }
}

/// Safe wrapper for `bn254_square`.
///
/// Non-aliasing of `&mut` arguments is enforced by Rust's borrow checker.
/// Safety follows from the bedrock2 separation logic proof of `bn254_square`.
#[inline]
pub fn fp_square(out: &mut Fp, x: &Fp) {
    unsafe { bn254_square(out.as_limbs_mut().as_mut_ptr() as usize, x.as_limbs().as_ptr() as usize) }
}

/// Safe wrapper for `bn254_pairing`.
///
/// Non-aliasing of `&mut` arguments is enforced by Rust's borrow checker.
/// Safety follows from the bedrock2 separation logic proof of `bn254_pairing`.
#[inline]
pub fn pairing(out: &mut Fp12, p_x: &Fp, p_y: &Fp, q_x: &Fp2, q_y: &Fp2) {
    unsafe { bn254_pairing(out.as_limbs_mut().as_mut_ptr() as usize, p_x.as_limbs().as_ptr() as usize, p_y.as_limbs().as_ptr() as usize, q_x.as_limbs().as_ptr() as usize, q_y.as_limbs().as_ptr() as usize) }
}
