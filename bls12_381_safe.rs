//! Safe Rust wrappers for verified BLS12_381 arithmetic.
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
pub struct Fp(pub [u64; 6]);

impl Fp {
    /// Create from raw little-endian limbs (Montgomery form).
    #[inline] pub const fn from_limbs(limbs: [u64; 6]) -> Self { Fp(limbs) }
    /// Zero element.
    #[inline] pub const fn zero() -> Self { Fp([0u64; 6]) }
    /// Borrow as raw limb array.
    #[inline] pub fn as_limbs(&self) -> &[u64; 6] { &self.0 }
    /// Mutably borrow as raw limb array.
    #[inline] pub fn as_limbs_mut(&mut self) -> &mut [u64; 6] { &mut self.0 }
}

#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp2(pub [u64; 12]);

impl Fp2 {
    /// Create from raw little-endian limbs (Montgomery form).
    #[inline] pub const fn from_limbs(limbs: [u64; 12]) -> Self { Fp2(limbs) }
    /// Zero element.
    #[inline] pub const fn zero() -> Self { Fp2([0u64; 12]) }
    /// Borrow as raw limb array.
    #[inline] pub fn as_limbs(&self) -> &[u64; 12] { &self.0 }
    /// Mutably borrow as raw limb array.
    #[inline] pub fn as_limbs_mut(&mut self) -> &mut [u64; 12] { &mut self.0 }
}

#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp6(pub [u64; 36]);

impl Fp6 {
    /// Create from raw little-endian limbs (Montgomery form).
    #[inline] pub const fn from_limbs(limbs: [u64; 36]) -> Self { Fp6(limbs) }
    /// Zero element.
    #[inline] pub const fn zero() -> Self { Fp6([0u64; 36]) }
    /// Borrow as raw limb array.
    #[inline] pub fn as_limbs(&self) -> &[u64; 36] { &self.0 }
    /// Mutably borrow as raw limb array.
    #[inline] pub fn as_limbs_mut(&mut self) -> &mut [u64; 36] { &mut self.0 }
}

#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp12(pub [u64; 72]);

impl Fp12 {
    /// Create from raw little-endian limbs (Montgomery form).
    #[inline] pub const fn from_limbs(limbs: [u64; 72]) -> Self { Fp12(limbs) }
    /// Zero element.
    #[inline] pub const fn zero() -> Self { Fp12([0u64; 72]) }
    /// Borrow as raw limb array.
    #[inline] pub fn as_limbs(&self) -> &[u64; 72] { &self.0 }
    /// Mutably borrow as raw limb array.
    #[inline] pub fn as_limbs_mut(&mut self) -> &mut [u64; 72] { &mut self.0 }
}

extern "C" {
    fn bls12_add(out: usize, x: usize, y: usize);
    fn bls12_sub(out: usize, x: usize, y: usize);
    fn bls12_mul(out: usize, x: usize, y: usize);
    fn bls12_square(out: usize, x: usize);
    fn bls12_Fp2_add(out: usize, x: usize, y: usize);
    fn bls12_Fp2_mul(out: usize, x: usize, y: usize);
    fn bls12_Fp12_mul(out: usize, x: usize, y: usize);
    fn bls12_Fp12_square(out: usize, x: usize);
    fn bls12_miller_loop(out: usize, p_x: usize, p_y: usize, q_x: usize, q_y: usize);
    fn bls12_pairing(out: usize, p_x: usize, p_y: usize, q_x: usize, q_y: usize);
}

/// Safe wrapper for `bls12_add`.
///
/// Non-aliasing of `&mut` arguments is enforced by Rust's borrow checker.
/// Safety follows from the bedrock2 separation logic proof of `bls12_add`.
#[inline]
pub fn fp_add(out: &mut Fp, x: &Fp, y: &Fp) {
    unsafe { bls12_add(out.as_limbs_mut().as_mut_ptr() as usize, x.as_limbs().as_ptr() as usize, y.as_limbs().as_ptr() as usize) }
}

/// Safe wrapper for `bls12_sub`.
///
/// Non-aliasing of `&mut` arguments is enforced by Rust's borrow checker.
/// Safety follows from the bedrock2 separation logic proof of `bls12_sub`.
#[inline]
pub fn fp_sub(out: &mut Fp, x: &Fp, y: &Fp) {
    unsafe { bls12_sub(out.as_limbs_mut().as_mut_ptr() as usize, x.as_limbs().as_ptr() as usize, y.as_limbs().as_ptr() as usize) }
}

/// Safe wrapper for `bls12_mul`.
///
/// Non-aliasing of `&mut` arguments is enforced by Rust's borrow checker.
/// Safety follows from the bedrock2 separation logic proof of `bls12_mul`.
#[inline]
pub fn fp_mul(out: &mut Fp, x: &Fp, y: &Fp) {
    unsafe { bls12_mul(out.as_limbs_mut().as_mut_ptr() as usize, x.as_limbs().as_ptr() as usize, y.as_limbs().as_ptr() as usize) }
}

/// Safe wrapper for `bls12_square`.
///
/// Non-aliasing of `&mut` arguments is enforced by Rust's borrow checker.
/// Safety follows from the bedrock2 separation logic proof of `bls12_square`.
#[inline]
pub fn fp_square(out: &mut Fp, x: &Fp) {
    unsafe { bls12_square(out.as_limbs_mut().as_mut_ptr() as usize, x.as_limbs().as_ptr() as usize) }
}

/// Safe wrapper for `bls12_Fp2_add`.
///
/// Non-aliasing of `&mut` arguments is enforced by Rust's borrow checker.
/// Safety follows from the bedrock2 separation logic proof of `bls12_Fp2_add`.
#[inline]
pub fn fp2_add(out: &mut Fp2, x: &Fp2, y: &Fp2) {
    unsafe { bls12_Fp2_add(out.as_limbs_mut().as_mut_ptr() as usize, x.as_limbs().as_ptr() as usize, y.as_limbs().as_ptr() as usize) }
}

/// Safe wrapper for `bls12_Fp2_mul`.
///
/// Non-aliasing of `&mut` arguments is enforced by Rust's borrow checker.
/// Safety follows from the bedrock2 separation logic proof of `bls12_Fp2_mul`.
#[inline]
pub fn fp2_mul(out: &mut Fp2, x: &Fp2, y: &Fp2) {
    unsafe { bls12_Fp2_mul(out.as_limbs_mut().as_mut_ptr() as usize, x.as_limbs().as_ptr() as usize, y.as_limbs().as_ptr() as usize) }
}

/// Safe wrapper for `bls12_Fp12_mul`.
///
/// Non-aliasing of `&mut` arguments is enforced by Rust's borrow checker.
/// Safety follows from the bedrock2 separation logic proof of `bls12_Fp12_mul`.
#[inline]
pub fn fp12_mul(out: &mut Fp12, x: &Fp12, y: &Fp12) {
    unsafe { bls12_Fp12_mul(out.as_limbs_mut().as_mut_ptr() as usize, x.as_limbs().as_ptr() as usize, y.as_limbs().as_ptr() as usize) }
}

/// Safe wrapper for `bls12_Fp12_square`.
///
/// Non-aliasing of `&mut` arguments is enforced by Rust's borrow checker.
/// Safety follows from the bedrock2 separation logic proof of `bls12_Fp12_square`.
#[inline]
pub fn fp12_square(out: &mut Fp12, x: &Fp12) {
    unsafe { bls12_Fp12_square(out.as_limbs_mut().as_mut_ptr() as usize, x.as_limbs().as_ptr() as usize) }
}

/// Safe wrapper for `bls12_miller_loop`.
///
/// Non-aliasing of `&mut` arguments is enforced by Rust's borrow checker.
/// Safety follows from the bedrock2 separation logic proof of `bls12_miller_loop`.
#[inline]
pub fn miller_loop(out: &mut Fp12, p_x: &Fp, p_y: &Fp, q_x: &Fp2, q_y: &Fp2) {
    unsafe { bls12_miller_loop(out.as_limbs_mut().as_mut_ptr() as usize, p_x.as_limbs().as_ptr() as usize, p_y.as_limbs().as_ptr() as usize, q_x.as_limbs().as_ptr() as usize, q_y.as_limbs().as_ptr() as usize) }
}

/// Safe wrapper for `bls12_pairing`.
///
/// Non-aliasing of `&mut` arguments is enforced by Rust's borrow checker.
/// Safety follows from the bedrock2 separation logic proof of `bls12_pairing`.
#[inline]
pub fn pairing(out: &mut Fp12, p_x: &Fp, p_y: &Fp, q_x: &Fp2, q_y: &Fp2) {
    unsafe { bls12_pairing(out.as_limbs_mut().as_mut_ptr() as usize, p_x.as_limbs().as_ptr() as usize, p_y.as_limbs().as_ptr() as usize, q_x.as_limbs().as_ptr() as usize, q_y.as_limbs().as_ptr() as usize) }
}
