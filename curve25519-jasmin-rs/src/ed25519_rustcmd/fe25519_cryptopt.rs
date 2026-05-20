//! Hybrid `fe25519_*` shim for the decomposed Ed25519 bodies:
//!   - mul/square route through CryptOpt-superoptimized
//!     `fiat_curve25519_solinas_*` assembly (4×64 saturated Solinas) —
//!     verified by CryptOpt's `check_equivalence` against fiat-crypto's
//!     solinas spec.
//!   - add/sub/carry stay on fiat-rust's 5×51 (same path as the
//!     portable B1 shim).
//!
//! ## Empirical result (Zen 4, 2026-05-12)
//!
//! On the Ed25519 sign KAT (RFC 8032 TEST 2, 1-byte message):
//!   - B1 (fiat-rust 5×51 everywhere):  527 µs
//!   - B2 (this shim, CryptOpt mul/sq): 696 µs   ← REGRESSION ~30%
//!   - dalek (hand-tuned AVX2):          17.6 µs
//!
//! The 5×51 ↔ 4×64 bridge cost dominates over CryptOpt's asm savings.
//! Per-call microbench:
//!   - fiat_25519_carry_mul (bare):                15.5 ns
//!   - cryptopt asm (bare):                        11.1 ns
//!   - cryptopt + 5x51 ↔ 4x64 + Solinas fold:      ~70 ns (measured)
//!   - fiat 5×51 full B1 shim (with byte-slot codec): 57 ns
//!
//! The Solinas re-fold required to safely re-import CryptOpt's
//! [0, 2^256) output into fiat's [0, 2^255) `from_bytes` API erases
//! the asm win.  See `benches/fe25519_micro.rs`.
//!
//! ## Why the bridge is unavoidable in *this* ABI
//!
//! The decomposed bodies emit / consume 40-byte byte slots
//! (`le_split 40 z`) and call `fe25519_*` as an `extern "C"` ABI.
//! The portable shim binds those bytes to fiat's 5×51 tight form.
//! Swapping in 4×64 saturated at the leaf boundary would require
//! changing the in-body representation (40 bytes interpreted as
//! 4×64 saturated rather than 32 LE bytes of canonical 5×51) AND
//! providing 4×64 add/sub/canonicalize that match the
//! extended-Edwards arithmetic.  An attempt at that pure-4×64 path
//! was abandoned after the Ed25519 KATs failed (saturated carry
//! handling at the 256th bit subtly disagrees with the `Ta`/`Tb`
//! convention used in the decomposed `XyztAdd` body — debug not
//! pursued; see the principled gap analysis in the B2 report).
//!
//! ## Conclusion
//!
//! **B2 (drop-in CryptOpt asm under the 5×51 ABI) is NOT a win on
//! Zen 4 / Ed25519.**  To realize CryptOpt's per-op speed-up at the
//! protocol level, the ENTIRE field representation in the decomposed
//! bodies must change to 4×64 saturated (eliminating the bridge), or
//! the asm itself must accept 5×51 inputs (a different CryptOpt run).
//! The architectural gap to dalek (20 µs) is dominated by:
//!   - precomputed base-point table (dalek caches ~30 KB),
//!   - inlining of scalar-mul into compiled Rust (no FFI per leaf),
//!   - hand-tuned wNAF / Niels representations.
//! CryptOpt-grade asm under our extracted-body chain caps near
//! ~300 µs even in the best case (~5× of dalek), not 20 µs.

#![cfg(all(feature = "decomposed_leaves", feature = "cryptopt_leaves", not(feature = "dalek_leaves")))]
#![allow(non_snake_case)]

use fiat_crypto::curve25519_64::{
    fiat_25519_add, fiat_25519_carry, fiat_25519_from_bytes,
    fiat_25519_loose_field_element, fiat_25519_relax, fiat_25519_sub,
    fiat_25519_tight_field_element, fiat_25519_to_bytes,
};

unsafe extern "C" {
    fn fiat_curve25519_solinas_mul(out: *mut u64, a: *const u64, b: *const u64);
    fn fiat_curve25519_solinas_square(out: *mut u64, a: *const u64);
}

// ---------------------------------------------------------------------------
// Byte slot (40 LE bytes, top 8 zero) ↔ fiat 5×51 tight.

#[inline(always)]
fn read_tight(bytes: &[u8; 40]) -> fiat_25519_tight_field_element {
    let mut head = [0u8; 32];
    head.copy_from_slice(&bytes[0..32]);
    head[31] &= 0x7f;
    let mut out = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_from_bytes(&mut out, &head);
    out
}

#[inline(always)]
fn write_tight(bytes: &mut [u8; 40], fe: &fiat_25519_tight_field_element) {
    let mut head = [0u8; 32];
    fiat_25519_to_bytes(&mut head, fe);
    bytes[0..32].copy_from_slice(&head);
    for byte in &mut bytes[32..40] {
        *byte = 0;
    }
}

#[inline(always)]
fn relax(fe: &fiat_25519_tight_field_element) -> fiat_25519_loose_field_element {
    let mut out = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_relax(&mut out, fe);
    out
}

#[inline(always)]
unsafe fn read_tight_ptr(p: *const u8) -> fiat_25519_tight_field_element {
    let r: &[u8; 40] = unsafe { &*(p as *const [u8; 40]) };
    read_tight(r)
}

#[inline(always)]
unsafe fn write_tight_ptr(p: *mut u8, fe: &fiat_25519_tight_field_element) {
    let w: &mut [u8; 40] = unsafe { &mut *(p as *mut [u8; 40]) };
    write_tight(w, fe);
}

// ---------------------------------------------------------------------------
// Bridge: tight 5×51 → 32 LE bytes → 4×u64 → CryptOpt asm → 4×u64 → 32 LE
// bytes → tight 5×51.

/// Total-function helper to read a little-endian `u64` from a fixed offset
/// of a `[u8; 32]`.  Compile-time bounds check; no `unwrap`/`unsafe`.
///
/// See `docs/performance-and-panic-freeness-2026-05-13.md` §2.3 step (b).
#[inline(always)]
fn u64_from_le_at_32<const OFFSET: usize>(bytes: &[u8; 32]) -> u64 {
    const { assert!(OFFSET + 8 <= 32, "OFFSET out of range for [u8; 32]") };
    let chunk: [u8; 8] = [
        bytes[OFFSET],
        bytes[OFFSET + 1],
        bytes[OFFSET + 2],
        bytes[OFFSET + 3],
        bytes[OFFSET + 4],
        bytes[OFFSET + 5],
        bytes[OFFSET + 6],
        bytes[OFFSET + 7],
    ];
    u64::from_le_bytes(chunk)
}

#[inline(always)]
fn tight_to_4x64(fe: &fiat_25519_tight_field_element) -> [u64; 4] {
    let mut bytes = [0u8; 32];
    fiat_25519_to_bytes(&mut bytes, fe);
    [
        u64_from_le_at_32::<0>(&bytes),
        u64_from_le_at_32::<8>(&bytes),
        u64_from_le_at_32::<16>(&bytes),
        u64_from_le_at_32::<24>(&bytes),
    ]
}

#[inline(always)]
fn from_4x64(v: &[u64; 4]) -> fiat_25519_tight_field_element {
    // CryptOpt asm output is in [0, 2^256) — may have bit 255 set.
    // Solinas-fold the top bit into the low limb:
    //   out := (v & (2^255-1)) + 19 * (v >> 255).
    // This gives a value < 2^255 + 19, which fiat_25519_from_bytes
    // accepts (it expects inputs < 2^255).  One additional partial
    // reduction inside fiat_25519_from_bytes handles the [2^255 - 19,
    // 2^255 + 19) overflow range correctly.
    let hi = v[3] >> 63;
    let mut w = [v[0], v[1], v[2], v[3] & 0x7fff_ffff_ffff_ffff];
    let (s0, c0) = w[0].overflowing_add(19u64.wrapping_mul(hi));
    w[0] = s0;
    let (s1, c1) = w[1].overflowing_add(c0 as u64);
    w[1] = s1;
    let (s2, c2) = w[2].overflowing_add(c1 as u64);
    w[2] = s2;
    let (s3, _) = w[3].overflowing_add(c2 as u64);
    w[3] = s3;
    // Now w < 2^255 + 19 < 2^256, bit 255 is 0 (since fold ate it).
    // Actually bit 255 of w is 0 iff w < 2^255.  After the fold,
    // worst case is w[3] = 0x7fff_ffff_ffff_ffff + 1 = 0x8000... which
    // sets bit 255.  Mask it again with one more Solinas fold:
    let hi2 = w[3] >> 63;
    w[3] &= 0x7fff_ffff_ffff_ffff;
    let (t0, ct0) = w[0].overflowing_add(19u64.wrapping_mul(hi2));
    w[0] = t0;
    let (t1, ct1) = w[1].overflowing_add(ct0 as u64);
    w[1] = t1;
    let (t2, ct2) = w[2].overflowing_add(ct1 as u64);
    w[2] = t2;
    let (t3, _) = w[3].overflowing_add(ct2 as u64);
    w[3] = t3;
    // Now w < 2^255 + 38, bit 255 is 0 (after at most two folds).
    let mut bytes = [0u8; 32];
    bytes[0..8].copy_from_slice(&w[0].to_le_bytes());
    bytes[8..16].copy_from_slice(&w[1].to_le_bytes());
    bytes[16..24].copy_from_slice(&w[2].to_le_bytes());
    bytes[24..32].copy_from_slice(&w[3].to_le_bytes());
    let mut out = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_from_bytes(&mut out, &bytes);
    out
}

#[inline(always)]
fn cryptopt_mul(a: &fiat_25519_tight_field_element, b: &fiat_25519_tight_field_element)
    -> fiat_25519_tight_field_element
{
    let a4 = tight_to_4x64(a);
    let b4 = tight_to_4x64(b);
    let mut out4 = [0u64; 4];
    unsafe { fiat_curve25519_solinas_mul(out4.as_mut_ptr(), a4.as_ptr(), b4.as_ptr()); }
    from_4x64(&out4)
}

#[inline(always)]
fn cryptopt_sqr(a: &fiat_25519_tight_field_element) -> fiat_25519_tight_field_element {
    let a4 = tight_to_4x64(a);
    let mut out4 = [0u64; 4];
    unsafe { fiat_curve25519_solinas_square(out4.as_mut_ptr(), a4.as_ptr()); }
    from_4x64(&out4)
}

// ---------------------------------------------------------------------------
// 2d_25519 in 5×51 tight (same as portable shim).
const TWO_D_LIMBS: [u64; 5] = [
    1859910466990425u64,
    932731440258426u64,
    1072319116312658u64,
    1815898335770999u64,
    633789495995903u64,
];

// ---------------------------------------------------------------------------
// FFI surface.  Same `extern "C"` ABI as `fe25519_portable.rs`.

#[unsafe(no_mangle)]
pub unsafe extern "C" fn fe25519_add(out: *mut u8, a: *const u8, b: *const u8) {
    let at = unsafe { read_tight_ptr(a) };
    let bt = unsafe { read_tight_ptr(b) };
    let mut sum = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_add(&mut sum, &at, &bt);
    let mut r = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry(&mut r, &sum);
    unsafe { write_tight_ptr(out, &r) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn fe25519_sub(out: *mut u8, a: *const u8, b: *const u8) {
    let at = unsafe { read_tight_ptr(a) };
    let bt = unsafe { read_tight_ptr(b) };
    let mut diff = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_sub(&mut diff, &at, &bt);
    let mut r = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry(&mut r, &diff);
    unsafe { write_tight_ptr(out, &r) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn fe25519_mul(out: *mut u8, a: *const u8, b: *const u8) {
    let at = unsafe { read_tight_ptr(a) };
    let bt = unsafe { read_tight_ptr(b) };
    let r = cryptopt_mul(&at, &bt);
    unsafe { write_tight_ptr(out, &r) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn fe25519_sqr(out: *mut u8, a: *const u8) {
    let at = unsafe { read_tight_ptr(a) };
    let r = cryptopt_sqr(&at);
    unsafe { write_tight_ptr(out, &r) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn fe25519_mul_2(out: *mut u8, a: *const u8) {
    let at = unsafe { read_tight_ptr(a) };
    let mut sum = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_add(&mut sum, &at, &at);
    let mut r = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry(&mut r, &sum);
    unsafe { write_tight_ptr(out, &r) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn fe25519_mul_d2(out: *mut u8, a: *const u8) {
    let at = unsafe { read_tight_ptr(a) };
    // 2d as 5×51 tight; route through CryptOpt asm.
    let two_d_tight = fiat_25519_tight_field_element(TWO_D_LIMBS);
    let r = cryptopt_mul(&at, &two_d_tight);
    unsafe { write_tight_ptr(out, &r) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn fe25519_sqr_scale2(out: *mut u8, a: *const u8) {
    let at = unsafe { read_tight_ptr(a) };
    let sq = cryptopt_sqr(&at);
    let mut twice = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_add(&mut twice, &sq, &sq);
    let mut r = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry(&mut r, &twice);
    unsafe { write_tight_ptr(out, &r) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn fe25519_sqr_sub2(
    out: *mut u8,
    a: *const u8,
    b: *const u8,
    c: *const u8,
) {
    let at = unsafe { read_tight_ptr(a) };
    let sq = cryptopt_sqr(&at);

    let bt = unsafe { read_tight_ptr(b) };
    let mut diff1_loose = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_sub(&mut diff1_loose, &sq, &bt);
    let mut diff1 = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry(&mut diff1, &diff1_loose);

    let ct = unsafe { read_tight_ptr(c) };
    let mut diff2_loose = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_sub(&mut diff2_loose, &diff1, &ct);
    let mut r = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry(&mut r, &diff2_loose);
    unsafe { write_tight_ptr(out, &r) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn fe25519_neg_add(out: *mut u8, a: *const u8, b: *const u8) {
    let at = unsafe { read_tight_ptr(a) };
    let bt = unsafe { read_tight_ptr(b) };
    let mut sum_loose = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_add(&mut sum_loose, &at, &bt);
    let mut sum = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry(&mut sum, &sum_loose);

    let zero = fiat_25519_tight_field_element([0; 5]);
    let mut neg_loose = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_sub(&mut neg_loose, &zero, &sum);
    let mut r = fiat_25519_tight_field_element([0; 5]);
    fiat_25519_carry(&mut r, &neg_loose);
    unsafe { write_tight_ptr(out, &r) };
}

// xyzt pack / unpack / copy — pure byte moves (same as portable).

#[unsafe(no_mangle)]
pub unsafe extern "C" fn fe25519_unpack_xyzt5(
    x: *mut u8, y: *mut u8, z: *mut u8, ta: *mut u8, tb: *mut u8, p: *const u8,
) {
    unsafe {
        core::ptr::copy_nonoverlapping(p, x, 40);
        core::ptr::copy_nonoverlapping(p.add(40), y, 40);
        core::ptr::copy_nonoverlapping(p.add(80), z, 40);
        core::ptr::copy_nonoverlapping(p.add(120), ta, 40);
        core::ptr::copy_nonoverlapping(p.add(160), tb, 40);
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn fe25519_pack_xyzt5(
    out: *mut u8, x: *const u8, y: *const u8, z: *const u8, ta: *const u8, tb: *const u8,
) {
    unsafe {
        core::ptr::copy_nonoverlapping(x, out, 40);
        core::ptr::copy_nonoverlapping(y, out.add(40), 40);
        core::ptr::copy_nonoverlapping(z, out.add(80), 40);
        core::ptr::copy_nonoverlapping(ta, out.add(120), 40);
        core::ptr::copy_nonoverlapping(tb, out.add(160), 40);
    }
}

#[cfg(not(feature = "jasminc_leaves"))]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fe25519_xyzt_copy(out: *mut u8, src: *const u8) {
    unsafe { core::ptr::copy_nonoverlapping(src, out, 200) };
}
