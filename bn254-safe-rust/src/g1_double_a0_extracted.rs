//! Rocq-EMITTED complete projective doubling for BN254 (alt_bn128) G1
//! (Renes–Costello–Batina 2015, Algorithm 9; a = 0, 18 field ops =
//! 8 M + 1 m_3b + 9 add/sub).
//!
//! DO NOT EDIT the body below by hand.  It is the verbatim output of
//!
//!   Compute bn254_g1_double_a0_rs.       (* §4 of *)
//!   src/Bedrock/Curve/CurveDoubleA0RustCmd.v
//!
//! driven by `src/Bedrock/Curve/EmitDoubleA0Rust.v`, with only the
//! Coq string-literal quoting stripped.
//!
//! Verification status of what is emitted:
//!   * `PointDoubleA0.rcb_double_a0_correct` — the Rupicola derivation
//!     of a bedrock2 body for `rcb_double_a0_gallina` — is Qed, 0 axioms.
//!   * `PointDoubleA0.rcb_double_a0_eq_ladderstep` proves that Gallina
//!     body equal, coordinate for coordinate, to
//!     `ladderstep_gallina three_b X X Y Y Z Z` on every on-curve input.
//!   * `bn254_g1_double_a0_borrow_ok` holds by `vm_compute`.
//!   * The `cB3` constant below is
//!     `mont_bytes 4 bn254_m ((3*b) mod m)`, certified
//!     `bn254_threeb_bytes_len = 32`.
//!
//! Point ABI: one `[u8; 96]` holding X ‖ Y ‖ Z, each felem 32 bytes =
//! 4 little-endian u64 Montgomery limbs.  The leaves are the byte-ABI
//! shims in `crate::extracted_leaves`.
//!
//! This crate has no projective-G1 point type, so the wrappers below
//! are byte- and limb-level rather than struct-level.

use crate::extracted_leaves::{bn254_fp_add, bn254_fp_mul, bn254_fp_sub, FBYTES, LIMBS};

pub const PTBYTES: usize = 3 * FBYTES;

/// Byte-level entry point: `out` and `p` are X ‖ Y ‖ Z in the leaf
/// (Montgomery, little-endian limb) representation.
#[inline]
pub fn g1_proj_double_bytes(out: &mut [u8; PTBYTES], p: &[u8; PTBYTES]) {
    let mut inb = *p;
    bn254_g1_double_a0_extracted(out, &mut inb);
}

/// Limb-level entry point, for callers holding `[u64; LIMBS]` triples.
#[inline]
pub fn g1_proj_double_limbs(p: &[[u64; LIMBS]; 3]) -> [[u64; LIMBS]; 3] {
    let mut inb = [0u8; PTBYTES];
    for (i, f) in p.iter().enumerate() {
        for (j, w) in f.iter().enumerate() {
            inb[i * FBYTES + 8 * j..i * FBYTES + 8 * j + 8]
                .copy_from_slice(&w.to_le_bytes());
        }
    }
    let mut outb = [0u8; PTBYTES];
    bn254_g1_double_a0_extracted(&mut outb, &mut inb);
    let mut r = [[0u64; LIMBS]; 3];
    for (i, f) in r.iter_mut().enumerate() {
        for (j, w) in f.iter_mut().enumerate() {
            let mut t = [0u8; 8];
            t.copy_from_slice(&outb[i * FBYTES + 8 * j..i * FBYTES + 8 * j + 8]);
            *w = u64::from_le_bytes(t);
        }
    }
    r
}

// ─────────── everything below this line is emitted verbatim ───────────

pub fn bn254_g1_double_a0_extracted(out: &mut [u8; 96], arg0: &mut [u8; 96]) {
    let mut X1: [u8; 32] = [0; 32];
    let mut Y1: [u8; 32] = [0; 32];
    let mut Z1: [u8; 32] = [0; 32];
    let mut cB3: [u8; 32] = [0; 32];
    let mut t0: [u8; 32] = [0; 32];
    let mut za: [u8; 32] = [0; 32];
    let mut zb: [u8; 32] = [0; 32];
    let mut zc: [u8; 32] = [0; 32];
    let mut t1: [u8; 32] = [0; 32];
    let mut t2: [u8; 32] = [0; 32];
    let mut t2b: [u8; 32] = [0; 32];
    let mut xa: [u8; 32] = [0; 32];
    let mut ya: [u8; 32] = [0; 32];
    let mut t1b: [u8; 32] = [0; 32];
    let mut t2c: [u8; 32] = [0; 32];
    let mut t0b: [u8; 32] = [0; 32];
    let mut yb: [u8; 32] = [0; 32];
    let mut t1c: [u8; 32] = [0; 32];
    let mut xb: [u8; 32] = [0; 32];
    let mut X3: [u8; 32] = [0; 32];
    let mut Y3: [u8; 32] = [0; 32];
    let mut Z3: [u8; 32] = [0; 32];
    for i in 0u64..32u64 {
        let bv: u64 = arg0[((i.wrapping_add(0u64))) as usize] as u64;
        X1[(i) as usize] = (bv) as u8
    };
    for i in 0u64..32u64 {
        let bv: u64 = arg0[((i.wrapping_add(32u64))) as usize] as u64;
        Y1[(i) as usize] = (bv) as u8
    };
    for i in 0u64..32u64 {
        let bv: u64 = arg0[((i.wrapping_add(64u64))) as usize] as u64;
        Z1[(i) as usize] = (bv) as u8
    };
    cB3.copy_from_slice(&[247u8, 127u8, 13u8, 65u8, 206u8, 71u8, 6u8, 246u8, 17u8, 208u8, 27u8, 211u8, 77u8, 111u8, 61u8, 47u8, 209u8, 198u8, 64u8, 57u8, 126u8, 51u8, 67u8, 41u8, 87u8, 152u8, 227u8, 167u8, 232u8, 152u8, 149u8, 29u8]);
    unsafe { bn254_fp_mul(t0.as_mut_ptr(), Y1.as_ptr(), Y1.as_ptr()) };
    unsafe { bn254_fp_add(za.as_mut_ptr(), t0.as_ptr(), t0.as_ptr()) };
    unsafe { bn254_fp_add(zb.as_mut_ptr(), za.as_ptr(), za.as_ptr()) };
    unsafe { bn254_fp_add(zc.as_mut_ptr(), zb.as_ptr(), zb.as_ptr()) };
    unsafe { bn254_fp_mul(t1.as_mut_ptr(), Y1.as_ptr(), Z1.as_ptr()) };
    unsafe { bn254_fp_mul(t2.as_mut_ptr(), Z1.as_ptr(), Z1.as_ptr()) };
    unsafe { bn254_fp_mul(t2b.as_mut_ptr(), cB3.as_ptr(), t2.as_ptr()) };
    unsafe { bn254_fp_mul(xa.as_mut_ptr(), t2b.as_ptr(), zc.as_ptr()) };
    unsafe { bn254_fp_add(ya.as_mut_ptr(), t0.as_ptr(), t2b.as_ptr()) };
    unsafe { bn254_fp_mul(Z3.as_mut_ptr(), t1.as_ptr(), zc.as_ptr()) };
    unsafe { bn254_fp_add(t1b.as_mut_ptr(), t2b.as_ptr(), t2b.as_ptr()) };
    unsafe { bn254_fp_add(t2c.as_mut_ptr(), t1b.as_ptr(), t2b.as_ptr()) };
    unsafe { bn254_fp_sub(t0b.as_mut_ptr(), t0.as_ptr(), t2c.as_ptr()) };
    unsafe { bn254_fp_mul(yb.as_mut_ptr(), t0b.as_ptr(), ya.as_ptr()) };
    unsafe { bn254_fp_add(Y3.as_mut_ptr(), xa.as_ptr(), yb.as_ptr()) };
    unsafe { bn254_fp_mul(t1c.as_mut_ptr(), X1.as_ptr(), Y1.as_ptr()) };
    unsafe { bn254_fp_mul(xb.as_mut_ptr(), t0b.as_ptr(), t1c.as_ptr()) };
    unsafe { bn254_fp_add(X3.as_mut_ptr(), xb.as_ptr(), xb.as_ptr()) };
    for i in 0u64..32u64 {
        let bv: u64 = X3[(i) as usize] as u64;
        out[((i.wrapping_add(0u64))) as usize] = (bv) as u8
    };
    for i in 0u64..32u64 {
        let bv: u64 = Y3[(i) as usize] as u64;
        out[((i.wrapping_add(32u64))) as usize] = (bv) as u8
    };
    for i in 0u64..32u64 {
        let bv: u64 = Z3[(i) as usize] as u64;
        out[((i.wrapping_add(64u64))) as usize] = (bv) as u8
    };
}
