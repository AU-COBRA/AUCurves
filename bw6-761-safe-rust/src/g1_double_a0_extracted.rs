//! Rocq-EMITTED complete projective doubling for BW6-761 G1
//! (Renes–Costello–Batina 2015, Algorithm 9; a = 0, 18 field ops =
//! 8 M + 1 m_3b + 9 add/sub).
//!
//! DO NOT EDIT the body below by hand.  It is the verbatim output of
//!
//!   Compute bw6_761_g1_double_a0_rs.        (* §4 of *)
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
//!     `ladderstep_gallina three_b X X Y Y Z Z` on every on-curve input
//!     (i.e. to Algorithm 7 applied to a repeated argument).
//!   * `bw6_761_g1_double_a0_borrow_ok` holds by `vm_compute`, so the
//!     emitted `&mut` discipline is sound.
//!   * The `cB3` constant below is `mont_bytes 12 bw6_761_m ((3*b) mod m)`
//!     with `b = m − 1`, certified `bw6_761_threeb_bytes_len = 96`.
//!
//! Point ABI: one `[u8; 288]` holding X ‖ Y ‖ Z, each felem 96 bytes =
//! 12 little-endian u64 Montgomery limbs.  The leaves are the byte-ABI
//! shims in `crate::extracted_leaves`.

use crate::extracted_leaves::{bw6_761_fp_add, bw6_761_fp_mul, bw6_761_fp_sub, FBYTES};
use crate::group::G1Proj;
use crate::tower::Fp as TFp;

pub const PTBYTES: usize = 3 * FBYTES;

#[inline]
fn pack(p: &G1Proj) -> [u8; PTBYTES] {
    let mut b = [0u8; PTBYTES];
    for (i, f) in [&p.x, &p.y, &p.z].into_iter().enumerate() {
        for (j, w) in f.0.iter().enumerate() {
            b[i * FBYTES + 8 * j..i * FBYTES + 8 * j + 8].copy_from_slice(&w.to_le_bytes());
        }
    }
    b
}

#[inline]
fn unpack(b: &[u8; PTBYTES]) -> G1Proj {
    let mut c = [TFp::zero(); 3];
    for (i, f) in c.iter_mut().enumerate() {
        for (j, w) in f.0.iter_mut().enumerate() {
            let mut t = [0u8; 8];
            t.copy_from_slice(&b[i * FBYTES + 8 * j..i * FBYTES + 8 * j + 8]);
            *w = u64::from_le_bytes(t);
        }
    }
    G1Proj { x: c[0], y: c[1], z: c[2] }
}

/// Native-calling-convention wrapper around the emitted body:
/// the drop-in replacement for `group::g1_proj_double`.
///
/// `3b` is baked into the emitted body as `cB3`, so unlike
/// `g1_proj_double` this takes no `b3` argument.
#[inline]
pub fn g1_proj_double_extracted(p: &G1Proj) -> G1Proj {
    let mut inb = pack(p);
    let mut outb = [0u8; PTBYTES];
    bw6_761_g1_double_a0_extracted(&mut outb, &mut inb);
    unpack(&outb)
}

// ─────────── everything below this line is emitted verbatim ───────────

pub fn bw6_761_g1_double_a0_extracted(out: &mut [u8; 288], arg0: &mut [u8; 288]) {
    let mut X1: [u8; 96] = [0; 96];
    let mut Y1: [u8; 96] = [0; 96];
    let mut Z1: [u8; 96] = [0; 96];
    let mut cB3: [u8; 96] = [0; 96];
    let mut t0: [u8; 96] = [0; 96];
    let mut za: [u8; 96] = [0; 96];
    let mut zb: [u8; 96] = [0; 96];
    let mut zc: [u8; 96] = [0; 96];
    let mut t1: [u8; 96] = [0; 96];
    let mut t2: [u8; 96] = [0; 96];
    let mut t2b: [u8; 96] = [0; 96];
    let mut xa: [u8; 96] = [0; 96];
    let mut ya: [u8; 96] = [0; 96];
    let mut t1b: [u8; 96] = [0; 96];
    let mut t2c: [u8; 96] = [0; 96];
    let mut t0b: [u8; 96] = [0; 96];
    let mut yb: [u8; 96] = [0; 96];
    let mut t1c: [u8; 96] = [0; 96];
    let mut xb: [u8; 96] = [0; 96];
    let mut X3: [u8; 96] = [0; 96];
    let mut Y3: [u8; 96] = [0; 96];
    let mut Z3: [u8; 96] = [0; 96];
    for i in 0u64..96u64 {
        let bv: u64 = arg0[((i.wrapping_add(0u64))) as usize] as u64;
        X1[(i) as usize] = (bv) as u8
    };
    for i in 0u64..96u64 {
        let bv: u64 = arg0[((i.wrapping_add(96u64))) as usize] as u64;
        Y1[(i) as usize] = (bv) as u8
    };
    for i in 0u64..96u64 {
        let bv: u64 = arg0[((i.wrapping_add(192u64))) as usize] as u64;
        Z1[(i) as usize] = (bv) as u8
    };
    cB3.copy_from_slice(&[12u8, 111u8, 1u8, 0u8, 0u8, 0u8, 148u8, 238u8, 205u8, 89u8, 1u8, 192u8, 199u8, 203u8, 136u8, 215u8, 156u8, 163u8, 113u8, 99u8, 228u8, 173u8, 64u8, 58u8, 26u8, 47u8, 186u8, 41u8, 44u8, 25u8, 96u8, 9u8, 11u8, 215u8, 45u8, 27u8, 34u8, 114u8, 31u8, 171u8, 108u8, 145u8, 33u8, 28u8, 6u8, 146u8, 214u8, 67u8, 243u8, 119u8, 172u8, 143u8, 191u8, 201u8, 229u8, 13u8, 14u8, 134u8, 247u8, 18u8, 62u8, 238u8, 130u8, 6u8, 205u8, 100u8, 114u8, 102u8, 111u8, 108u8, 127u8, 224u8, 249u8, 63u8, 158u8, 204u8, 62u8, 121u8, 152u8, 232u8, 160u8, 1u8, 202u8, 38u8, 13u8, 109u8, 143u8, 74u8, 145u8, 20u8, 12u8, 40u8, 168u8, 1u8, 45u8, 0u8]);
    unsafe { bw6_761_fp_mul(t0.as_mut_ptr(), Y1.as_ptr(), Y1.as_ptr()) };
    unsafe { bw6_761_fp_add(za.as_mut_ptr(), t0.as_ptr(), t0.as_ptr()) };
    unsafe { bw6_761_fp_add(zb.as_mut_ptr(), za.as_ptr(), za.as_ptr()) };
    unsafe { bw6_761_fp_add(zc.as_mut_ptr(), zb.as_ptr(), zb.as_ptr()) };
    unsafe { bw6_761_fp_mul(t1.as_mut_ptr(), Y1.as_ptr(), Z1.as_ptr()) };
    unsafe { bw6_761_fp_mul(t2.as_mut_ptr(), Z1.as_ptr(), Z1.as_ptr()) };
    unsafe { bw6_761_fp_mul(t2b.as_mut_ptr(), cB3.as_ptr(), t2.as_ptr()) };
    unsafe { bw6_761_fp_mul(xa.as_mut_ptr(), t2b.as_ptr(), zc.as_ptr()) };
    unsafe { bw6_761_fp_add(ya.as_mut_ptr(), t0.as_ptr(), t2b.as_ptr()) };
    unsafe { bw6_761_fp_mul(Z3.as_mut_ptr(), t1.as_ptr(), zc.as_ptr()) };
    unsafe { bw6_761_fp_add(t1b.as_mut_ptr(), t2b.as_ptr(), t2b.as_ptr()) };
    unsafe { bw6_761_fp_add(t2c.as_mut_ptr(), t1b.as_ptr(), t2b.as_ptr()) };
    unsafe { bw6_761_fp_sub(t0b.as_mut_ptr(), t0.as_ptr(), t2c.as_ptr()) };
    unsafe { bw6_761_fp_mul(yb.as_mut_ptr(), t0b.as_ptr(), ya.as_ptr()) };
    unsafe { bw6_761_fp_add(Y3.as_mut_ptr(), xa.as_ptr(), yb.as_ptr()) };
    unsafe { bw6_761_fp_mul(t1c.as_mut_ptr(), X1.as_ptr(), Y1.as_ptr()) };
    unsafe { bw6_761_fp_mul(xb.as_mut_ptr(), t0b.as_ptr(), t1c.as_ptr()) };
    unsafe { bw6_761_fp_add(X3.as_mut_ptr(), xb.as_ptr(), xb.as_ptr()) };
    for i in 0u64..96u64 {
        let bv: u64 = X3[(i) as usize] as u64;
        out[((i.wrapping_add(0u64))) as usize] = (bv) as u8
    };
    for i in 0u64..96u64 {
        let bv: u64 = Y3[(i) as usize] as u64;
        out[((i.wrapping_add(96u64))) as usize] = (bv) as u8
    };
    for i in 0u64..96u64 {
        let bv: u64 = Z3[(i) as usize] as u64;
        out[((i.wrapping_add(192u64))) as usize] = (bv) as u8
    };
}
