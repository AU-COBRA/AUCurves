//! AUTO-GENERATED — do not edit.
//!
//! Emitted by Rocq from the borrow-checked rust_cmd_ed body
//! `p224_g1_add_body` in `src/Bedrock/Curve/NistG1AddRustCmd.v`
//! (printer: `RustCmdToRust.rs_body_extract`; borrow certificate:
//! `p224_g1_add_borrow_ok`, Qed).  Point ABI: X || Y || Z felem
//! buffers; see `extracted_leaves.rs` for the leaf shims.
//! Regenerate via `Eval vm_compute in p224_g1_add_rs`.

#[allow(unused_imports)]
use crate::extracted_leaves::*;

pub fn p224_g1_add_extracted(out: &mut [u8; 96], arg0: &mut [u8; 96], arg1: &mut [u8; 96]) {
    let mut X1: [u8; 32] = [0; 32];
    let mut Y1: [u8; 32] = [0; 32];
    let mut Z1: [u8; 32] = [0; 32];
    let mut X2: [u8; 32] = [0; 32];
    let mut Y2: [u8; 32] = [0; 32];
    let mut Z2: [u8; 32] = [0; 32];
    let mut cA: [u8; 32] = [0; 32];
    let mut cB3: [u8; 32] = [0; 32];
    let mut t0: [u8; 32] = [0; 32];
    let mut t1: [u8; 32] = [0; 32];
    let mut t2: [u8; 32] = [0; 32];
    let mut m1: [u8; 32] = [0; 32];
    let mut m2: [u8; 32] = [0; 32];
    let mut m3: [u8; 32] = [0; 32];
    let mut m4: [u8; 32] = [0; 32];
    let mut t3f: [u8; 32] = [0; 32];
    let mut m5: [u8; 32] = [0; 32];
    let mut m6: [u8; 32] = [0; 32];
    let mut m7: [u8; 32] = [0; 32];
    let mut m8: [u8; 32] = [0; 32];
    let mut t4m: [u8; 32] = [0; 32];
    let mut m9: [u8; 32] = [0; 32];
    let mut m10: [u8; 32] = [0; 32];
    let mut m11: [u8; 32] = [0; 32];
    let mut m12: [u8; 32] = [0; 32];
    let mut t5f: [u8; 32] = [0; 32];
    let mut za: [u8; 32] = [0; 32];
    let mut zb: [u8; 32] = [0; 32];
    let mut zc: [u8; 32] = [0; 32];
    let mut xv: [u8; 32] = [0; 32];
    let mut zv: [u8; 32] = [0; 32];
    let mut yv: [u8; 32] = [0; 32];
    let mut d1: [u8; 32] = [0; 32];
    let mut d2: [u8; 32] = [0; 32];
    let mut v1: [u8; 32] = [0; 32];
    let mut w2: [u8; 32] = [0; 32];
    let mut ta: [u8; 32] = [0; 32];
    let mut v2: [u8; 32] = [0; 32];
    let mut v3: [u8; 32] = [0; 32];
    let mut w3: [u8; 32] = [0; 32];
    let mut q1: [u8; 32] = [0; 32];
    let mut q2: [u8; 32] = [0; 32];
    let mut q3: [u8; 32] = [0; 32];
    let mut x2: [u8; 32] = [0; 32];
    let mut z4: [u8; 32] = [0; 32];
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
    for i in 0u64..32u64 {
        let bv: u64 = arg1[((i.wrapping_add(0u64))) as usize] as u64;
        X2[(i) as usize] = (bv) as u8
    };
    for i in 0u64..32u64 {
        let bv: u64 = arg1[((i.wrapping_add(32u64))) as usize] as u64;
        Y2[(i) as usize] = (bv) as u8
    };
    for i in 0u64..32u64 {
        let bv: u64 = arg1[((i.wrapping_add(64u64))) as usize] as u64;
        Z2[(i) as usize] = (bv) as u8
    };
    cA.copy_from_slice(&[1u8, 0u8, 0u8, 0u8, 3u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 255u8, 255u8, 255u8, 255u8, 252u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 0u8, 0u8, 0u8, 0u8]);
    cB3.copy_from_slice(&[102u8, 13u8, 65u8, 43u8, 227u8, 105u8, 58u8, 182u8, 50u8, 57u8, 208u8, 102u8, 220u8, 72u8, 112u8, 49u8, 243u8, 131u8, 247u8, 88u8, 202u8, 47u8, 108u8, 185u8, 185u8, 142u8, 64u8, 127u8, 0u8, 0u8, 0u8, 0u8]);
    unsafe { p224_fp_mul(t0.as_mut_ptr(), X1.as_ptr(), X2.as_ptr()) };
    unsafe { p224_fp_mul(t1.as_mut_ptr(), Y1.as_ptr(), Y2.as_ptr()) };
    unsafe { p224_fp_mul(t2.as_mut_ptr(), Z1.as_ptr(), Z2.as_ptr()) };
    unsafe { p224_fp_add(m1.as_mut_ptr(), X1.as_ptr(), Y1.as_ptr()) };
    unsafe { p224_fp_add(m2.as_mut_ptr(), X2.as_ptr(), Y2.as_ptr()) };
    unsafe { p224_fp_mul(m3.as_mut_ptr(), m1.as_ptr(), m2.as_ptr()) };
    unsafe { p224_fp_add(m4.as_mut_ptr(), t0.as_ptr(), t1.as_ptr()) };
    unsafe { p224_fp_sub(t3f.as_mut_ptr(), m3.as_ptr(), m4.as_ptr()) };
    unsafe { p224_fp_add(m5.as_mut_ptr(), X1.as_ptr(), Z1.as_ptr()) };
    unsafe { p224_fp_add(m6.as_mut_ptr(), X2.as_ptr(), Z2.as_ptr()) };
    unsafe { p224_fp_mul(m7.as_mut_ptr(), m5.as_ptr(), m6.as_ptr()) };
    unsafe { p224_fp_add(m8.as_mut_ptr(), t0.as_ptr(), t2.as_ptr()) };
    unsafe { p224_fp_sub(t4m.as_mut_ptr(), m7.as_ptr(), m8.as_ptr()) };
    unsafe { p224_fp_add(m9.as_mut_ptr(), Y1.as_ptr(), Z1.as_ptr()) };
    unsafe { p224_fp_add(m10.as_mut_ptr(), Y2.as_ptr(), Z2.as_ptr()) };
    unsafe { p224_fp_mul(m11.as_mut_ptr(), m9.as_ptr(), m10.as_ptr()) };
    unsafe { p224_fp_add(m12.as_mut_ptr(), t1.as_ptr(), t2.as_ptr()) };
    unsafe { p224_fp_sub(t5f.as_mut_ptr(), m11.as_ptr(), m12.as_ptr()) };
    unsafe { p224_fp_mul(za.as_mut_ptr(), cA.as_ptr(), t4m.as_ptr()) };
    unsafe { p224_fp_mul(zb.as_mut_ptr(), cB3.as_ptr(), t2.as_ptr()) };
    unsafe { p224_fp_add(zc.as_mut_ptr(), zb.as_ptr(), za.as_ptr()) };
    unsafe { p224_fp_sub(xv.as_mut_ptr(), t1.as_ptr(), zc.as_ptr()) };
    unsafe { p224_fp_add(zv.as_mut_ptr(), zc.as_ptr(), t1.as_ptr()) };
    unsafe { p224_fp_mul(yv.as_mut_ptr(), xv.as_ptr(), zv.as_ptr()) };
    unsafe { p224_fp_add(d1.as_mut_ptr(), t0.as_ptr(), t0.as_ptr()) };
    unsafe { p224_fp_add(d2.as_mut_ptr(), d1.as_ptr(), t0.as_ptr()) };
    unsafe { p224_fp_mul(v1.as_mut_ptr(), cA.as_ptr(), t2.as_ptr()) };
    unsafe { p224_fp_mul(w2.as_mut_ptr(), cB3.as_ptr(), t4m.as_ptr()) };
    unsafe { p224_fp_add(ta.as_mut_ptr(), d2.as_ptr(), v1.as_ptr()) };
    unsafe { p224_fp_sub(v2.as_mut_ptr(), t0.as_ptr(), v1.as_ptr()) };
    unsafe { p224_fp_mul(v3.as_mut_ptr(), cA.as_ptr(), v2.as_ptr()) };
    unsafe { p224_fp_add(w3.as_mut_ptr(), w2.as_ptr(), v3.as_ptr()) };
    unsafe { p224_fp_mul(q1.as_mut_ptr(), ta.as_ptr(), w3.as_ptr()) };
    unsafe { p224_fp_add(Y3.as_mut_ptr(), yv.as_ptr(), q1.as_ptr()) };
    unsafe { p224_fp_mul(q2.as_mut_ptr(), t5f.as_ptr(), w3.as_ptr()) };
    unsafe { p224_fp_mul(x2.as_mut_ptr(), t3f.as_ptr(), xv.as_ptr()) };
    unsafe { p224_fp_sub(X3.as_mut_ptr(), x2.as_ptr(), q2.as_ptr()) };
    unsafe { p224_fp_mul(q3.as_mut_ptr(), t3f.as_ptr(), ta.as_ptr()) };
    unsafe { p224_fp_mul(z4.as_mut_ptr(), t5f.as_ptr(), zv.as_ptr()) };
    unsafe { p224_fp_add(Z3.as_mut_ptr(), z4.as_ptr(), q3.as_ptr()) };
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
