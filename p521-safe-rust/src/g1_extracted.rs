//! AUTO-GENERATED — do not edit.
//!
//! Emitted by Rocq from the borrow-checked rust_cmd_ed body
//! `p521_g1_add_body` in `src/Bedrock/Curve/NistG1AddRustCmd.v`
//! (printer: `RustCmdToRust.rs_body_extract`; borrow certificate:
//! `p521_g1_add_borrow_ok`, Qed).  Point ABI: X || Y || Z felem
//! buffers; see `extracted_leaves.rs` for the leaf shims.
//! Regenerate via `Eval vm_compute in p521_g1_add_rs`.

#[allow(unused_imports)]
use crate::extracted_leaves::*;

pub fn p521_g1_add_extracted(out: &mut [u8; 198], arg0: &mut [u8; 198], arg1: &mut [u8; 198]) {
    let mut X1: [u8; 66] = [0; 66];
    let mut Y1: [u8; 66] = [0; 66];
    let mut Z1: [u8; 66] = [0; 66];
    let mut X2: [u8; 66] = [0; 66];
    let mut Y2: [u8; 66] = [0; 66];
    let mut Z2: [u8; 66] = [0; 66];
    let mut cA: [u8; 66] = [0; 66];
    let mut cB3: [u8; 66] = [0; 66];
    let mut t0: [u8; 66] = [0; 66];
    let mut t1: [u8; 66] = [0; 66];
    let mut t2: [u8; 66] = [0; 66];
    let mut m1: [u8; 66] = [0; 66];
    let mut m2: [u8; 66] = [0; 66];
    let mut m3: [u8; 66] = [0; 66];
    let mut m4: [u8; 66] = [0; 66];
    let mut t3f: [u8; 66] = [0; 66];
    let mut m5: [u8; 66] = [0; 66];
    let mut m6: [u8; 66] = [0; 66];
    let mut m7: [u8; 66] = [0; 66];
    let mut m8: [u8; 66] = [0; 66];
    let mut t4m: [u8; 66] = [0; 66];
    let mut m9: [u8; 66] = [0; 66];
    let mut m10: [u8; 66] = [0; 66];
    let mut m11: [u8; 66] = [0; 66];
    let mut m12: [u8; 66] = [0; 66];
    let mut t5f: [u8; 66] = [0; 66];
    let mut za: [u8; 66] = [0; 66];
    let mut zb: [u8; 66] = [0; 66];
    let mut zc: [u8; 66] = [0; 66];
    let mut xv: [u8; 66] = [0; 66];
    let mut zv: [u8; 66] = [0; 66];
    let mut yv: [u8; 66] = [0; 66];
    let mut d1: [u8; 66] = [0; 66];
    let mut d2: [u8; 66] = [0; 66];
    let mut v1: [u8; 66] = [0; 66];
    let mut w2: [u8; 66] = [0; 66];
    let mut ta: [u8; 66] = [0; 66];
    let mut v2: [u8; 66] = [0; 66];
    let mut v3: [u8; 66] = [0; 66];
    let mut w3: [u8; 66] = [0; 66];
    let mut q1: [u8; 66] = [0; 66];
    let mut q2: [u8; 66] = [0; 66];
    let mut q3: [u8; 66] = [0; 66];
    let mut x2: [u8; 66] = [0; 66];
    let mut z4: [u8; 66] = [0; 66];
    let mut X3: [u8; 66] = [0; 66];
    let mut Y3: [u8; 66] = [0; 66];
    let mut Z3: [u8; 66] = [0; 66];
    for i in 0u64..66u64 {
        let bv: u64 = arg0[((i.wrapping_add(0u64))) as usize] as u64;
        X1[(i) as usize] = (bv) as u8
    };
    for i in 0u64..66u64 {
        let bv: u64 = arg0[((i.wrapping_add(66u64))) as usize] as u64;
        Y1[(i) as usize] = (bv) as u8
    };
    for i in 0u64..66u64 {
        let bv: u64 = arg0[((i.wrapping_add(132u64))) as usize] as u64;
        Z1[(i) as usize] = (bv) as u8
    };
    for i in 0u64..66u64 {
        let bv: u64 = arg1[((i.wrapping_add(0u64))) as usize] as u64;
        X2[(i) as usize] = (bv) as u8
    };
    for i in 0u64..66u64 {
        let bv: u64 = arg1[((i.wrapping_add(66u64))) as usize] as u64;
        Y2[(i) as usize] = (bv) as u8
    };
    for i in 0u64..66u64 {
        let bv: u64 = arg1[((i.wrapping_add(132u64))) as usize] as u64;
        Z2[(i) as usize] = (bv) as u8
    };
    cA.copy_from_slice(&[252u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 1u8]);
    cB3.copy_from_slice(&[0u8, 189u8, 240u8, 65u8, 125u8, 95u8, 207u8, 205u8, 213u8, 158u8, 132u8, 183u8, 152u8, 158u8, 91u8, 160u8, 21u8, 61u8, 21u8, 179u8, 55u8, 66u8, 248u8, 66u8, 113u8, 186u8, 123u8, 197u8, 245u8, 171u8, 75u8, 2u8, 164u8, 29u8, 211u8, 172u8, 180u8, 156u8, 29u8, 42u8, 219u8, 65u8, 25u8, 205u8, 18u8, 87u8, 143u8, 232u8, 203u8, 194u8, 143u8, 35u8, 226u8, 100u8, 206u8, 183u8, 94u8, 206u8, 85u8, 170u8, 36u8, 44u8, 188u8, 191u8, 244u8, 0u8]);
    unsafe { p521_fp_mul(t0.as_mut_ptr(), X1.as_ptr(), X2.as_ptr()) };
    unsafe { p521_fp_mul(t1.as_mut_ptr(), Y1.as_ptr(), Y2.as_ptr()) };
    unsafe { p521_fp_mul(t2.as_mut_ptr(), Z1.as_ptr(), Z2.as_ptr()) };
    unsafe { p521_fp_add(m1.as_mut_ptr(), X1.as_ptr(), Y1.as_ptr()) };
    unsafe { p521_fp_add(m2.as_mut_ptr(), X2.as_ptr(), Y2.as_ptr()) };
    unsafe { p521_fp_mul(m3.as_mut_ptr(), m1.as_ptr(), m2.as_ptr()) };
    unsafe { p521_fp_add(m4.as_mut_ptr(), t0.as_ptr(), t1.as_ptr()) };
    unsafe { p521_fp_sub(t3f.as_mut_ptr(), m3.as_ptr(), m4.as_ptr()) };
    unsafe { p521_fp_add(m5.as_mut_ptr(), X1.as_ptr(), Z1.as_ptr()) };
    unsafe { p521_fp_add(m6.as_mut_ptr(), X2.as_ptr(), Z2.as_ptr()) };
    unsafe { p521_fp_mul(m7.as_mut_ptr(), m5.as_ptr(), m6.as_ptr()) };
    unsafe { p521_fp_add(m8.as_mut_ptr(), t0.as_ptr(), t2.as_ptr()) };
    unsafe { p521_fp_sub(t4m.as_mut_ptr(), m7.as_ptr(), m8.as_ptr()) };
    unsafe { p521_fp_add(m9.as_mut_ptr(), Y1.as_ptr(), Z1.as_ptr()) };
    unsafe { p521_fp_add(m10.as_mut_ptr(), Y2.as_ptr(), Z2.as_ptr()) };
    unsafe { p521_fp_mul(m11.as_mut_ptr(), m9.as_ptr(), m10.as_ptr()) };
    unsafe { p521_fp_add(m12.as_mut_ptr(), t1.as_ptr(), t2.as_ptr()) };
    unsafe { p521_fp_sub(t5f.as_mut_ptr(), m11.as_ptr(), m12.as_ptr()) };
    unsafe { p521_fp_mul(za.as_mut_ptr(), cA.as_ptr(), t4m.as_ptr()) };
    unsafe { p521_fp_mul(zb.as_mut_ptr(), cB3.as_ptr(), t2.as_ptr()) };
    unsafe { p521_fp_add(zc.as_mut_ptr(), zb.as_ptr(), za.as_ptr()) };
    unsafe { p521_fp_sub(xv.as_mut_ptr(), t1.as_ptr(), zc.as_ptr()) };
    unsafe { p521_fp_add(zv.as_mut_ptr(), zc.as_ptr(), t1.as_ptr()) };
    unsafe { p521_fp_mul(yv.as_mut_ptr(), xv.as_ptr(), zv.as_ptr()) };
    unsafe { p521_fp_add(d1.as_mut_ptr(), t0.as_ptr(), t0.as_ptr()) };
    unsafe { p521_fp_add(d2.as_mut_ptr(), d1.as_ptr(), t0.as_ptr()) };
    unsafe { p521_fp_mul(v1.as_mut_ptr(), cA.as_ptr(), t2.as_ptr()) };
    unsafe { p521_fp_mul(w2.as_mut_ptr(), cB3.as_ptr(), t4m.as_ptr()) };
    unsafe { p521_fp_add(ta.as_mut_ptr(), d2.as_ptr(), v1.as_ptr()) };
    unsafe { p521_fp_sub(v2.as_mut_ptr(), t0.as_ptr(), v1.as_ptr()) };
    unsafe { p521_fp_mul(v3.as_mut_ptr(), cA.as_ptr(), v2.as_ptr()) };
    unsafe { p521_fp_add(w3.as_mut_ptr(), w2.as_ptr(), v3.as_ptr()) };
    unsafe { p521_fp_mul(q1.as_mut_ptr(), ta.as_ptr(), w3.as_ptr()) };
    unsafe { p521_fp_add(Y3.as_mut_ptr(), yv.as_ptr(), q1.as_ptr()) };
    unsafe { p521_fp_mul(q2.as_mut_ptr(), t5f.as_ptr(), w3.as_ptr()) };
    unsafe { p521_fp_mul(x2.as_mut_ptr(), t3f.as_ptr(), xv.as_ptr()) };
    unsafe { p521_fp_sub(X3.as_mut_ptr(), x2.as_ptr(), q2.as_ptr()) };
    unsafe { p521_fp_mul(q3.as_mut_ptr(), t3f.as_ptr(), ta.as_ptr()) };
    unsafe { p521_fp_mul(z4.as_mut_ptr(), t5f.as_ptr(), zv.as_ptr()) };
    unsafe { p521_fp_add(Z3.as_mut_ptr(), z4.as_ptr(), q3.as_ptr()) };
    for i in 0u64..66u64 {
        let bv: u64 = X3[(i) as usize] as u64;
        out[((i.wrapping_add(0u64))) as usize] = (bv) as u8
    };
    for i in 0u64..66u64 {
        let bv: u64 = Y3[(i) as usize] as u64;
        out[((i.wrapping_add(66u64))) as usize] = (bv) as u8
    };
    for i in 0u64..66u64 {
        let bv: u64 = Z3[(i) as usize] as u64;
        out[((i.wrapping_add(132u64))) as usize] = (bv) as u8
    };
}
