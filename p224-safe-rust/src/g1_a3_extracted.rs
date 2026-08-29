//! AUTO-GENERATED — do not edit.
//!
//! Emitted by Rocq from the borrow-checked rust_cmd_ed bodies
//! `p224_g1_add_a3_body` / `p224_g1_double_a3_body` in
//! `src/Bedrock/Curve/NistA3RustCmd.v` (printer:
//! `RustCmdToRust.rs_body_extract`; borrow certificates
//! `p224_g1_add_a3_borrow_ok` / `p224_g1_double_a3_borrow_ok`, Qed).
//!
//! These are the a = -3 specialisations: Renes-Costello-Batina 2015
//! Algorithm 4 (addition, 43 ops = 14 M + 29 add/sub) and Algorithm 6
//! (doubling, 34 ops = 13 M + 21 add/sub), derived in Rocq by
//! `src/Bedrock/Group/CurveAdd/CurveAddA3.v` and
//! `src/Bedrock/Group/CurveAdd/CurveDoubleA3.v` and proved equal to the
//! general-a chain at a = -3 by
//! `src/Bedrock/Group/CurveAdd/CurveA3Equiv.v`.  They carry ONE stack
//! constant (`cB` = b in Montgomery form), where the general-a body of
//! `g1_extracted.rs` carries two (`cA` = a, `cB3` = 3b).
//!
//! Point ABI: X || Y || Z felem buffers; see `extracted_leaves.rs` for
//! the leaf shims.  Regenerate via
//! `Eval vm_compute in p224_g1_add_a3_rs` / `..._double_a3_rs`.

#[allow(unused_imports)]
use crate::extracted_leaves::*;

pub fn p224_g1_add_a3_extracted(out: &mut [u8; 96], arg0: &mut [u8; 96], arg1: &mut [u8; 96]) {
    let mut X1: [u8; 32] = [0; 32];
    let mut Y1: [u8; 32] = [0; 32];
    let mut Z1: [u8; 32] = [0; 32];
    let mut X2: [u8; 32] = [0; 32];
    let mut Y2: [u8; 32] = [0; 32];
    let mut Z2: [u8; 32] = [0; 32];
    let mut cB: [u8; 32] = [0; 32];
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
    let mut xz: [u8; 32] = [0; 32];
    let mut bz: [u8; 32] = [0; 32];
    let mut u0: [u8; 32] = [0; 32];
    let mut u1: [u8; 32] = [0; 32];
    let mut wv: [u8; 32] = [0; 32];
    let mut uu: [u8; 32] = [0; 32];
    let mut vv: [u8; 32] = [0; 32];
    let mut bx: [u8; 32] = [0; 32];
    let mut z2a: [u8; 32] = [0; 32];
    let mut z3b: [u8; 32] = [0; 32];
    let mut s0: [u8; 32] = [0; 32];
    let mut s1: [u8; 32] = [0; 32];
    let mut s2: [u8; 32] = [0; 32];
    let mut s3: [u8; 32] = [0; 32];
    let mut x2a: [u8; 32] = [0; 32];
    let mut x3b: [u8; 32] = [0; 32];
    let mut dd: [u8; 32] = [0; 32];
    let mut p1: [u8; 32] = [0; 32];
    let mut p2: [u8; 32] = [0; 32];
    let mut p3: [u8; 32] = [0; 32];
    let mut p4: [u8; 32] = [0; 32];
    let mut p5: [u8; 32] = [0; 32];
    let mut p6: [u8; 32] = [0; 32];
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
    cB.copy_from_slice(&[205u8, 89u8, 192u8, 99u8, 246u8, 205u8, 104u8, 231u8, 16u8, 19u8, 240u8, 204u8, 243u8, 194u8, 122u8, 16u8, 81u8, 129u8, 82u8, 200u8, 152u8, 186u8, 206u8, 61u8, 147u8, 47u8, 192u8, 127u8, 0u8, 0u8, 0u8, 0u8]);
    unsafe { p224_fp_mul(t0.as_mut_ptr(), X1.as_ptr(), X2.as_ptr()) };
    unsafe { p224_fp_mul(t1.as_mut_ptr(), Y1.as_ptr(), Y2.as_ptr()) };
    unsafe { p224_fp_mul(t2.as_mut_ptr(), Z1.as_ptr(), Z2.as_ptr()) };
    unsafe { p224_fp_add(m1.as_mut_ptr(), X1.as_ptr(), Y1.as_ptr()) };
    unsafe { p224_fp_add(m2.as_mut_ptr(), X2.as_ptr(), Y2.as_ptr()) };
    unsafe { p224_fp_mul(m3.as_mut_ptr(), m1.as_ptr(), m2.as_ptr()) };
    unsafe { p224_fp_add(m4.as_mut_ptr(), t0.as_ptr(), t1.as_ptr()) };
    unsafe { p224_fp_sub(t3f.as_mut_ptr(), m3.as_ptr(), m4.as_ptr()) };
    unsafe { p224_fp_add(m5.as_mut_ptr(), Y1.as_ptr(), Z1.as_ptr()) };
    unsafe { p224_fp_add(m6.as_mut_ptr(), Y2.as_ptr(), Z2.as_ptr()) };
    unsafe { p224_fp_mul(m7.as_mut_ptr(), m5.as_ptr(), m6.as_ptr()) };
    unsafe { p224_fp_add(m8.as_mut_ptr(), t1.as_ptr(), t2.as_ptr()) };
    unsafe { p224_fp_sub(t4m.as_mut_ptr(), m7.as_ptr(), m8.as_ptr()) };
    unsafe { p224_fp_add(m9.as_mut_ptr(), X1.as_ptr(), Z1.as_ptr()) };
    unsafe { p224_fp_add(m10.as_mut_ptr(), X2.as_ptr(), Z2.as_ptr()) };
    unsafe { p224_fp_mul(m11.as_mut_ptr(), m9.as_ptr(), m10.as_ptr()) };
    unsafe { p224_fp_add(m12.as_mut_ptr(), t0.as_ptr(), t2.as_ptr()) };
    unsafe { p224_fp_sub(xz.as_mut_ptr(), m11.as_ptr(), m12.as_ptr()) };
    unsafe { p224_fp_mul(bz.as_mut_ptr(), cB.as_ptr(), t2.as_ptr()) };
    unsafe { p224_fp_sub(u0.as_mut_ptr(), xz.as_ptr(), bz.as_ptr()) };
    unsafe { p224_fp_add(u1.as_mut_ptr(), u0.as_ptr(), u0.as_ptr()) };
    unsafe { p224_fp_add(wv.as_mut_ptr(), u0.as_ptr(), u1.as_ptr()) };
    unsafe { p224_fp_sub(uu.as_mut_ptr(), t1.as_ptr(), wv.as_ptr()) };
    unsafe { p224_fp_add(vv.as_mut_ptr(), t1.as_ptr(), wv.as_ptr()) };
    unsafe { p224_fp_mul(bx.as_mut_ptr(), cB.as_ptr(), xz.as_ptr()) };
    unsafe { p224_fp_add(z2a.as_mut_ptr(), t2.as_ptr(), t2.as_ptr()) };
    unsafe { p224_fp_add(z3b.as_mut_ptr(), z2a.as_ptr(), t2.as_ptr()) };
    unsafe { p224_fp_sub(s0.as_mut_ptr(), bx.as_ptr(), z3b.as_ptr()) };
    unsafe { p224_fp_sub(s1.as_mut_ptr(), s0.as_ptr(), t0.as_ptr()) };
    unsafe { p224_fp_add(s2.as_mut_ptr(), s1.as_ptr(), s1.as_ptr()) };
    unsafe { p224_fp_add(s3.as_mut_ptr(), s2.as_ptr(), s1.as_ptr()) };
    unsafe { p224_fp_add(x2a.as_mut_ptr(), t0.as_ptr(), t0.as_ptr()) };
    unsafe { p224_fp_add(x3b.as_mut_ptr(), x2a.as_ptr(), t0.as_ptr()) };
    unsafe { p224_fp_sub(dd.as_mut_ptr(), x3b.as_ptr(), z3b.as_ptr()) };
    unsafe { p224_fp_mul(p1.as_mut_ptr(), t4m.as_ptr(), s3.as_ptr()) };
    unsafe { p224_fp_mul(p2.as_mut_ptr(), dd.as_ptr(), s3.as_ptr()) };
    unsafe { p224_fp_mul(p3.as_mut_ptr(), vv.as_ptr(), uu.as_ptr()) };
    unsafe { p224_fp_add(Y3.as_mut_ptr(), p3.as_ptr(), p2.as_ptr()) };
    unsafe { p224_fp_mul(p4.as_mut_ptr(), t3f.as_ptr(), vv.as_ptr()) };
    unsafe { p224_fp_sub(X3.as_mut_ptr(), p4.as_ptr(), p1.as_ptr()) };
    unsafe { p224_fp_mul(p5.as_mut_ptr(), t4m.as_ptr(), uu.as_ptr()) };
    unsafe { p224_fp_mul(p6.as_mut_ptr(), t3f.as_ptr(), dd.as_ptr()) };
    unsafe { p224_fp_add(Z3.as_mut_ptr(), p5.as_ptr(), p6.as_ptr()) };
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

pub fn p224_g1_double_a3_extracted(out: &mut [u8; 96], arg0: &mut [u8; 96]) {
    let mut X1: [u8; 32] = [0; 32];
    let mut Y1: [u8; 32] = [0; 32];
    let mut Z1: [u8; 32] = [0; 32];
    let mut cB: [u8; 32] = [0; 32];
    let mut t0: [u8; 32] = [0; 32];
    let mut t1: [u8; 32] = [0; 32];
    let mut t2: [u8; 32] = [0; 32];
    let mut m1: [u8; 32] = [0; 32];
    let mut t3: [u8; 32] = [0; 32];
    let mut m2: [u8; 32] = [0; 32];
    let mut zxz: [u8; 32] = [0; 32];
    let mut bz: [u8; 32] = [0; 32];
    let mut y0: [u8; 32] = [0; 32];
    let mut y1: [u8; 32] = [0; 32];
    let mut y2: [u8; 32] = [0; 32];
    let mut x0: [u8; 32] = [0; 32];
    let mut y3v: [u8; 32] = [0; 32];
    let mut y4: [u8; 32] = [0; 32];
    let mut x1v: [u8; 32] = [0; 32];
    let mut z2a: [u8; 32] = [0; 32];
    let mut z3b: [u8; 32] = [0; 32];
    let mut bz2: [u8; 32] = [0; 32];
    let mut w0: [u8; 32] = [0; 32];
    let mut w1: [u8; 32] = [0; 32];
    let mut w2: [u8; 32] = [0; 32];
    let mut w3: [u8; 32] = [0; 32];
    let mut x2a: [u8; 32] = [0; 32];
    let mut x3b: [u8; 32] = [0; 32];
    let mut dd: [u8; 32] = [0; 32];
    let mut p1: [u8; 32] = [0; 32];
    let mut m3: [u8; 32] = [0; 32];
    let mut yz2: [u8; 32] = [0; 32];
    let mut p2: [u8; 32] = [0; 32];
    let mut p3: [u8; 32] = [0; 32];
    let mut p4: [u8; 32] = [0; 32];
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
    cB.copy_from_slice(&[205u8, 89u8, 192u8, 99u8, 246u8, 205u8, 104u8, 231u8, 16u8, 19u8, 240u8, 204u8, 243u8, 194u8, 122u8, 16u8, 81u8, 129u8, 82u8, 200u8, 152u8, 186u8, 206u8, 61u8, 147u8, 47u8, 192u8, 127u8, 0u8, 0u8, 0u8, 0u8]);
    unsafe { p224_fp_mul(t0.as_mut_ptr(), X1.as_ptr(), X1.as_ptr()) };
    unsafe { p224_fp_mul(t1.as_mut_ptr(), Y1.as_ptr(), Y1.as_ptr()) };
    unsafe { p224_fp_mul(t2.as_mut_ptr(), Z1.as_ptr(), Z1.as_ptr()) };
    unsafe { p224_fp_mul(m1.as_mut_ptr(), X1.as_ptr(), Y1.as_ptr()) };
    unsafe { p224_fp_add(t3.as_mut_ptr(), m1.as_ptr(), m1.as_ptr()) };
    unsafe { p224_fp_mul(m2.as_mut_ptr(), X1.as_ptr(), Z1.as_ptr()) };
    unsafe { p224_fp_add(zxz.as_mut_ptr(), m2.as_ptr(), m2.as_ptr()) };
    unsafe { p224_fp_mul(bz.as_mut_ptr(), cB.as_ptr(), t2.as_ptr()) };
    unsafe { p224_fp_sub(y0.as_mut_ptr(), bz.as_ptr(), zxz.as_ptr()) };
    unsafe { p224_fp_add(y1.as_mut_ptr(), y0.as_ptr(), y0.as_ptr()) };
    unsafe { p224_fp_add(y2.as_mut_ptr(), y1.as_ptr(), y0.as_ptr()) };
    unsafe { p224_fp_sub(x0.as_mut_ptr(), t1.as_ptr(), y2.as_ptr()) };
    unsafe { p224_fp_add(y3v.as_mut_ptr(), t1.as_ptr(), y2.as_ptr()) };
    unsafe { p224_fp_mul(y4.as_mut_ptr(), x0.as_ptr(), y3v.as_ptr()) };
    unsafe { p224_fp_mul(x1v.as_mut_ptr(), x0.as_ptr(), t3.as_ptr()) };
    unsafe { p224_fp_add(z2a.as_mut_ptr(), t2.as_ptr(), t2.as_ptr()) };
    unsafe { p224_fp_add(z3b.as_mut_ptr(), t2.as_ptr(), z2a.as_ptr()) };
    unsafe { p224_fp_mul(bz2.as_mut_ptr(), cB.as_ptr(), zxz.as_ptr()) };
    unsafe { p224_fp_sub(w0.as_mut_ptr(), bz2.as_ptr(), z3b.as_ptr()) };
    unsafe { p224_fp_sub(w1.as_mut_ptr(), w0.as_ptr(), t0.as_ptr()) };
    unsafe { p224_fp_add(w2.as_mut_ptr(), w1.as_ptr(), w1.as_ptr()) };
    unsafe { p224_fp_add(w3.as_mut_ptr(), w1.as_ptr(), w2.as_ptr()) };
    unsafe { p224_fp_add(x2a.as_mut_ptr(), t0.as_ptr(), t0.as_ptr()) };
    unsafe { p224_fp_add(x3b.as_mut_ptr(), x2a.as_ptr(), t0.as_ptr()) };
    unsafe { p224_fp_sub(dd.as_mut_ptr(), x3b.as_ptr(), z3b.as_ptr()) };
    unsafe { p224_fp_mul(p1.as_mut_ptr(), dd.as_ptr(), w3.as_ptr()) };
    unsafe { p224_fp_add(Y3.as_mut_ptr(), y4.as_ptr(), p1.as_ptr()) };
    unsafe { p224_fp_mul(m3.as_mut_ptr(), Y1.as_ptr(), Z1.as_ptr()) };
    unsafe { p224_fp_add(yz2.as_mut_ptr(), m3.as_ptr(), m3.as_ptr()) };
    unsafe { p224_fp_mul(p2.as_mut_ptr(), yz2.as_ptr(), w3.as_ptr()) };
    unsafe { p224_fp_sub(X3.as_mut_ptr(), x1v.as_ptr(), p2.as_ptr()) };
    unsafe { p224_fp_mul(p3.as_mut_ptr(), yz2.as_ptr(), t1.as_ptr()) };
    unsafe { p224_fp_add(p4.as_mut_ptr(), p3.as_ptr(), p3.as_ptr()) };
    unsafe { p224_fp_add(Z3.as_mut_ptr(), p4.as_ptr(), p4.as_ptr()) };
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
