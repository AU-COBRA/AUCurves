//! AUTO-GENERATED — do not edit.
//!
//! Emitted by Rocq from the borrow-checked `rust_cmd_ed` body
//! `p256_wnaf_body` in `src/Bedrock/Curve/NistWnafScalarMultRustCmd.v`
//! (printer: `RustCmdToRust.rs_body_extract_inline`; borrow certificate:
//! `p256_wnaf_borrow_ok`, Qed).  Regenerate via
//! `Eval vm_compute in p256_wnaf_rs`.
//!
//! This is the w = 4, 257-digit single-scalar wNAF driver that
//! `Bedrock.Group.ScalarMult.P256_wNAF_Instance.p256_wnaf_single_full`
//! (Qed) proves computes `k * P`, transcribed to the packed 96-byte
//! point ABI of `g1_extracted.rs`.  It calls `p256_g1_add_extracted`
//! (also Rocq-emitted) for every group operation and `p256_fp_opp`
//! (leaf shim) for the digit sign.
//!
//! ABI
//!   out  : the result point, X || Y || Z, 32 little-endian Montgomery
//!          bytes each
//!   arg0 : the base point P, same layout
//!   arg1 : scratch for the odd-multiples table [1P; 3P; 5P; 7P]; the
//!          body BUILDS it (one doubling, three additions) — it is not
//!          a caller input
//!   arg2 : the 257 wNAF digits, each a two's-complement i64 in a u64
//!          (`wnaf::wnaf_digits_w4` produces them)
//!
//! NOT CONSTANT TIME.  The driver branches on `d != 0` and on the digit
//! sign, and indexes the table at a digit-derived index.  Use it for
//! public scalars only; `group::g1_scalar_mul` remains the constant-time
//! path.  See the header of the Rocq file for the full argument.
//!
//! Verified: this text is byte-identical to `Eval vm_compute in p256_wnaf_rs`
//! from `src/Bedrock/Curve/NistWnafScalarMultRustCmd.v` (checked 2026-08-29).
#![allow(non_snake_case, unused_assignments, unused_mut, unused_parens, dead_code)]

#[allow(unused_imports)]
use crate::extracted_leaves::*;
#[allow(unused_imports)]
use crate::g1_extracted::p256_g1_add_extracted;

#[inline(always)]
pub fn p256_wnaf_scalar_mul_extracted(out: &mut [u8; 96], arg0: &mut [u8; 96], arg1: &mut [[u8; 96]; 4], arg2: &mut [u64; 257]) {
    let mut e0: [u8; 96] = [0; 96];
    let mut e1: [u8; 96] = [0; 96];
    let mut e2: [u8; 96] = [0; 96];
    let mut e3: [u8; 96] = [0; 96];
    let mut dbl: [u8; 96] = [0; 96];
    let mut t1: [u8; 96] = [0; 96];
    let mut t2: [u8; 96] = [0; 96];
    let mut aux: [u8; 96] = [0; 96];
    let mut auy: [u8; 32] = [0; 32];
    let mut auyn: [u8; 32] = [0; 32];
    let mut d: u64 = 0;
    let mut ld: u64 = 0u64;
    let mut ti: u64 = 0u64;
    let mut iter: u64 = 257u64;
    for ci in 0u64..96u64 {
        let cb: u64 = arg0[(ci) as usize] as u64;
        e0[(ci) as usize] = (cb) as u8
    };
    arg1[(0u64) as usize] = e0;
    for ci in 0u64..96u64 {
        let cb: u64 = e0[(ci) as usize] as u64;
        t1[(ci) as usize] = (cb) as u8
    };
    p256_g1_add_extracted(unsafe { &mut *(dbl.as_mut_ptr() as *mut [u8; 96]) }, unsafe { &mut *(e0.as_mut_ptr() as *mut [u8; 96]) }, unsafe { &mut *(t1.as_mut_ptr() as *mut [u8; 96]) });
    p256_g1_add_extracted(unsafe { &mut *(e1.as_mut_ptr() as *mut [u8; 96]) }, unsafe { &mut *(e0.as_mut_ptr() as *mut [u8; 96]) }, unsafe { &mut *(dbl.as_mut_ptr() as *mut [u8; 96]) });
    arg1[(1u64) as usize] = e1;
    p256_g1_add_extracted(unsafe { &mut *(e2.as_mut_ptr() as *mut [u8; 96]) }, unsafe { &mut *(e1.as_mut_ptr() as *mut [u8; 96]) }, unsafe { &mut *(dbl.as_mut_ptr() as *mut [u8; 96]) });
    arg1[(2u64) as usize] = e2;
    p256_g1_add_extracted(unsafe { &mut *(e3.as_mut_ptr() as *mut [u8; 96]) }, unsafe { &mut *(e2.as_mut_ptr() as *mut [u8; 96]) }, unsafe { &mut *(dbl.as_mut_ptr() as *mut [u8; 96]) });
    arg1[(3u64) as usize] = e3;
    out.copy_from_slice(&[0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 254u8, 255u8, 255u8, 255u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
    while (((0u64 < iter) as u64)) != 0 {
        iter = (iter.wrapping_sub(1u64));
        for ci in 0u64..96u64 {
            let cb: u64 = out[(ci) as usize] as u64;
            t1[(ci) as usize] = (cb) as u8
        };
        for ci in 0u64..96u64 {
            let cb: u64 = out[(ci) as usize] as u64;
            t2[(ci) as usize] = (cb) as u8
        };
        p256_g1_add_extracted(unsafe { &mut *(out.as_mut_ptr() as *mut [u8; 96]) }, unsafe { &mut *(t1.as_mut_ptr() as *mut [u8; 96]) }, unsafe { &mut *(t2.as_mut_ptr() as *mut [u8; 96]) });
        d = arg2[(iter) as usize];
        if (d) != 0 {
            if (((d >> 63u64) & 1u64)) != 0 {
                ld = (0u64.wrapping_sub(d))
            } else {
                ld = d
            };
            ti = ((ld.wrapping_sub(1u64)) >> 1u64);
            aux = arg1[(ti) as usize];
            if (((d >> 63u64) & 1u64)) != 0 {
                for yi in 0u64..32u64 {
                    let yb: u64 = aux[((yi.wrapping_add(32u64))) as usize] as u64;
                    auy[(yi) as usize] = (yb) as u8
                };
                unsafe { p256_fp_opp(auyn.as_mut_ptr(), auy.as_ptr()) };
                for yi in 0u64..32u64 {
                    let yb: u64 = auyn[(yi) as usize] as u64;
                    aux[((yi.wrapping_add(32u64))) as usize] = (yb) as u8
                }
            } else {
                ()
            };
            for ci in 0u64..96u64 {
                let cb: u64 = out[(ci) as usize] as u64;
                t1[(ci) as usize] = (cb) as u8
            };
            p256_g1_add_extracted(unsafe { &mut *(out.as_mut_ptr() as *mut [u8; 96]) }, unsafe { &mut *(t1.as_mut_ptr() as *mut [u8; 96]) }, unsafe { &mut *(aux.as_mut_ptr() as *mut [u8; 96]) })
        } else {
            ()
        }
    };
}
