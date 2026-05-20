//! Decomposed Ed25519 wNAF + comb-table scalar-mult bodies, extracted
//! from the verified `rust_cmd_ed` AST in:
//!
//!   - `AUCurves/src/Bedrock/End2End/Ed25519/WnafScalarmultBody.v`
//!   - `AUCurves/src/Bedrock/End2End/Ed25519/CombScalarmultBody.v`
//!
//! via `Bedrock/ExtractWnafCombBodies.v`.
//!
//! Both bodies dispatch their cross-body calls to the Phase A
//! verified xyzt_add_decomposed / xyzt_double_decomposed / xyzt_copy
//! leaves declared in `decomposed_bodies.rs`.  The new
//! `comb_table_lookup` leaf is provided by the `wnaf_comb_curve_leaves`
//! module in `leaves.rs` — backed by a runtime-initialised dalek
//! base-point table (one-time `EdwardsPoint::mul_base` per cell at
//! first call; ~204KB of cells × 1.5K-cycle compute => ~50ms warmup).
//!
//! Status (2026-05-12): wired but NOT proven correct end-to-end.
//! `wnaf_scalarmult_body_correct` and `comb_scalarmult_base_body_correct`
//! are both `Admitted` (PoC scope).  The wnaf body's sign-bit handling
//! is intentionally elided — see `WnafScalarmultBody.v` header for the
//! PoC limitation note.

// Auto-extracted body: the IR extractor emits constant-folded comparisons
// like `(0u64) != 0` for unconditional select-mask lookups (the "always
// pick lane 0" entry in a CT-cmov table).  Clippy's `eq_op` flags these,
// but they are intentional and correct.  We do not hand-edit this file.
#![allow(non_snake_case, unused_assignments, unused_mut, unused_variables, unused_parens, dead_code, clippy::eq_op)]

unsafe extern "C" {
    fn xyzt_add_decomposed(out: *mut u8, a: *const u8, b: *const u8);
    fn xyzt_double_decomposed(out: *mut u8, a: *const u8);
    fn xyzt_copy(out: *mut u8, src: *const u8);
    /// PoC comb-table lookup: dest := digit * 16^win_idx * B.
    /// CT through pre-init (table built once via dalek at first call).
    fn comb_table_lookup(dest: *mut u8, win_idx: u64, digit: u64);
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wnaf_scalarmult(out_raw: *mut u8, arg0_raw: *const u8, arg1_raw: *const u8) {
    let out: &mut [u8; 200] = unsafe { &mut *(out_raw as *mut [u8; 200]) };
    let arg0: &mut [u8; 64] = unsafe { &mut *(arg0_raw as *mut [u8; 64]) };
    let arg1: &mut [u8; 200] = unsafe { &mut *(arg1_raw as *mut [u8; 200]) };
    let mut T0: [u8; 200] = [0; 200];
    let mut T1: [u8; 200] = [0; 200];
    let mut T2: [u8; 200] = [0; 200];
    let mut T3: [u8; 200] = [0; 200];
    let mut T4: [u8; 200] = [0; 200];
    let mut T5: [u8; 200] = [0; 200];
    let mut T6: [u8; 200] = [0; 200];
    let mut T7: [u8; 200] = [0; 200];
    let mut TwoP: [u8; 200] = [0; 200];
    let mut Q: [u8; 200] = [0; 200];
    let mut lookup_buf: [u8; 200] = [0; 200];
    let mut Q_plus: [u8; 200] = [0; 200];
    unsafe { xyzt_double_decomposed(TwoP.as_mut_ptr(), arg1.as_ptr()) };
    unsafe { xyzt_copy(T0.as_mut_ptr(), arg1.as_ptr()) };
    unsafe { xyzt_add_decomposed(T1.as_mut_ptr(), T0.as_ptr(), TwoP.as_ptr()) };
    unsafe { xyzt_add_decomposed(T2.as_mut_ptr(), T1.as_ptr(), TwoP.as_ptr()) };
    unsafe { xyzt_add_decomposed(T3.as_mut_ptr(), T2.as_ptr(), TwoP.as_ptr()) };
    unsafe { xyzt_add_decomposed(T4.as_mut_ptr(), T3.as_ptr(), TwoP.as_ptr()) };
    unsafe { xyzt_add_decomposed(T5.as_mut_ptr(), T4.as_ptr(), TwoP.as_ptr()) };
    unsafe { xyzt_add_decomposed(T6.as_mut_ptr(), T5.as_ptr(), TwoP.as_ptr()) };
    unsafe { xyzt_add_decomposed(T7.as_mut_ptr(), T6.as_ptr(), TwoP.as_ptr()) };
    Q[(40u64) as usize] = (1u64) as u8;
    Q[(80u64) as usize] = (1u64) as u8;
    for i in 0u64..52u64 {
        let mut d: u64 = (51u64.wrapping_sub(i));
        let digit_byte: u64 = arg0[(d) as usize] as u64;
        unsafe { xyzt_double_decomposed(Q.as_mut_ptr(), Q.as_ptr()) };
        unsafe { xyzt_double_decomposed(Q.as_mut_ptr(), Q.as_ptr()) };
        unsafe { xyzt_double_decomposed(Q.as_mut_ptr(), Q.as_ptr()) };
        unsafe { xyzt_double_decomposed(Q.as_mut_ptr(), Q.as_ptr()) };
        unsafe { xyzt_double_decomposed(Q.as_mut_ptr(), Q.as_ptr()) };
        let mut magnitude: u64 = (digit_byte & 127u64);
        let mut abs_idx: u64 = (magnitude >> 1u64);
        let mut is_nonzero: u64 = magnitude;
        { let _mask: u8 = (if (0u64) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (T0[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((abs_idx.wrapping_sub(1u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (T1[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((abs_idx.wrapping_sub(2u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (T2[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((abs_idx.wrapping_sub(3u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (T3[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((abs_idx.wrapping_sub(4u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (T4[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((abs_idx.wrapping_sub(5u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (T5[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((abs_idx.wrapping_sub(6u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (T6[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((abs_idx.wrapping_sub(7u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (T7[_i] & !_mask);
          } };
        unsafe { xyzt_add_decomposed(Q_plus.as_mut_ptr(), Q.as_ptr(), lookup_buf.as_ptr()) };
        { let _mask: u8 = (if (is_nonzero) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(Q.len() as usize) {
            Q[_i] = (Q_plus[_i] & _mask) | (Q[_i] & !_mask);
          } }
    };
    unsafe { xyzt_copy(out.as_mut_ptr(), Q.as_ptr()) };
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn comb_scalarmult_base(out_raw: *mut u8, arg0_raw: *const u8) {
    let out: &mut [u8; 200] = unsafe { &mut *(out_raw as *mut [u8; 200]) };
    let arg0: &mut [u8; 32] = unsafe { &mut *(arg0_raw as *mut [u8; 32]) };
    let mut Q: [u8; 200] = [0; 200];
    let mut T_lookup: [u8; 200] = [0; 200];
    let mut Q_plus: [u8; 200] = [0; 200];
    Q[(40u64) as usize] = (1u64) as u8;
    Q[(80u64) as usize] = (1u64) as u8;
    for i in 0u64..64u64 {
        let mut byte_idx: u64 = (i >> 1u64);
        let mut nibble_shift: u64 = ((i & 1u64).wrapping_mul(4u64));
        let scalar_byte: u64 = arg0[(byte_idx) as usize] as u64;
        let mut digit: u64 = ((scalar_byte >> nibble_shift) & 15u64);
        unsafe { comb_table_lookup(T_lookup.as_mut_ptr(), i, digit) };
        unsafe { xyzt_add_decomposed(Q_plus.as_mut_ptr(), Q.as_ptr(), T_lookup.as_ptr()) };
        { let _mask: u8 = (if (digit) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(Q.len() as usize) {
            Q[_i] = (Q_plus[_i] & _mask) | (Q[_i] & !_mask);
          } }
    };
    unsafe { xyzt_copy(out.as_mut_ptr(), Q.as_ptr()) };
}
