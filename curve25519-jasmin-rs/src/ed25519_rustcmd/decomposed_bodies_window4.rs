//! Auto-extracted scalarmult bodies — sourced from AUCurves's
//! Window4ScalarmultBody.v, Straus2MSMBody.v, WnafScalarmultBody.v
//! via Bedrock/ExtractWindow4Body.v.
//!
//! **FFI centralization (status doc §6.3, Phase B) — EXEMPT.**
//! Mechanically IR-emitted; unsafe blocks are FFI dispatch and will
//! collapse when the emitter targets `ffi_safe::*` directly.
//!
//! - window4_scalarmult: unsigned window-4 (Phase 1a-revised)
//! - straus_2msm:        2-MSM, extracted but not wired (Phase 6 finding)
//! - wnaf_scalarmult_signed: signed wnaf-5 with xyzt_cond_negate (Phase 1a)

#![cfg(all(feature = "wnaf_comb_leaves",
           not(feature = "decomposed_leaves"),
           not(feature = "inline_leaves"),
           not(feature = "dalek_leaves")))]
// Auto-extracted body: see header note in decomposed_bodies_wnaf_comb.rs.
// `clippy::eq_op` is intentionally allowed for extractor-emitted constant
// comparisons like `(0u64) != 0`.
#![allow(non_snake_case, unused_assignments, unused_mut, unused_variables, unused_parens, dead_code, clippy::eq_op)]

unsafe extern "C" {
    fn xyzt_add_decomposed(out: *mut u8, a: *const u8, b: *const u8);
    fn xyzt_double_decomposed(out: *mut u8, a: *const u8);
    fn xyzt_copy(out: *mut u8, src: *const u8);
    fn xyzt_cond_negate(out: *mut u8, src: *const u8, sign: u64);
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn window4_scalarmult(out_raw: *mut u8, arg0_raw: *const u8, arg1_raw: *const u8) {
    let out: &mut [u8; 200] = unsafe { &mut *(out_raw as *mut [u8; 200]) };
    let arg0: &mut [u8; 32] = unsafe { &mut *(arg0_raw as *mut [u8; 32]) };
    let arg1: &mut [u8; 200] = unsafe { &mut *(arg1_raw as *mut [u8; 200]) };
    let mut T0: [u8; 200] = [0; 200];
    let mut T1: [u8; 200] = [0; 200];
    let mut T2: [u8; 200] = [0; 200];
    let mut T3: [u8; 200] = [0; 200];
    let mut T4: [u8; 200] = [0; 200];
    let mut T5: [u8; 200] = [0; 200];
    let mut T6: [u8; 200] = [0; 200];
    let mut T7: [u8; 200] = [0; 200];
    let mut T8: [u8; 200] = [0; 200];
    let mut T9: [u8; 200] = [0; 200];
    let mut T10: [u8; 200] = [0; 200];
    let mut T11: [u8; 200] = [0; 200];
    let mut T12: [u8; 200] = [0; 200];
    let mut T13: [u8; 200] = [0; 200];
    let mut T14: [u8; 200] = [0; 200];
    let mut T15: [u8; 200] = [0; 200];
    let mut Q: [u8; 200] = [0; 200];
    let mut lookup_buf: [u8; 200] = [0; 200];
    let mut Q_plus: [u8; 200] = [0; 200];
    T0[(40u64) as usize] = (1u64) as u8;
    T0[(80u64) as usize] = (1u64) as u8;
    T0[(160u64) as usize] = (1u64) as u8;
    unsafe { xyzt_copy(T1.as_mut_ptr(), arg1.as_ptr()) };
    unsafe { xyzt_add_decomposed(T2.as_mut_ptr(), T1.as_ptr(), arg1.as_ptr()) };
    unsafe { xyzt_add_decomposed(T3.as_mut_ptr(), T2.as_ptr(), arg1.as_ptr()) };
    unsafe { xyzt_add_decomposed(T4.as_mut_ptr(), T3.as_ptr(), arg1.as_ptr()) };
    unsafe { xyzt_add_decomposed(T5.as_mut_ptr(), T4.as_ptr(), arg1.as_ptr()) };
    unsafe { xyzt_add_decomposed(T6.as_mut_ptr(), T5.as_ptr(), arg1.as_ptr()) };
    unsafe { xyzt_add_decomposed(T7.as_mut_ptr(), T6.as_ptr(), arg1.as_ptr()) };
    unsafe { xyzt_add_decomposed(T8.as_mut_ptr(), T7.as_ptr(), arg1.as_ptr()) };
    unsafe { xyzt_add_decomposed(T9.as_mut_ptr(), T8.as_ptr(), arg1.as_ptr()) };
    unsafe { xyzt_add_decomposed(T10.as_mut_ptr(), T9.as_ptr(), arg1.as_ptr()) };
    unsafe { xyzt_add_decomposed(T11.as_mut_ptr(), T10.as_ptr(), arg1.as_ptr()) };
    unsafe { xyzt_add_decomposed(T12.as_mut_ptr(), T11.as_ptr(), arg1.as_ptr()) };
    unsafe { xyzt_add_decomposed(T13.as_mut_ptr(), T12.as_ptr(), arg1.as_ptr()) };
    unsafe { xyzt_add_decomposed(T14.as_mut_ptr(), T13.as_ptr(), arg1.as_ptr()) };
    unsafe { xyzt_add_decomposed(T15.as_mut_ptr(), T14.as_ptr(), arg1.as_ptr()) };
    Q[(40u64) as usize] = (1u64) as u8;
    Q[(80u64) as usize] = (1u64) as u8;
    Q[(160u64) as usize] = (1u64) as u8;
    for i in 0u64..64u64 {
        let mut d: u64 = (63u64.wrapping_sub(i));
        let mut byte_idx: u64 = (d >> 1u64);
        let mut nibble_shift: u64 = ((d & 1u64).wrapping_mul(4u64));
        let scalar_byte: u64 = arg0[(byte_idx) as usize] as u64;
        let mut digit: u64 = ((scalar_byte >> nibble_shift) & 15u64);
        unsafe { xyzt_double_decomposed(Q.as_mut_ptr(), Q.as_ptr()) };
        unsafe { xyzt_double_decomposed(Q.as_mut_ptr(), Q.as_ptr()) };
        unsafe { xyzt_double_decomposed(Q.as_mut_ptr(), Q.as_ptr()) };
        unsafe { xyzt_double_decomposed(Q.as_mut_ptr(), Q.as_ptr()) };
        { let _mask: u8 = (if (0u64) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (T0[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit.wrapping_sub(1u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (T1[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit.wrapping_sub(2u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (T2[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit.wrapping_sub(3u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (T3[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit.wrapping_sub(4u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (T4[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit.wrapping_sub(5u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (T5[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit.wrapping_sub(6u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (T6[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit.wrapping_sub(7u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (T7[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit.wrapping_sub(8u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (T8[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit.wrapping_sub(9u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (T9[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit.wrapping_sub(10u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (T10[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit.wrapping_sub(11u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (T11[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit.wrapping_sub(12u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (T12[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit.wrapping_sub(13u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (T13[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit.wrapping_sub(14u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (T14[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit.wrapping_sub(15u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (T15[_i] & !_mask);
          } };
        unsafe { xyzt_add_decomposed(Q_plus.as_mut_ptr(), Q.as_ptr(), lookup_buf.as_ptr()) };
        { let _mask: u8 = (if (1u64) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(Q.len() as usize) {
            Q[_i] = (Q_plus[_i] & _mask) | (Q[_i] & !_mask);
          } }
    };
    unsafe { xyzt_copy(out.as_mut_ptr(), Q.as_ptr()) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn straus_2msm(out_raw: *mut u8, arg0_raw: *const u8, arg1_raw: *const u8, arg2_raw: *const u8, arg3_raw: *const u8) {
    let out: &mut [u8; 200] = unsafe { &mut *(out_raw as *mut [u8; 200]) };
    let arg0: &mut [u8; 32] = unsafe { &mut *(arg0_raw as *mut [u8; 32]) };
    let arg1: &mut [u8; 32] = unsafe { &mut *(arg1_raw as *mut [u8; 32]) };
    let arg2: &mut [u8; 200] = unsafe { &mut *(arg2_raw as *mut [u8; 200]) };
    let arg3: &mut [u8; 200] = unsafe { &mut *(arg3_raw as *mut [u8; 200]) };
    let mut TB0: [u8; 200] = [0; 200];
    let mut TB1: [u8; 200] = [0; 200];
    let mut TB2: [u8; 200] = [0; 200];
    let mut TB3: [u8; 200] = [0; 200];
    let mut TB4: [u8; 200] = [0; 200];
    let mut TB5: [u8; 200] = [0; 200];
    let mut TB6: [u8; 200] = [0; 200];
    let mut TB7: [u8; 200] = [0; 200];
    let mut TB8: [u8; 200] = [0; 200];
    let mut TB9: [u8; 200] = [0; 200];
    let mut TB10: [u8; 200] = [0; 200];
    let mut TB11: [u8; 200] = [0; 200];
    let mut TB12: [u8; 200] = [0; 200];
    let mut TB13: [u8; 200] = [0; 200];
    let mut TB14: [u8; 200] = [0; 200];
    let mut TB15: [u8; 200] = [0; 200];
    let mut TA0: [u8; 200] = [0; 200];
    let mut TA1: [u8; 200] = [0; 200];
    let mut TA2: [u8; 200] = [0; 200];
    let mut TA3: [u8; 200] = [0; 200];
    let mut TA4: [u8; 200] = [0; 200];
    let mut TA5: [u8; 200] = [0; 200];
    let mut TA6: [u8; 200] = [0; 200];
    let mut TA7: [u8; 200] = [0; 200];
    let mut TA8: [u8; 200] = [0; 200];
    let mut TA9: [u8; 200] = [0; 200];
    let mut TA10: [u8; 200] = [0; 200];
    let mut TA11: [u8; 200] = [0; 200];
    let mut TA12: [u8; 200] = [0; 200];
    let mut TA13: [u8; 200] = [0; 200];
    let mut TA14: [u8; 200] = [0; 200];
    let mut TA15: [u8; 200] = [0; 200];
    let mut Q: [u8; 200] = [0; 200];
    let mut lookup_buf: [u8; 200] = [0; 200];
    let mut Q_plus: [u8; 200] = [0; 200];
    TB0[(40u64) as usize] = (1u64) as u8;
    TB0[(80u64) as usize] = (1u64) as u8;
    TB0[(160u64) as usize] = (1u64) as u8;
    TA0[(40u64) as usize] = (1u64) as u8;
    TA0[(80u64) as usize] = (1u64) as u8;
    TA0[(160u64) as usize] = (1u64) as u8;
    Q[(40u64) as usize] = (1u64) as u8;
    Q[(80u64) as usize] = (1u64) as u8;
    Q[(160u64) as usize] = (1u64) as u8;
    unsafe { xyzt_copy(TB1.as_mut_ptr(), arg2.as_ptr()) };
    unsafe { xyzt_add_decomposed(TB2.as_mut_ptr(), TB1.as_ptr(), arg2.as_ptr()) };
    unsafe { xyzt_add_decomposed(TB3.as_mut_ptr(), TB2.as_ptr(), arg2.as_ptr()) };
    unsafe { xyzt_add_decomposed(TB4.as_mut_ptr(), TB3.as_ptr(), arg2.as_ptr()) };
    unsafe { xyzt_add_decomposed(TB5.as_mut_ptr(), TB4.as_ptr(), arg2.as_ptr()) };
    unsafe { xyzt_add_decomposed(TB6.as_mut_ptr(), TB5.as_ptr(), arg2.as_ptr()) };
    unsafe { xyzt_add_decomposed(TB7.as_mut_ptr(), TB6.as_ptr(), arg2.as_ptr()) };
    unsafe { xyzt_add_decomposed(TB8.as_mut_ptr(), TB7.as_ptr(), arg2.as_ptr()) };
    unsafe { xyzt_add_decomposed(TB9.as_mut_ptr(), TB8.as_ptr(), arg2.as_ptr()) };
    unsafe { xyzt_add_decomposed(TB10.as_mut_ptr(), TB9.as_ptr(), arg2.as_ptr()) };
    unsafe { xyzt_add_decomposed(TB11.as_mut_ptr(), TB10.as_ptr(), arg2.as_ptr()) };
    unsafe { xyzt_add_decomposed(TB12.as_mut_ptr(), TB11.as_ptr(), arg2.as_ptr()) };
    unsafe { xyzt_add_decomposed(TB13.as_mut_ptr(), TB12.as_ptr(), arg2.as_ptr()) };
    unsafe { xyzt_add_decomposed(TB14.as_mut_ptr(), TB13.as_ptr(), arg2.as_ptr()) };
    unsafe { xyzt_add_decomposed(TB15.as_mut_ptr(), TB14.as_ptr(), arg2.as_ptr()) };
    unsafe { xyzt_copy(TA1.as_mut_ptr(), arg3.as_ptr()) };
    unsafe { xyzt_add_decomposed(TA2.as_mut_ptr(), TA1.as_ptr(), arg3.as_ptr()) };
    unsafe { xyzt_add_decomposed(TA3.as_mut_ptr(), TA2.as_ptr(), arg3.as_ptr()) };
    unsafe { xyzt_add_decomposed(TA4.as_mut_ptr(), TA3.as_ptr(), arg3.as_ptr()) };
    unsafe { xyzt_add_decomposed(TA5.as_mut_ptr(), TA4.as_ptr(), arg3.as_ptr()) };
    unsafe { xyzt_add_decomposed(TA6.as_mut_ptr(), TA5.as_ptr(), arg3.as_ptr()) };
    unsafe { xyzt_add_decomposed(TA7.as_mut_ptr(), TA6.as_ptr(), arg3.as_ptr()) };
    unsafe { xyzt_add_decomposed(TA8.as_mut_ptr(), TA7.as_ptr(), arg3.as_ptr()) };
    unsafe { xyzt_add_decomposed(TA9.as_mut_ptr(), TA8.as_ptr(), arg3.as_ptr()) };
    unsafe { xyzt_add_decomposed(TA10.as_mut_ptr(), TA9.as_ptr(), arg3.as_ptr()) };
    unsafe { xyzt_add_decomposed(TA11.as_mut_ptr(), TA10.as_ptr(), arg3.as_ptr()) };
    unsafe { xyzt_add_decomposed(TA12.as_mut_ptr(), TA11.as_ptr(), arg3.as_ptr()) };
    unsafe { xyzt_add_decomposed(TA13.as_mut_ptr(), TA12.as_ptr(), arg3.as_ptr()) };
    unsafe { xyzt_add_decomposed(TA14.as_mut_ptr(), TA13.as_ptr(), arg3.as_ptr()) };
    unsafe { xyzt_add_decomposed(TA15.as_mut_ptr(), TA14.as_ptr(), arg3.as_ptr()) };
    for i in 0u64..64u64 {
        let mut d: u64 = (63u64.wrapping_sub(i));
        let mut byte_idx: u64 = (d >> 1u64);
        let mut nibble_shift: u64 = ((d & 1u64).wrapping_mul(4u64));
        let scalar_byte_s: u64 = arg0[(byte_idx) as usize] as u64;
        let scalar_byte_k: u64 = arg1[(byte_idx) as usize] as u64;
        let mut digit_s: u64 = ((scalar_byte_s >> nibble_shift) & 15u64);
        let mut digit_k: u64 = ((scalar_byte_k >> nibble_shift) & 15u64);
        unsafe { xyzt_double_decomposed(Q.as_mut_ptr(), Q.as_ptr()) };
        unsafe { xyzt_double_decomposed(Q.as_mut_ptr(), Q.as_ptr()) };
        unsafe { xyzt_double_decomposed(Q.as_mut_ptr(), Q.as_ptr()) };
        unsafe { xyzt_double_decomposed(Q.as_mut_ptr(), Q.as_ptr()) };
        { let _mask: u8 = (if (0u64) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (TB0[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit_s.wrapping_sub(1u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (TB1[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit_s.wrapping_sub(2u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (TB2[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit_s.wrapping_sub(3u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (TB3[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit_s.wrapping_sub(4u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (TB4[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit_s.wrapping_sub(5u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (TB5[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit_s.wrapping_sub(6u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (TB6[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit_s.wrapping_sub(7u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (TB7[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit_s.wrapping_sub(8u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (TB8[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit_s.wrapping_sub(9u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (TB9[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit_s.wrapping_sub(10u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (TB10[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit_s.wrapping_sub(11u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (TB11[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit_s.wrapping_sub(12u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (TB12[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit_s.wrapping_sub(13u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (TB13[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit_s.wrapping_sub(14u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (TB14[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit_s.wrapping_sub(15u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (TB15[_i] & !_mask);
          } };
        unsafe { xyzt_add_decomposed(Q_plus.as_mut_ptr(), Q.as_ptr(), lookup_buf.as_ptr()) };
        { let _mask: u8 = (if (1u64) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(Q.len() as usize) {
            Q[_i] = (Q_plus[_i] & _mask) | (Q[_i] & !_mask);
          } };
        { let _mask: u8 = (if (0u64) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (TA0[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit_k.wrapping_sub(1u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (TA1[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit_k.wrapping_sub(2u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (TA2[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit_k.wrapping_sub(3u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (TA3[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit_k.wrapping_sub(4u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (TA4[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit_k.wrapping_sub(5u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (TA5[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit_k.wrapping_sub(6u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (TA6[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit_k.wrapping_sub(7u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (TA7[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit_k.wrapping_sub(8u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (TA8[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit_k.wrapping_sub(9u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (TA9[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit_k.wrapping_sub(10u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (TA10[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit_k.wrapping_sub(11u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (TA11[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit_k.wrapping_sub(12u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (TA12[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit_k.wrapping_sub(13u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (TA13[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit_k.wrapping_sub(14u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (TA14[_i] & !_mask);
          } };
        { let _mask: u8 = (if ((digit_k.wrapping_sub(15u64))) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(lookup_buf.len() as usize) {
            lookup_buf[_i] = (lookup_buf[_i] & _mask) | (TA15[_i] & !_mask);
          } };
        unsafe { xyzt_add_decomposed(Q_plus.as_mut_ptr(), Q.as_ptr(), lookup_buf.as_ptr()) };
        { let _mask: u8 = (if (1u64) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(Q.len() as usize) {
            Q[_i] = (Q_plus[_i] & _mask) | (Q[_i] & !_mask);
          } }
    };
    unsafe { xyzt_copy(out.as_mut_ptr(), Q.as_ptr()) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wnaf_scalarmult_signed(out_raw: *mut u8, arg0_raw: *const u8, arg1_raw: *const u8) {
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
        let mut sign: u64 = (digit_byte >> 7u64);
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
        unsafe { xyzt_cond_negate(lookup_buf.as_mut_ptr(), lookup_buf.as_ptr(), sign) };
        unsafe { xyzt_add_decomposed(Q_plus.as_mut_ptr(), Q.as_ptr(), lookup_buf.as_ptr()) };
        { let _mask: u8 = (if (is_nonzero) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(Q.len() as usize) {
            Q[_i] = (Q_plus[_i] & _mask) | (Q[_i] & !_mask);
          } }
    };
    unsafe { xyzt_copy(out.as_mut_ptr(), Q.as_ptr()) };
}
