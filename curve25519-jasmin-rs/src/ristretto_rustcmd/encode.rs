// Generated from rust_cmd_ed.  Avoid editing directly.
// Verification: rust_cmd_ed -> functional simulation against
//   ristretto_encode_gallina_nlet (Ristretto_Encode_*.v).

#![allow(non_snake_case, unused_assignments, unused_mut, unused_variables, unused_parens, dead_code)]

unsafe extern "C" {
    // Field arithmetic (shared with Ed25519 / decode path).
    fn fe25519_mul(out: *mut u8, a: *const u8, b: *const u8);
    fn fe25519_add(out: *mut u8, a: *const u8, b: *const u8);
    fn fe25519_sub(out: *mut u8, a: *const u8, b: *const u8);
    fn fe25519_sq (out: *mut u8, a: *const u8);
    // Modular inverse z^(p-2) mod p (shared; provided by main leaves.rs).
    fn fe25519_inv(out: *mut u8, a: *const u8);
    // Ristretto leaves (shared with decode path).
    fn ristretto_pack_canonical_felem(out: *mut u8, s_in: *const u8);
    fn ristretto_sqrt_ratio_m1(ws_out: *mut u8, r_out: *mut u8, u_in: *const u8, v_in: *const u8);
    // Encode-specific input split (inverse of pack_xyzt5).
    fn unpack_xyzt5(x_out: *mut u8, y_out: *mut u8, z_out: *mut u8, ta_out: *mut u8, tb_out: *mut u8, xyzt_in: *const u8);
}

pub fn ristretto_encode(xyzt_var: &mut [u8; 200], out_var: &mut [u8; 32]) {
    let mut x_var: [u8; 32] = [0; 32];
    let mut y_var: [u8; 32] = [0; 32];
    let mut z_var: [u8; 32] = [0; 32];
    let mut ta_var: [u8; 32] = [0; 32];
    let mut tb_var: [u8; 32] = [0; 32];
    let mut one_var: [u8; 32] = [0; 32];
    let mut p_var: [u8; 32] = [0; 32];
    let mut sqrtm1_var: [u8; 32] = [0; 32];
    let mut invad_var: [u8; 32] = [0; 32];
    let mut zinv_var: [u8; 32] = [0; 32];
    let mut tatb_var: [u8; 32] = [0; 32];
    let mut t_var: [u8; 32] = [0; 32];
    let mut zpy_var: [u8; 32] = [0; 32];
    let mut zmy_var: [u8; 32] = [0; 32];
    let mut u1_var: [u8; 32] = [0; 32];
    let mut u2_var: [u8; 32] = [0; 32];
    let mut u2sq_var: [u8; 32] = [0; 32];
    let mut den_var: [u8; 32] = [0; 32];
    let mut ws_var: [u8; 1] = [0; 1];
    let mut invsqrt_var: [u8; 32] = [0; 32];
    let mut D1_var: [u8; 32] = [0; 32];
    let mut D2_var: [u8; 32] = [0; 32];
    let mut D1D2_var: [u8; 32] = [0; 32];
    let mut Zinv_var: [u8; 32] = [0; 32];
    let mut ix_var: [u8; 32] = [0; 32];
    let mut iy_var: [u8; 32] = [0; 32];
    let mut eden_var: [u8; 32] = [0; 32];
    let mut tZinv_var: [u8; 32] = [0; 32];
    let mut xp_var: [u8; 32] = [0; 32];
    let mut yp_var: [u8; 32] = [0; 32];
    let mut deninv_var: [u8; 32] = [0; 32];
    let mut xzinv_var: [u8; 32] = [0; 32];
    let mut ypneg_var: [u8; 32] = [0; 32];
    let mut ypp_var: [u8; 32] = [0; 32];
    let mut zmypp_var: [u8; 32] = [0; 32];
    let mut sraw_var: [u8; 32] = [0; 32];
    let mut sneg_var: [u8; 32] = [0; 32];
    let mut s_var: [u8; 32] = [0; 32];
    unsafe { unpack_xyzt5(x_var.as_mut_ptr(), y_var.as_mut_ptr(), z_var.as_mut_ptr(), ta_var.as_mut_ptr(), tb_var.as_mut_ptr(), xyzt_var.as_ptr()) };
    one_var.copy_from_slice(&[1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
    p_var.copy_from_slice(&[237u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 127u8]);
    sqrtm1_var.copy_from_slice(&[176u8, 160u8, 14u8, 74u8, 39u8, 27u8, 238u8, 196u8, 120u8, 228u8, 47u8, 173u8, 6u8, 24u8, 67u8, 47u8, 167u8, 215u8, 251u8, 61u8, 153u8, 0u8, 77u8, 43u8, 11u8, 223u8, 193u8, 79u8, 128u8, 36u8, 131u8, 43u8]);
    invad_var.copy_from_slice(&[234u8, 64u8, 93u8, 128u8, 170u8, 253u8, 200u8, 153u8, 190u8, 114u8, 65u8, 90u8, 23u8, 22u8, 47u8, 157u8, 64u8, 216u8, 1u8, 254u8, 145u8, 123u8, 194u8, 22u8, 162u8, 252u8, 175u8, 207u8, 5u8, 137u8, 108u8, 120u8]);
    unsafe { fe25519_inv(zinv_var.as_mut_ptr(), z_var.as_ptr()) };
    unsafe { fe25519_mul(tatb_var.as_mut_ptr(), ta_var.as_ptr(), tb_var.as_ptr()) };
    unsafe { fe25519_mul(t_var.as_mut_ptr(), tatb_var.as_ptr(), zinv_var.as_ptr()) };
    unsafe { fe25519_add(zpy_var.as_mut_ptr(), z_var.as_ptr(), y_var.as_ptr()) };
    unsafe { fe25519_sub(zmy_var.as_mut_ptr(), z_var.as_ptr(), y_var.as_ptr()) };
    unsafe { fe25519_mul(u1_var.as_mut_ptr(), zpy_var.as_ptr(), zmy_var.as_ptr()) };
    unsafe { fe25519_mul(u2_var.as_mut_ptr(), x_var.as_ptr(), y_var.as_ptr()) };
    unsafe { fe25519_sq(u2sq_var.as_mut_ptr(), u2_var.as_ptr()) };
    unsafe { fe25519_mul(den_var.as_mut_ptr(), u1_var.as_ptr(), u2sq_var.as_ptr()) };
    unsafe { ristretto_sqrt_ratio_m1(ws_var.as_mut_ptr(), invsqrt_var.as_mut_ptr(), one_var.as_ptr(), den_var.as_ptr()) };
    unsafe { fe25519_mul(D1_var.as_mut_ptr(), invsqrt_var.as_ptr(), u1_var.as_ptr()) };
    unsafe { fe25519_mul(D2_var.as_mut_ptr(), invsqrt_var.as_ptr(), u2_var.as_ptr()) };
    unsafe { fe25519_mul(D1D2_var.as_mut_ptr(), D1_var.as_ptr(), D2_var.as_ptr()) };
    unsafe { fe25519_mul(Zinv_var.as_mut_ptr(), D1D2_var.as_ptr(), t_var.as_ptr()) };
    unsafe { fe25519_mul(ix_var.as_mut_ptr(), x_var.as_ptr(), sqrtm1_var.as_ptr()) };
    unsafe { fe25519_mul(iy_var.as_mut_ptr(), y_var.as_ptr(), sqrtm1_var.as_ptr()) };
    unsafe { fe25519_mul(eden_var.as_mut_ptr(), D1_var.as_ptr(), invad_var.as_ptr()) };
    unsafe { fe25519_mul(tZinv_var.as_mut_ptr(), t_var.as_ptr(), Zinv_var.as_ptr()) };
    let rotbit_s: u64 = tZinv_var[(0u64) as usize] as u64;
    { let _mask: u8 = (if ((rotbit_s & 1u64)) != 0 { 0xffu8 } else { 0x00u8 });
      for _i in 0..(xp_var.len() as usize) {
        xp_var[_i] = (iy_var[_i] & _mask) | (x_var[_i] & !_mask);
      } };
    { let _mask: u8 = (if ((rotbit_s & 1u64)) != 0 { 0xffu8 } else { 0x00u8 });
      for _i in 0..(yp_var.len() as usize) {
        yp_var[_i] = (ix_var[_i] & _mask) | (y_var[_i] & !_mask);
      } };
    { let _mask: u8 = (if ((rotbit_s & 1u64)) != 0 { 0xffu8 } else { 0x00u8 });
      for _i in 0..(deninv_var.len() as usize) {
        deninv_var[_i] = (eden_var[_i] & _mask) | (D2_var[_i] & !_mask);
      } };
    unsafe { fe25519_mul(xzinv_var.as_mut_ptr(), xp_var.as_ptr(), Zinv_var.as_ptr()) };
    unsafe { fe25519_sub(ypneg_var.as_mut_ptr(), p_var.as_ptr(), yp_var.as_ptr()) };
    let xzbit_s: u64 = xzinv_var[(0u64) as usize] as u64;
    { let _mask: u8 = (if ((xzbit_s & 1u64)) != 0 { 0xffu8 } else { 0x00u8 });
      for _i in 0..(ypp_var.len() as usize) {
        ypp_var[_i] = (ypneg_var[_i] & _mask) | (yp_var[_i] & !_mask);
      } };
    unsafe { fe25519_sub(zmypp_var.as_mut_ptr(), z_var.as_ptr(), ypp_var.as_ptr()) };
    unsafe { fe25519_mul(sraw_var.as_mut_ptr(), deninv_var.as_ptr(), zmypp_var.as_ptr()) };
    unsafe { fe25519_sub(sneg_var.as_mut_ptr(), p_var.as_ptr(), sraw_var.as_ptr()) };
    let sbit_s: u64 = sraw_var[(0u64) as usize] as u64;
    { let _mask: u8 = (if ((sbit_s & 1u64)) != 0 { 0xffu8 } else { 0x00u8 });
      for _i in 0..(s_var.len() as usize) {
        s_var[_i] = (sneg_var[_i] & _mask) | (sraw_var[_i] & !_mask);
      } };
    unsafe { ristretto_pack_canonical_felem(out_var.as_mut_ptr(), s_var.as_ptr()) };
}
