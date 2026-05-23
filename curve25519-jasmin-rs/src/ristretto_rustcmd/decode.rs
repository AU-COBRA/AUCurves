// Generated from rust_cmd_ed.  Avoid editing directly.
// Verification: rust_cmd_ed -> safe_cmd_correct_ed (Qed) ->
//   to_bedrock_cmd_semantic_correct (Qed) -> bedrock2 fnspec.

#![allow(non_snake_case, unused_assignments, unused_mut, unused_variables, unused_parens, dead_code)]

unsafe extern "C" {
    // Field arithmetic (shared with Ed25519 path).
    fn fe25519_mul(out: *mut u8, a: *const u8, b: *const u8);
    fn fe25519_add(out: *mut u8, a: *const u8, b: *const u8);
    fn fe25519_sub(out: *mut u8, a: *const u8, b: *const u8);
    fn fe25519_sq (out: *mut u8, a: *const u8);
    // Ristretto-specific leaves.
    fn ristretto_parse_canonical_felem(s_out: *mut u8, status_out: *mut u8, bs_in: *const u8);
    fn ristretto_pack_canonical_felem(out: *mut u8, s_in: *const u8);
    fn ristretto_canonical_negate(out: *mut u8, s_in: *const u8);
    fn ristretto_sqrt_ratio_m1(ws_out: *mut u8, r_out: *mut u8, u_in: *const u8, v_in: *const u8);
    // Data-movement leaf (memmove-class).
    fn pack_xyzt5(out: *mut u8, x: *const u8, y: *const u8, z: *const u8, ta: *const u8, tb: *const u8);
}

pub fn ristretto_decode(bs_var: &mut [u8; 32], out_var: &mut [u8; 200]) {
    let mut yacc_s: u64 = 0;
    let mut s_var: [u8; 40] = [0; 40];
    let mut status_var: [u8; 1] = [0; 1];
    let mut one_var: [u8; 40] = [0; 40];
    let mut two_var: [u8; 40] = [0; 40];
    let mut d_var: [u8; 40] = [0; 40];
    let mut p_var: [u8; 40] = [0; 40];
    let mut ss_var: [u8; 40] = [0; 40];
    let mut u1_var: [u8; 40] = [0; 40];
    let mut u2_var: [u8; 40] = [0; 40];
    let mut u1_sq_var: [u8; 40] = [0; 40];
    let mut u2_sqr_var: [u8; 40] = [0; 40];
    let mut d_u1sq_var: [u8; 40] = [0; 40];
    let mut neg_du1sq_var: [u8; 40] = [0; 40];
    let mut v_var: [u8; 40] = [0; 40];
    let mut den_var: [u8; 40] = [0; 40];
    let mut ws_var: [u8; 1] = [0; 1];
    let mut I_var: [u8; 40] = [0; 40];
    let mut Dx_var: [u8; 40] = [0; 40];
    let mut IDx_var: [u8; 40] = [0; 40];
    let mut Dy_var: [u8; 40] = [0; 40];
    let mut s2_var: [u8; 40] = [0; 40];
    let mut x_raw_var: [u8; 40] = [0; 40];
    let mut x_neg_var: [u8; 40] = [0; 40];
    let mut x_var: [u8; 40] = [0; 40];
    let mut y_var: [u8; 40] = [0; 40];
    let mut t_var: [u8; 40] = [0; 40];
    unsafe { ristretto_parse_canonical_felem(s_var.as_mut_ptr(), status_var.as_mut_ptr(), bs_var.as_ptr()) };
    let statusb_s: u64 = status_var[(0u64) as usize] as u64;
    if (statusb_s) != 0 {
        out_var.copy_from_slice(&[0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8])
    } else {
        one_var.copy_from_slice(&[1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
        two_var.copy_from_slice(&[2u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
        p_var.copy_from_slice(&[237u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8, 127u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
        d_var.copy_from_slice(&[163u8, 120u8, 89u8, 19u8, 202u8, 77u8, 235u8, 117u8, 171u8, 216u8, 65u8, 65u8, 77u8, 10u8, 112u8, 0u8, 152u8, 232u8, 121u8, 119u8, 121u8, 64u8, 199u8, 140u8, 115u8, 254u8, 111u8, 43u8, 238u8, 108u8, 3u8, 82u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
        unsafe { fe25519_sq(ss_var.as_mut_ptr(), s_var.as_ptr()) };
        unsafe { fe25519_sub(u1_var.as_mut_ptr(), one_var.as_ptr(), ss_var.as_ptr()) };
        unsafe { fe25519_add(u2_var.as_mut_ptr(), one_var.as_ptr(), ss_var.as_ptr()) };
        unsafe { fe25519_sq(u2_sqr_var.as_mut_ptr(), u2_var.as_ptr()) };
        unsafe { fe25519_sq(u1_sq_var.as_mut_ptr(), u1_var.as_ptr()) };
        unsafe { fe25519_mul(d_u1sq_var.as_mut_ptr(), d_var.as_ptr(), u1_sq_var.as_ptr()) };
        unsafe { fe25519_sub(neg_du1sq_var.as_mut_ptr(), p_var.as_ptr(), d_u1sq_var.as_ptr()) };
        unsafe { fe25519_sub(v_var.as_mut_ptr(), neg_du1sq_var.as_ptr(), u2_sqr_var.as_ptr()) };
        unsafe { fe25519_mul(den_var.as_mut_ptr(), v_var.as_ptr(), u2_sqr_var.as_ptr()) };
        unsafe { ristretto_sqrt_ratio_m1(ws_var.as_mut_ptr(), I_var.as_mut_ptr(), one_var.as_ptr(), den_var.as_ptr()) };
        unsafe { fe25519_mul(Dx_var.as_mut_ptr(), I_var.as_ptr(), u2_var.as_ptr()) };
        unsafe { fe25519_mul(IDx_var.as_mut_ptr(), I_var.as_ptr(), Dx_var.as_ptr()) };
        unsafe { fe25519_mul(Dy_var.as_mut_ptr(), IDx_var.as_ptr(), v_var.as_ptr()) };
        unsafe { fe25519_mul(s2_var.as_mut_ptr(), two_var.as_ptr(), s_var.as_ptr()) };
        unsafe { fe25519_mul(x_raw_var.as_mut_ptr(), s2_var.as_ptr(), Dx_var.as_ptr()) };
        unsafe { fe25519_sub(x_neg_var.as_mut_ptr(), p_var.as_ptr(), x_raw_var.as_ptr()) };
        let xbit_s: u64 = x_raw_var[(0u64) as usize] as u64;
        { let _mask: u8 = (if ((xbit_s & 1u64)) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(x_var.len() as usize) {
            x_var[_i] = (x_neg_var[_i] & _mask) | (x_raw_var[_i] & !_mask);
          } };
        unsafe { fe25519_mul(y_var.as_mut_ptr(), Dy_var.as_ptr(), u1_var.as_ptr()) };
        unsafe { fe25519_mul(t_var.as_mut_ptr(), x_var.as_ptr(), y_var.as_ptr()) };
        let wsb_s: u64 = ws_var[(0u64) as usize] as u64;
        if (wsb_s) != 0 {
            let tbit_s: u64 = t_var[(0u64) as usize] as u64;
            if ((tbit_s & 1u64)) != 0 {
                out_var.copy_from_slice(&[0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8])
            } else {
                yacc_s = 0u64;
                for yloop_s in 0u64..32u64 {
                    let ybyte_s: u64 = y_var[(yloop_s) as usize] as u64;
                    yacc_s = (yacc_s.wrapping_add(ybyte_s))
                };
                if (yacc_s) != 0 {
                    unsafe { pack_xyzt5(out_var.as_mut_ptr(), x_var.as_ptr(), y_var.as_ptr(), one_var.as_ptr(), x_var.as_ptr(), y_var.as_ptr()) }
                } else {
                    out_var.copy_from_slice(&[0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8])
                }
            }
        } else {
            out_var.copy_from_slice(&[0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8])
        }
    };
}