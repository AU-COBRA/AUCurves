// Generated from rust_cmd_ed.  Avoid editing directly.
// Verification: rust_cmd_ed → safe_cmd_correct_ed (Qed) →
//   to_bedrock_cmd_semantic_correct (Qed) → bedrock2 fnspec.
//
// FFI centralization (status doc §6.3, Phase B) — EXEMPT.
// IR-emitted body: unsafe blocks are mechanical FFI dispatch to
// the leaf symbols, and will collapse to safe wrappers in
// `crate::ffi_safe` once the emitter is updated.

#![allow(non_snake_case, unused_assignments, unused_mut, unused_variables, unused_parens, dead_code)]

unsafe extern "C" {
    fn sha512_64(out: *mut u8, msg: *const u8, len: u64);
    fn scalar_reduce(out: *mut u8, full: *const u8);
    fn scalar_muladd(out: *mut u8, r: *const u8, k: *const u8, a: *const u8);
    fn ed25519_compress(out: *mut u8, xyzt: *const u8);
    fn ed25519_decompress_R(out: *mut u8, sig: *const u8);
    fn ed25519_decompress_A(out: *mut u8, pk: *const u8);
    fn ed25519_scalarmult_base(out: *mut u8, scalar: *const u8);
    fn ed25519_scalarmult(out: *mut u8, scalar: *const u8, point: *const u8);
    fn ed25519_xyzt_add(out: *mut u8, p: *const u8, q: *const u8);
    fn scalar_lt_L(out: *mut u8, scalar: *const u8);
    fn bytes_equal_32(out: *mut u8, a: *const u8, b: *const u8);
    fn verify_fail(out: *mut u8);
    fn clamp_64(sk: *mut u8);
    // Region-copy helpers (slice memmoves at fixed offsets);
    // emitted by rust_cmd_ed for byte-region transfers.
    fn memmove_a_from_h(out: *mut u8, h: *const u8);
    fn memmove_prefix_from_h(out: *mut u8, h: *const u8);
    fn memmove_nonce_prefix(buf: *mut u8, prefix: *const u8);
    fn memmove_nonce_msg(buf: *mut u8, msg: *const u8);
    fn memmove_chal_R(buf: *mut u8, R: *const u8);
    fn memmove_chal_A(buf: *mut u8, A: *const u8);
    fn memmove_chal_M(buf: *mut u8, M: *const u8);
    fn memmove_sig_R(sig: *mut u8, R: *const u8);
    fn memmove_R_from_sig(R: *mut u8, sig: *const u8);
    fn memmove_S_from_sig(S: *mut u8, sig: *const u8);
}

pub fn ed25519_verify(result_out: &mut [u8; 1], sig_in: &mut [u8; 64], r#pub: &mut [u8; 32], msg: &mut [u8; 4096], msg_len: u64) {
    let mut R_xyzt_v: [u8; 200] = [0; 200];
    let mut A_xyzt_v: [u8; 200] = [0; 200];
    let mut h_v: [u8; 64] = [0; 64];
    let mut h_red: [u8; 32] = [0; 32];
    let mut sB: [u8; 200] = [0; 200];
    let mut hA: [u8; 200] = [0; 200];
    let mut RcheckA: [u8; 200] = [0; 200];
    let mut check_bytes: [u8; 32] = [0; 32];
    let mut R_bytes_v: [u8; 32] = [0; 32];
    let mut chal_buf_v: [u8; 4160] = [0; 4160];
    let mut S_bytes: [u8; 32] = [0; 32];
    let mut check_sB_bytes: [u8; 32] = [0; 32];
    unsafe { scalar_lt_L(result_out.as_mut_ptr(), sig_in.as_ptr()) };
    unsafe { ed25519_decompress_R(R_xyzt_v.as_mut_ptr(), sig_in.as_ptr()) };
    unsafe { ed25519_decompress_A(A_xyzt_v.as_mut_ptr(), r#pub.as_ptr()) };
    unsafe { memmove_R_from_sig(R_bytes_v.as_mut_ptr(), sig_in.as_ptr()) };
    unsafe { memmove_chal_R(chal_buf_v.as_mut_ptr(), R_bytes_v.as_ptr()) };
    unsafe { memmove_chal_A(chal_buf_v.as_mut_ptr(), r#pub.as_ptr()) };
    unsafe { memmove_chal_M(chal_buf_v.as_mut_ptr(), msg.as_ptr()) };
    let mut verify_chal_len: u64 = (64u64.wrapping_add(msg_len));
    unsafe { sha512_64(h_v.as_mut_ptr(), chal_buf_v.as_ptr(), verify_chal_len) };
    unsafe { scalar_reduce(h_red.as_mut_ptr(), h_v.as_ptr()) };
    unsafe { memmove_S_from_sig(S_bytes.as_mut_ptr(), sig_in.as_ptr()) };
    unsafe { ed25519_scalarmult_base(sB.as_mut_ptr(), S_bytes.as_ptr()) };
    unsafe { ed25519_scalarmult(hA.as_mut_ptr(), h_red.as_ptr(), A_xyzt_v.as_ptr()) };
    unsafe { ed25519_xyzt_add(RcheckA.as_mut_ptr(), R_xyzt_v.as_ptr(), hA.as_ptr()) };
    unsafe { ed25519_compress(check_bytes.as_mut_ptr(), RcheckA.as_ptr()) };
    unsafe { ed25519_compress(check_sB_bytes.as_mut_ptr(), sB.as_ptr()) };
    unsafe { bytes_equal_32(result_out.as_mut_ptr(), check_sB_bytes.as_ptr(), check_bytes.as_ptr()) };
}
