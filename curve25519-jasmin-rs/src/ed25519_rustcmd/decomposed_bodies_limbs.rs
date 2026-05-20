//! Limb-typed `xyzt_{add,double}_decomposed` — auto-extracted from
//! AUCurves's retyped XyztAdd/Double BodyDecomposed.v (TBytes 40 →
//! TFp25519 retype, 2026-05-12) via `Bedrock/ExtractCurveBodies.v`.
//!
//! **FFI centralization (status doc §6.3, Phase B) — EXEMPT.**
//! Mechanically IR-emitted; unsafe blocks are FFI dispatch and will
//! collapse when the emitter targets `ffi_safe::*` directly.
//!
//! Source AST (verified, modulo the same `Admitted` correctness
//! theorem as the byte-typed version):
//!
//!   - `AUCurves/src/Bedrock/End2End/Ed25519/XyztAddBodyDecomposed.v`
//!   - `AUCurves/src/Bedrock/End2End/Ed25519/XyztDoubleBodyDecomposed.v`
//!
//! Verified extraction artefact lives at
//!   `AUCurves/_build/default/curve_bodies_rs.out`
//!
//! ## Slot ABI
//!
//! The body declares each intermediate as `[u64; 5]` (the Rust mapping
//! of `TFp25519` per `RustCmdToRust.v` §1) and passes pointers to
//! `fe25519_*` callees via `as_mut_ptr()` / `as_ptr()` → `*mut u64` /
//! `*const u64`.  Under `feature = "tfp25519_limbs"`, those symbols
//! resolve to `fe25519_limbs.rs`'s `extern "C"` exports — direct
//! `fiat_25519_carry_mul` on 5×u64 tight slots with no per-op
//! byte↔limb conversion.
//!
//! The 200-byte XYZT point slot is read/written via `fe25519_unpack/
//! pack_xyzt5` in `fe25519_portable.rs` (memcpy of 5 × 40 bytes).
//! Combined with `feature = "xyzt_limb_abi"`, those 40-byte chunks
//! are LE u64 limbs, so the unpack/pack are byte-identical to
//! reading the slot as `5 × [u64; 5]` — zero conversion at the
//! protocol-body boundary.

#![cfg(feature = "tfp25519_limbs")]
#![allow(non_snake_case, unused_assignments, unused_mut, unused_variables, unused_parens, dead_code)]

unsafe extern "C" {
    fn fe25519_add(out: *mut u64, a: *const u64, b: *const u64);
    fn fe25519_sub(out: *mut u64, a: *const u64, b: *const u64);
    fn fe25519_mul(out: *mut u64, a: *const u64, b: *const u64);
    fn fe25519_sqr(out: *mut u64, a: *const u64);
    fn fe25519_mul_2(out: *mut u64, a: *const u64);
    fn fe25519_mul_d2(out: *mut u64, a: *const u64);
    fn fe25519_sqr_scale2(out: *mut u64, a: *const u64);
    fn fe25519_sqr_sub2(out: *mut u64, a: *const u64, b: *const u64, c: *const u64);
    fn fe25519_neg_add(out: *mut u64, a: *const u64, b: *const u64);
    fn fe25519_unpack_xyzt5(x: *mut u64, y: *mut u64, z: *mut u64,
                            ta: *mut u64, tb: *mut u64, p: *const u8);
    fn fe25519_pack_xyzt5(out: *mut u8, x: *const u64, y: *const u64,
                          z: *const u64, ta: *const u64, tb: *const u64);
}

#[cfg(not(feature = "tfp25519_inline_limbs"))]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn xyzt_add_decomposed(out_raw: *mut u8, arg0_raw: *const u8, arg1_raw: *const u8) {
    let out: &mut [u8; 200] = unsafe { &mut *(out_raw as *mut [u8; 200]) };
    let arg0: &mut [u8; 200] = unsafe { &mut *(arg0_raw as *mut [u8; 200]) };
    let arg1: &mut [u8; 200] = unsafe { &mut *(arg1_raw as *mut [u8; 200]) };
    let mut X1: [u64; 5] = [0; 5];
    let mut Y1: [u64; 5] = [0; 5];
    let mut Z1: [u64; 5] = [0; 5];
    let mut Ta1: [u64; 5] = [0; 5];
    let mut Tb1: [u64; 5] = [0; 5];
    let mut X2: [u64; 5] = [0; 5];
    let mut Y2: [u64; 5] = [0; 5];
    let mut Z2: [u64; 5] = [0; 5];
    let mut Ta2: [u64; 5] = [0; 5];
    let mut Tb2: [u64; 5] = [0; 5];
    let mut T1: [u64; 5] = [0; 5];
    let mut T2: [u64; 5] = [0; 5];
    let mut A: [u64; 5] = [0; 5];
    let mut B: [u64; 5] = [0; 5];
    let mut C: [u64; 5] = [0; 5];
    let mut D: [u64; 5] = [0; 5];
    let mut E: [u64; 5] = [0; 5];
    let mut F: [u64; 5] = [0; 5];
    let mut G: [u64; 5] = [0; 5];
    let mut H: [u64; 5] = [0; 5];
    let mut X3: [u64; 5] = [0; 5];
    let mut Y3: [u64; 5] = [0; 5];
    let mut Z3: [u64; 5] = [0; 5];
    unsafe { fe25519_unpack_xyzt5(X1.as_mut_ptr(), Y1.as_mut_ptr(), Z1.as_mut_ptr(), Ta1.as_mut_ptr(), Tb1.as_mut_ptr(), arg0.as_ptr()) };
    unsafe { fe25519_unpack_xyzt5(X2.as_mut_ptr(), Y2.as_mut_ptr(), Z2.as_mut_ptr(), Ta2.as_mut_ptr(), Tb2.as_mut_ptr(), arg1.as_ptr()) };
    unsafe { fe25519_mul(T1.as_mut_ptr(), Ta1.as_ptr(), Tb1.as_ptr()) };
    unsafe { fe25519_mul(T2.as_mut_ptr(), Ta2.as_ptr(), Tb2.as_ptr()) };
    unsafe { fe25519_sub(Y3.as_mut_ptr(), Y1.as_ptr(), X1.as_ptr()) };
    unsafe { fe25519_sub(Z3.as_mut_ptr(), Y2.as_ptr(), X2.as_ptr()) };
    unsafe { fe25519_mul(A.as_mut_ptr(), Y3.as_ptr(), Z3.as_ptr()) };
    unsafe { fe25519_add(Y3.as_mut_ptr(), Y1.as_ptr(), X1.as_ptr()) };
    unsafe { fe25519_add(Z3.as_mut_ptr(), Y2.as_ptr(), X2.as_ptr()) };
    unsafe { fe25519_mul(B.as_mut_ptr(), Y3.as_ptr(), Z3.as_ptr()) };
    unsafe { fe25519_mul_d2(Y3.as_mut_ptr(), T1.as_ptr()) };
    unsafe { fe25519_mul(C.as_mut_ptr(), Y3.as_ptr(), T2.as_ptr()) };
    unsafe { fe25519_mul(Y3.as_mut_ptr(), Z1.as_ptr(), Z2.as_ptr()) };
    unsafe { fe25519_mul_2(D.as_mut_ptr(), Y3.as_ptr()) };
    unsafe { fe25519_sub(E.as_mut_ptr(), B.as_ptr(), A.as_ptr()) };
    unsafe { fe25519_sub(F.as_mut_ptr(), D.as_ptr(), C.as_ptr()) };
    unsafe { fe25519_add(G.as_mut_ptr(), D.as_ptr(), C.as_ptr()) };
    unsafe { fe25519_add(H.as_mut_ptr(), B.as_ptr(), A.as_ptr()) };
    unsafe { fe25519_mul(X3.as_mut_ptr(), E.as_ptr(), F.as_ptr()) };
    unsafe { fe25519_mul(Y3.as_mut_ptr(), G.as_ptr(), H.as_ptr()) };
    unsafe { fe25519_mul(Z3.as_mut_ptr(), F.as_ptr(), G.as_ptr()) };
    unsafe { fe25519_pack_xyzt5(out.as_mut_ptr(), X3.as_ptr(), Y3.as_ptr(), Z3.as_ptr(), E.as_ptr(), H.as_ptr()) };
}

#[cfg(not(feature = "tfp25519_inline_limbs"))]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn xyzt_double_decomposed(out_raw: *mut u8, arg0_raw: *const u8) {
    let out: &mut [u8; 200] = unsafe { &mut *(out_raw as *mut [u8; 200]) };
    let arg0: &mut [u8; 200] = unsafe { &mut *(arg0_raw as *mut [u8; 200]) };
    let mut X: [u64; 5] = [0; 5];
    let mut Y: [u64; 5] = [0; 5];
    let mut Z: [u64; 5] = [0; 5];
    let mut Ta: [u64; 5] = [0; 5];
    let mut Tb: [u64; 5] = [0; 5];
    let mut A: [u64; 5] = [0; 5];
    let mut B: [u64; 5] = [0; 5];
    let mut C: [u64; 5] = [0; 5];
    let mut E: [u64; 5] = [0; 5];
    let mut F: [u64; 5] = [0; 5];
    let mut G: [u64; 5] = [0; 5];
    let mut H: [u64; 5] = [0; 5];
    let mut XpY: [u64; 5] = [0; 5];
    unsafe { fe25519_unpack_xyzt5(X.as_mut_ptr(), Y.as_mut_ptr(), Z.as_mut_ptr(), Ta.as_mut_ptr(), Tb.as_mut_ptr(), arg0.as_ptr()) };
    unsafe { fe25519_sqr(A.as_mut_ptr(), X.as_ptr()) };
    unsafe { fe25519_sqr(B.as_mut_ptr(), Y.as_ptr()) };
    unsafe { fe25519_sqr_scale2(C.as_mut_ptr(), Z.as_ptr()) };
    unsafe { fe25519_add(XpY.as_mut_ptr(), X.as_ptr(), Y.as_ptr()) };
    unsafe { fe25519_sqr_sub2(E.as_mut_ptr(), XpY.as_ptr(), A.as_ptr(), B.as_ptr()) };
    unsafe { fe25519_sub(G.as_mut_ptr(), B.as_ptr(), A.as_ptr()) };
    unsafe { fe25519_neg_add(H.as_mut_ptr(), A.as_ptr(), B.as_ptr()) };
    unsafe { fe25519_sub(F.as_mut_ptr(), G.as_ptr(), C.as_ptr()) };
    unsafe { fe25519_mul(X.as_mut_ptr(), E.as_ptr(), F.as_ptr()) };
    unsafe { fe25519_mul(Y.as_mut_ptr(), G.as_ptr(), H.as_ptr()) };
    unsafe { fe25519_mul(Z.as_mut_ptr(), F.as_ptr(), G.as_ptr()) };
    unsafe { fe25519_pack_xyzt5(out.as_mut_ptr(), X.as_ptr(), Y.as_ptr(), Z.as_ptr(), E.as_ptr(), H.as_ptr()) };
}
