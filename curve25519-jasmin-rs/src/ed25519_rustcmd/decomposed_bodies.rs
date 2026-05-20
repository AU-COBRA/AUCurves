//! Decomposed Ed25519 curve-leaf bodies, extracted from the verified
//! `function_table_ed` in `AUCurves/src/Bedrock/End2End/Ed25519/CurveBodies.v`
//! via `Bedrock/ExtractCurveBodies.v`.
//!
//! **FFI centralization (status doc §6.3, Phase B) — EXEMPT.**
//! Mechanically IR-emitted from the verified AST; the `unsafe`
//! blocks here are FFI dispatch to `fe25519_*` per-limb arithmetic
//! and will collapse when the emitter is updated to target
//! `ffi_safe::*` directly.
//!
//! Verification chain: each body is a `function_body_ed` whose
//! granular decomposition is proved correct (XyztAdd/Double/Scalarmult/
//! ScalarmultBase BodyDecomposed.v).  The `rs_table_extract` emitter
//! casts each raw `*mut u8` / `*const u8` to a fixed-size array
//! reference and dispatches the AST via `rs_emit`.
//!
//! Each entry is `extern "C"` with raw-pointer signatures so the
//! `decomposed_curve_leaves` panic-replacement wrappers and the
//! intra-body cross-calls (e.g. `scalarmult_decomposed` →
//! `xyzt_double_decomposed`) share the same FFI surface.
//!
//! Field-op leaves (`fe25519_mul`, `fe25519_unpack_xyzt5`, ...) are
//! declared `extern "C"` below; they are provided by either the
//! fiat-crypto portable shim or the Jasmin backend (see
//! `fe25519_portable.rs` / build.rs).

#![allow(non_snake_case, unused_assignments, unused_mut, unused_variables, unused_parens, dead_code)]

unsafe extern "C" {
    fn fe25519_add(out: *mut u8, a: *const u8, b: *const u8);
    fn fe25519_sub(out: *mut u8, a: *const u8, b: *const u8);
    fn fe25519_mul(out: *mut u8, a: *const u8, b: *const u8);
    fn fe25519_sqr(out: *mut u8, a: *const u8);
    fn fe25519_mul_2(out: *mut u8, a: *const u8);
    fn fe25519_mul_d2(out: *mut u8, a: *const u8);
    fn fe25519_sqr_scale2(out: *mut u8, a: *const u8);
    /// out := a^2 - b - c   (used in xyzt_double_decomposed: E = (X+Y)^2 - A - B).
    fn fe25519_sqr_sub2(out: *mut u8, a: *const u8, b: *const u8, c: *const u8);
    fn fe25519_neg_add(out: *mut u8, a: *const u8, b: *const u8);
    fn fe25519_unpack_xyzt5(x: *mut u8, y: *mut u8, z: *mut u8,
                            ta: *mut u8, tb: *mut u8, p: *const u8);
    fn fe25519_pack_xyzt5(out: *mut u8, x: *const u8, y: *const u8,
                          z: *const u8, ta: *const u8, tb: *const u8);
    fn fe25519_xyzt_copy(out: *mut u8, src: *const u8);
}

/// When `tfp25519_limbs` is active, the xyzt_*_decomposed *definitions*
/// below are cfg-gated out (the symbols come from
/// `decomposed_bodies_limbs.rs` instead).  In-tree Rust callers
/// (`scalarmult_decomposed` below, `leaves.rs::ed25519_xyzt_add`)
/// still need names for them, so re-import via `extern "C"`.
#[cfg(feature = "tfp25519_limbs")]
unsafe extern "C" {
    pub fn xyzt_add_decomposed(out: *mut u8, a: *const u8, b: *const u8);
    pub fn xyzt_double_decomposed(out: *mut u8, a: *const u8);
}

#[cfg(not(feature = "tfp25519_limbs"))]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn xyzt_add_decomposed(out_raw: *mut u8, arg0_raw: *const u8, arg1_raw: *const u8) {
    let out: &mut [u8; 200] = unsafe { &mut *(out_raw as *mut [u8; 200]) };
    let arg0: &mut [u8; 200] = unsafe { &mut *(arg0_raw as *mut [u8; 200]) };
    let arg1: &mut [u8; 200] = unsafe { &mut *(arg1_raw as *mut [u8; 200]) };
    let mut X1: [u8; 40] = [0; 40];
    let mut Y1: [u8; 40] = [0; 40];
    let mut Z1: [u8; 40] = [0; 40];
    let mut Ta1: [u8; 40] = [0; 40];
    let mut Tb1: [u8; 40] = [0; 40];
    let mut X2: [u8; 40] = [0; 40];
    let mut Y2: [u8; 40] = [0; 40];
    let mut Z2: [u8; 40] = [0; 40];
    let mut Ta2: [u8; 40] = [0; 40];
    let mut Tb2: [u8; 40] = [0; 40];
    let mut T1: [u8; 40] = [0; 40];
    let mut T2: [u8; 40] = [0; 40];
    let mut A: [u8; 40] = [0; 40];
    let mut B: [u8; 40] = [0; 40];
    let mut C: [u8; 40] = [0; 40];
    let mut D: [u8; 40] = [0; 40];
    let mut E: [u8; 40] = [0; 40];
    let mut F: [u8; 40] = [0; 40];
    let mut G: [u8; 40] = [0; 40];
    let mut H: [u8; 40] = [0; 40];
    let mut X3: [u8; 40] = [0; 40];
    let mut Y3: [u8; 40] = [0; 40];
    let mut Z3: [u8; 40] = [0; 40];
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

#[cfg(not(feature = "tfp25519_limbs"))]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn xyzt_double_decomposed(out_raw: *mut u8, arg0_raw: *const u8) {
    let out: &mut [u8; 200] = unsafe { &mut *(out_raw as *mut [u8; 200]) };
    let arg0: &mut [u8; 200] = unsafe { &mut *(arg0_raw as *mut [u8; 200]) };
    let mut X: [u8; 40] = [0; 40];
    let mut Y: [u8; 40] = [0; 40];
    let mut Z: [u8; 40] = [0; 40];
    let mut Ta: [u8; 40] = [0; 40];
    let mut Tb: [u8; 40] = [0; 40];
    let mut A: [u8; 40] = [0; 40];
    let mut B: [u8; 40] = [0; 40];
    let mut C: [u8; 40] = [0; 40];
    let mut E: [u8; 40] = [0; 40];
    let mut F: [u8; 40] = [0; 40];
    let mut G: [u8; 40] = [0; 40];
    let mut H: [u8; 40] = [0; 40];
    let mut XpY: [u8; 40] = [0; 40];
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

#[unsafe(no_mangle)]
pub unsafe extern "C" fn scalarmult_decomposed(out_raw: *mut u8, arg0_raw: *const u8, arg1_raw: *const u8) {
    let out: &mut [u8; 200] = unsafe { &mut *(out_raw as *mut [u8; 200]) };
    let arg0: &mut [u8; 32] = unsafe { &mut *(arg0_raw as *mut [u8; 32]) };
    let arg1: &mut [u8; 200] = unsafe { &mut *(arg1_raw as *mut [u8; 200]) };
    let mut accum: [u8; 200] = [0; 200];
    let mut tmp: [u8; 200] = [0; 200];
    accum[(40u64) as usize] = (1u64) as u8;
    accum[(80u64) as usize] = (1u64) as u8;
    for i in 0u64..256u64 {
        unsafe { xyzt_double_decomposed(accum.as_mut_ptr(), accum.as_ptr()) };
        unsafe { xyzt_add_decomposed(tmp.as_mut_ptr(), accum.as_ptr(), arg1.as_ptr()) };
        let mut scalar_idx: u64 = (255u64.wrapping_sub(i));
        let mut byte_idx: u64 = (scalar_idx >> 3u64);
        let mut bit_idx: u64 = (scalar_idx & 7u64);
        let byte_val: u64 = arg0[(byte_idx) as usize] as u64;
        let mut bit: u64 = ((byte_val >> bit_idx) & 1u64);
        { let _mask: u8 = (if (bit) != 0 { 0xffu8 } else { 0x00u8 });
          for _i in 0..(accum.len() as usize) {
            accum[_i] = (tmp[_i] & _mask) | (accum[_i] & !_mask);
          } }
    };
    unsafe { xyzt_copy(out.as_mut_ptr(), accum.as_ptr()) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn scalarmult_base_decomposed(out_raw: *mut u8, arg0_raw: *const u8) {
    let out: &mut [u8; 200] = unsafe { &mut *(out_raw as *mut [u8; 200]) };
    let arg0: &mut [u8; 32] = unsafe { &mut *(arg0_raw as *mut [u8; 32]) };
    let mut B_local: [u8; 200] = [0; 200];
    B_local[(0u64) as usize] = (26u64) as u8;
    B_local[(1u64) as usize] = (213u64) as u8;
    B_local[(2u64) as usize] = (37u64) as u8;
    B_local[(3u64) as usize] = (143u64) as u8;
    B_local[(4u64) as usize] = (96u64) as u8;
    B_local[(5u64) as usize] = (45u64) as u8;
    B_local[(6u64) as usize] = (86u64) as u8;
    B_local[(7u64) as usize] = (201u64) as u8;
    B_local[(8u64) as usize] = (178u64) as u8;
    B_local[(9u64) as usize] = (167u64) as u8;
    B_local[(10u64) as usize] = (37u64) as u8;
    B_local[(11u64) as usize] = (149u64) as u8;
    B_local[(12u64) as usize] = (96u64) as u8;
    B_local[(13u64) as usize] = (199u64) as u8;
    B_local[(14u64) as usize] = (44u64) as u8;
    B_local[(15u64) as usize] = (105u64) as u8;
    B_local[(16u64) as usize] = (92u64) as u8;
    B_local[(17u64) as usize] = (220u64) as u8;
    B_local[(18u64) as usize] = (214u64) as u8;
    B_local[(19u64) as usize] = (253u64) as u8;
    B_local[(20u64) as usize] = (49u64) as u8;
    B_local[(21u64) as usize] = (226u64) as u8;
    B_local[(22u64) as usize] = (164u64) as u8;
    B_local[(23u64) as usize] = (192u64) as u8;
    B_local[(24u64) as usize] = (254u64) as u8;
    B_local[(25u64) as usize] = (83u64) as u8;
    B_local[(26u64) as usize] = (110u64) as u8;
    B_local[(27u64) as usize] = (205u64) as u8;
    B_local[(28u64) as usize] = (211u64) as u8;
    B_local[(29u64) as usize] = (54u64) as u8;
    B_local[(30u64) as usize] = (105u64) as u8;
    B_local[(31u64) as usize] = (33u64) as u8;
    B_local[(32u64) as usize] = (0u64) as u8;
    B_local[(33u64) as usize] = (0u64) as u8;
    B_local[(34u64) as usize] = (0u64) as u8;
    B_local[(35u64) as usize] = (0u64) as u8;
    B_local[(36u64) as usize] = (0u64) as u8;
    B_local[(37u64) as usize] = (0u64) as u8;
    B_local[(38u64) as usize] = (0u64) as u8;
    B_local[(39u64) as usize] = (0u64) as u8;
    B_local[(40u64) as usize] = (88u64) as u8;
    B_local[(41u64) as usize] = (102u64) as u8;
    B_local[(42u64) as usize] = (102u64) as u8;
    B_local[(43u64) as usize] = (102u64) as u8;
    B_local[(44u64) as usize] = (102u64) as u8;
    B_local[(45u64) as usize] = (102u64) as u8;
    B_local[(46u64) as usize] = (102u64) as u8;
    B_local[(47u64) as usize] = (102u64) as u8;
    B_local[(48u64) as usize] = (102u64) as u8;
    B_local[(49u64) as usize] = (102u64) as u8;
    B_local[(50u64) as usize] = (102u64) as u8;
    B_local[(51u64) as usize] = (102u64) as u8;
    B_local[(52u64) as usize] = (102u64) as u8;
    B_local[(53u64) as usize] = (102u64) as u8;
    B_local[(54u64) as usize] = (102u64) as u8;
    B_local[(55u64) as usize] = (102u64) as u8;
    B_local[(56u64) as usize] = (102u64) as u8;
    B_local[(57u64) as usize] = (102u64) as u8;
    B_local[(58u64) as usize] = (102u64) as u8;
    B_local[(59u64) as usize] = (102u64) as u8;
    B_local[(60u64) as usize] = (102u64) as u8;
    B_local[(61u64) as usize] = (102u64) as u8;
    B_local[(62u64) as usize] = (102u64) as u8;
    B_local[(63u64) as usize] = (102u64) as u8;
    B_local[(64u64) as usize] = (102u64) as u8;
    B_local[(65u64) as usize] = (102u64) as u8;
    B_local[(66u64) as usize] = (102u64) as u8;
    B_local[(67u64) as usize] = (102u64) as u8;
    B_local[(68u64) as usize] = (102u64) as u8;
    B_local[(69u64) as usize] = (102u64) as u8;
    B_local[(70u64) as usize] = (102u64) as u8;
    B_local[(71u64) as usize] = (102u64) as u8;
    B_local[(72u64) as usize] = (0u64) as u8;
    B_local[(73u64) as usize] = (0u64) as u8;
    B_local[(74u64) as usize] = (0u64) as u8;
    B_local[(75u64) as usize] = (0u64) as u8;
    B_local[(76u64) as usize] = (0u64) as u8;
    B_local[(77u64) as usize] = (0u64) as u8;
    B_local[(78u64) as usize] = (0u64) as u8;
    B_local[(79u64) as usize] = (0u64) as u8;
    B_local[(80u64) as usize] = (1u64) as u8;
    B_local[(81u64) as usize] = (0u64) as u8;
    B_local[(82u64) as usize] = (0u64) as u8;
    B_local[(83u64) as usize] = (0u64) as u8;
    B_local[(84u64) as usize] = (0u64) as u8;
    B_local[(85u64) as usize] = (0u64) as u8;
    B_local[(86u64) as usize] = (0u64) as u8;
    B_local[(87u64) as usize] = (0u64) as u8;
    B_local[(88u64) as usize] = (0u64) as u8;
    B_local[(89u64) as usize] = (0u64) as u8;
    B_local[(90u64) as usize] = (0u64) as u8;
    B_local[(91u64) as usize] = (0u64) as u8;
    B_local[(92u64) as usize] = (0u64) as u8;
    B_local[(93u64) as usize] = (0u64) as u8;
    B_local[(94u64) as usize] = (0u64) as u8;
    B_local[(95u64) as usize] = (0u64) as u8;
    B_local[(96u64) as usize] = (0u64) as u8;
    B_local[(97u64) as usize] = (0u64) as u8;
    B_local[(98u64) as usize] = (0u64) as u8;
    B_local[(99u64) as usize] = (0u64) as u8;
    B_local[(100u64) as usize] = (0u64) as u8;
    B_local[(101u64) as usize] = (0u64) as u8;
    B_local[(102u64) as usize] = (0u64) as u8;
    B_local[(103u64) as usize] = (0u64) as u8;
    B_local[(104u64) as usize] = (0u64) as u8;
    B_local[(105u64) as usize] = (0u64) as u8;
    B_local[(106u64) as usize] = (0u64) as u8;
    B_local[(107u64) as usize] = (0u64) as u8;
    B_local[(108u64) as usize] = (0u64) as u8;
    B_local[(109u64) as usize] = (0u64) as u8;
    B_local[(110u64) as usize] = (0u64) as u8;
    B_local[(111u64) as usize] = (0u64) as u8;
    B_local[(112u64) as usize] = (0u64) as u8;
    B_local[(113u64) as usize] = (0u64) as u8;
    B_local[(114u64) as usize] = (0u64) as u8;
    B_local[(115u64) as usize] = (0u64) as u8;
    B_local[(116u64) as usize] = (0u64) as u8;
    B_local[(117u64) as usize] = (0u64) as u8;
    B_local[(118u64) as usize] = (0u64) as u8;
    B_local[(119u64) as usize] = (0u64) as u8;
    B_local[(120u64) as usize] = (26u64) as u8;
    B_local[(121u64) as usize] = (213u64) as u8;
    B_local[(122u64) as usize] = (37u64) as u8;
    B_local[(123u64) as usize] = (143u64) as u8;
    B_local[(124u64) as usize] = (96u64) as u8;
    B_local[(125u64) as usize] = (45u64) as u8;
    B_local[(126u64) as usize] = (86u64) as u8;
    B_local[(127u64) as usize] = (201u64) as u8;
    B_local[(128u64) as usize] = (178u64) as u8;
    B_local[(129u64) as usize] = (167u64) as u8;
    B_local[(130u64) as usize] = (37u64) as u8;
    B_local[(131u64) as usize] = (149u64) as u8;
    B_local[(132u64) as usize] = (96u64) as u8;
    B_local[(133u64) as usize] = (199u64) as u8;
    B_local[(134u64) as usize] = (44u64) as u8;
    B_local[(135u64) as usize] = (105u64) as u8;
    B_local[(136u64) as usize] = (92u64) as u8;
    B_local[(137u64) as usize] = (220u64) as u8;
    B_local[(138u64) as usize] = (214u64) as u8;
    B_local[(139u64) as usize] = (253u64) as u8;
    B_local[(140u64) as usize] = (49u64) as u8;
    B_local[(141u64) as usize] = (226u64) as u8;
    B_local[(142u64) as usize] = (164u64) as u8;
    B_local[(143u64) as usize] = (192u64) as u8;
    B_local[(144u64) as usize] = (254u64) as u8;
    B_local[(145u64) as usize] = (83u64) as u8;
    B_local[(146u64) as usize] = (110u64) as u8;
    B_local[(147u64) as usize] = (205u64) as u8;
    B_local[(148u64) as usize] = (211u64) as u8;
    B_local[(149u64) as usize] = (54u64) as u8;
    B_local[(150u64) as usize] = (105u64) as u8;
    B_local[(151u64) as usize] = (33u64) as u8;
    B_local[(152u64) as usize] = (0u64) as u8;
    B_local[(153u64) as usize] = (0u64) as u8;
    B_local[(154u64) as usize] = (0u64) as u8;
    B_local[(155u64) as usize] = (0u64) as u8;
    B_local[(156u64) as usize] = (0u64) as u8;
    B_local[(157u64) as usize] = (0u64) as u8;
    B_local[(158u64) as usize] = (0u64) as u8;
    B_local[(159u64) as usize] = (0u64) as u8;
    B_local[(160u64) as usize] = (88u64) as u8;
    B_local[(161u64) as usize] = (102u64) as u8;
    B_local[(162u64) as usize] = (102u64) as u8;
    B_local[(163u64) as usize] = (102u64) as u8;
    B_local[(164u64) as usize] = (102u64) as u8;
    B_local[(165u64) as usize] = (102u64) as u8;
    B_local[(166u64) as usize] = (102u64) as u8;
    B_local[(167u64) as usize] = (102u64) as u8;
    B_local[(168u64) as usize] = (102u64) as u8;
    B_local[(169u64) as usize] = (102u64) as u8;
    B_local[(170u64) as usize] = (102u64) as u8;
    B_local[(171u64) as usize] = (102u64) as u8;
    B_local[(172u64) as usize] = (102u64) as u8;
    B_local[(173u64) as usize] = (102u64) as u8;
    B_local[(174u64) as usize] = (102u64) as u8;
    B_local[(175u64) as usize] = (102u64) as u8;
    B_local[(176u64) as usize] = (102u64) as u8;
    B_local[(177u64) as usize] = (102u64) as u8;
    B_local[(178u64) as usize] = (102u64) as u8;
    B_local[(179u64) as usize] = (102u64) as u8;
    B_local[(180u64) as usize] = (102u64) as u8;
    B_local[(181u64) as usize] = (102u64) as u8;
    B_local[(182u64) as usize] = (102u64) as u8;
    B_local[(183u64) as usize] = (102u64) as u8;
    B_local[(184u64) as usize] = (102u64) as u8;
    B_local[(185u64) as usize] = (102u64) as u8;
    B_local[(186u64) as usize] = (102u64) as u8;
    B_local[(187u64) as usize] = (102u64) as u8;
    B_local[(188u64) as usize] = (102u64) as u8;
    B_local[(189u64) as usize] = (102u64) as u8;
    B_local[(190u64) as usize] = (102u64) as u8;
    B_local[(191u64) as usize] = (102u64) as u8;
    B_local[(192u64) as usize] = (0u64) as u8;
    B_local[(193u64) as usize] = (0u64) as u8;
    B_local[(194u64) as usize] = (0u64) as u8;
    B_local[(195u64) as usize] = (0u64) as u8;
    B_local[(196u64) as usize] = (0u64) as u8;
    B_local[(197u64) as usize] = (0u64) as u8;
    B_local[(198u64) as usize] = (0u64) as u8;
    B_local[(199u64) as usize] = (0u64) as u8;
    unsafe { scalarmult_decomposed(out.as_mut_ptr(), arg0.as_ptr(), B_local.as_ptr()) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn xyzt_copy(out_raw: *mut u8, arg0_raw: *const u8) {
    let out: &mut [u8; 200] = unsafe { &mut *(out_raw as *mut [u8; 200]) };
    let arg0: &mut [u8; 200] = unsafe { &mut *(arg0_raw as *mut [u8; 200]) };
    unsafe { fe25519_xyzt_copy(out.as_mut_ptr(), arg0.as_ptr()) };
}
