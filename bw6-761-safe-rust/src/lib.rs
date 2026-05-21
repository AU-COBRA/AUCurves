//! BW6-761 field arithmetic + safe-Rust extension tower (Fp3/Fp6).
//!
//! Field operations (add, sub, mul, square, opp, to/from Montgomery,
//! to/from bytes) come from the auto-generated, machine-checked
//! `fiat-crypto/fiat-rust/src/bw6_761_64.rs`.  Constant-time modular
//! inversion comes from the Bernstein-Yang divstep port in
//! `safegcd-rs/src/safegcd_bw6_761.rs` (verified against the
//! convergence certificate in
//! `src/Arithmetic/safegcd/divsteps_bw6_761_half.v`).
//!
//! Extension tower (Fp3/Fp6) is emitted by the Coq-verified
//! `ToSafeRustBody.v` from the bedrock2 pairing definitions in
//! `BW6_761_Extract` — see `src/Bedrock/ExtractSafeTowerBW6_761.v`
//! and `src/Bedrock/bw6_761_safe_tower_main.ml`.
//!
//! 761-bit prime, 12×u64 saturated limb representation.  BW6-761 is
//! one of the SNARK-friendly outer curves over BLS12-377 (so the
//! scalar field of BLS12-377 equals the base field of BW6-761).
//!
//! ## Caveats
//!
//! Two pending blockers prevent end-to-end pairing against gnark's
//! reference vectors:
//!
//! 1. `BW6_761_FrobConsts.v` ships PLACEHOLDER Frobenius constants
//!    (gamma_fp3, gamma_fp6, gamma_fp3_p2, gamma_fp6_p2,
//!    gamma_fp6_p3).  Until those are replaced with SageMath-computed
//!    values for the BW6-761 prime, the final-exponentiation output
//!    will not match gnark's `e(P, Q)`.
//!
//! 2. `BW6_761_MillerLoop_proof.v` still has 5 outstanding `Admit`
//!    obligations (the Miller-loop BODY is Qed-clean; the proof of
//!    full algebraic correctness is in progress).
//!
//! KAT tests that depend on (1) are guarded with `#[ignore]` and
//! documented inline.  The structural / linkage KATs run.

#![allow(non_snake_case, non_camel_case_types)]
#![allow(unused_assignments, unused_variables, unused_mut, unused_parens, dead_code)]

pub use fiat_crypto::bw6_761_64::fiat_bw6_761_montgomery_domain_field_element as Fp;
pub use fiat_crypto::bw6_761_64::fiat_bw6_761_non_montgomery_domain_field_element as FpRaw;

use fiat_crypto::bw6_761_64::*;

#[inline] pub fn fp_add(out: &mut Fp, x: &Fp, y: &Fp)     { fiat_bw6_761_add(out, x, y) }
#[inline] pub fn fp_sub(out: &mut Fp, x: &Fp, y: &Fp)     { fiat_bw6_761_sub(out, x, y) }
#[inline] pub fn fp_mul(out: &mut Fp, x: &Fp, y: &Fp)     { fiat_bw6_761_mul(out, x, y) }
#[inline] pub fn fp_square(out: &mut Fp, x: &Fp)          { fiat_bw6_761_square(out, x) }
#[inline] pub fn fp_opp(out: &mut Fp, x: &Fp)             { fiat_bw6_761_opp(out, x) }
#[inline] pub fn fp_to_bytes(out: &mut [u8; 761/8 + (761%8>0) as usize], x: &Fp) {
    fiat_bw6_761_to_bytes(out, &x.0)
}
#[inline] pub fn fp_from_bytes(out: &mut FpRaw, bs: &[u8; 761/8 + (761%8>0) as usize]) {
    fiat_bw6_761_from_bytes(&mut out.0, bs)
}
#[inline] pub fn fp_to_montgomery(out: &mut Fp, x: &FpRaw)    { fiat_bw6_761_to_montgomery(out, x) }
#[inline] pub fn fp_from_montgomery(out: &mut FpRaw, x: &Fp)  { fiat_bw6_761_from_montgomery(out, x) }

/// Constant-time modular inverse via the Bernstein–Yang divstep port.
/// Input/output are in Montgomery form.  Convert out → invert → convert in.
pub fn fp_inv(out: &mut Fp, x: &Fp) {
    let mut raw_in = FpRaw([0u64; 12]);
    fp_from_montgomery(&mut raw_in, x);
    let mut raw_inv = [0u64; 12];
    safegcd::safegcd_bw6_761::bw6_761_invert_divstep_sat(&mut raw_inv, &raw_in.0);
    fp_to_montgomery(out, &FpRaw(raw_inv));
}

/// Bernstein–Yang raw inverse on canonical 12×u64 limbs (NOT in
/// Montgomery form).
pub fn invert_raw(out: &mut [u64; 12], x: &[u64; 12]) {
    safegcd::safegcd_bw6_761::bw6_761_invert_divstep_sat(out, x);
}

// ─── extern "C" shim: provide the `_bw6_761_*` symbols the tower
// expects.  Each shim copies its arguments into Fp records, calls
// the fiat-rust wrapper from this same crate, and copies the result
// back.  All 9 leaves the tower's extern block declares are covered
// here.  Mirrors the bls12-377-safe-rust crate's extern_shim module.
mod extern_shim {
    use super::*;
    use core::ptr::copy_nonoverlapping;

    #[inline] fn rd12(p: *const u64) -> [u64; 12] {
        let mut a = [0u64; 12]; unsafe { copy_nonoverlapping(p, a.as_mut_ptr(), 12) }; a
    }
    #[inline] fn wr12(p: *mut u64, a: &[u64; 12]) {
        unsafe { copy_nonoverlapping(a.as_ptr(), p, 12) }
    }

    #[no_mangle] pub unsafe extern "C" fn _bw6_761_add(o: *mut u64, x: *const u64, y: *const u64) {
        let mut out = Fp([0u64; 12]);
        fp_add(&mut out, &Fp(rd12(x)), &Fp(rd12(y)));
        wr12(o, &out.0);
    }
    #[no_mangle] pub unsafe extern "C" fn _bw6_761_sub(o: *mut u64, x: *const u64, y: *const u64) {
        let mut out = Fp([0u64; 12]);
        fp_sub(&mut out, &Fp(rd12(x)), &Fp(rd12(y)));
        wr12(o, &out.0);
    }
    #[no_mangle] pub unsafe extern "C" fn _bw6_761_mul(o: *mut u64, x: *const u64, y: *const u64) {
        let mut out = Fp([0u64; 12]);
        fp_mul(&mut out, &Fp(rd12(x)), &Fp(rd12(y)));
        wr12(o, &out.0);
    }
    #[no_mangle] pub unsafe extern "C" fn _bw6_761_square(o: *mut u64, x: *const u64) {
        let mut out = Fp([0u64; 12]);
        fp_square(&mut out, &Fp(rd12(x)));
        wr12(o, &out.0);
    }
    #[no_mangle] pub unsafe extern "C" fn _bw6_761_opp(o: *mut u64, x: *const u64) {
        let mut out = Fp([0u64; 12]);
        fp_opp(&mut out, &Fp(rd12(x)));
        wr12(o, &out.0);
    }
    #[no_mangle] pub unsafe extern "C" fn _bw6_761_felem_copy(o: *mut u64, x: *const u64) {
        wr12(o, &rd12(x));
    }
    #[no_mangle] pub unsafe extern "C" fn _bw6_761_from_word(o: *mut u64, w: u64) {
        // Word w → Montgomery domain via to_montgomery(non-montgomery(w)).
        let mut raw = FpRaw([0u64; 12]);
        raw.0[0] = w;
        let mut out = Fp([0u64; 12]);
        fp_to_montgomery(&mut out, &raw);
        wr12(o, &out.0);
    }
    #[no_mangle] pub unsafe extern "C" fn _bw6_761_select_znz(
        o: *mut u64, c: u64, x: *const u64, y: *const u64,
    ) {
        // Constant-time select: c == 0 picks x, else picks y.
        let x_a = rd12(x);
        let y_a = rd12(y);
        let mut out = [0u64; 12];
        let mask = (!(c == 0) as u64).wrapping_neg();
        for i in 0..12 { out[i] = (mask & y_a[i]) | (!mask & x_a[i]); }
        wr12(o, &out);
    }
    #[no_mangle] pub unsafe extern "C" fn _bw6_761_inv(o: *mut u64, x: *const u64) {
        let mut out = Fp([0u64; 12]);
        fp_inv(&mut out, &Fp(rd12(x)));
        wr12(o, &out.0);
    }
}

/// Verified safe-Rust extension tower (Fp3/Fp6) emitted by
/// ToSafeRustBody.v from the bedrock2 pairing definitions.  Generated
/// by `src/Bedrock/ExtractSafeTowerBW6_761.v` + the OCaml driver
/// `src/Bedrock/bw6_761_safe_tower_main.ml`; the heredoc in the
/// driver provides the extern-C leaf wrappers and the
/// `bw6_761_Fp6_inv` helper (norm-trick over Fp3) used by the
/// verified `bw6_final_exp_easy` body.
pub mod tower {
    include!(concat!(env!("CARGO_MANIFEST_DIR"), "/generated/bw6_761_safe_tower.rs"));
}

pub use tower::{Fp as TowerFp, Fp3, Fp6};

/// G1 affine point on BW6-761: y^2 = x^3 - 1 over the tower's Fp
/// representation.  The tower's `Fp` is a `#[repr(C)] [u64;12]`
/// newtype distinct from (but byte-identical to) the
/// `fiat_bw6_761_montgomery_domain_field_element` re-exported as
/// `crate::Fp`.
#[repr(C)] #[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct G1 { pub x: TowerFp, pub y: TowerFp }

/// G2 affine point on the M-type cubic twist E'(Fp3): y^2 = x^3 - 1/zeta.
#[repr(C)] #[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct G2 { pub x: Fp3, pub y: Fp3 }

/// Optimal-ate pairing on BW6-761: G1 × G2 → Fp6.
///
/// Wires the verified `bw6_761_miller_loop` (single-loop binary
/// Miller body, |x_0|-parameterised — see [`BW6_761_MillerLoop.v`])
/// into the verified `bw6_final_exp` (Hayashida-style final
/// exponentiation — see [`BW6_761_FinalExp.v`]).
///
/// **Caveat**: the final-exponentiation step consumes 5 Frobenius
/// constants (`gamma_fp3`, `gamma_fp6`, `gamma_fp3_p2`,
/// `gamma_fp6_p2`, `gamma_fp6_p3`).  These are passed as caller-
/// supplied Fp3 elements so the function is reusable; the canonical
/// BW6-761 values must be computed offline (SageMath) since
/// `BW6_761_FrobConsts.v` ships placeholders.  See the module-level
/// doc comment for details.
pub fn pairing(
    out: &mut Fp6,
    p: &G1, q: &G2,
    gamma_fp3: &Fp3, gamma_fp6: &Fp3,
    gamma_fp3_p2: &Fp3, gamma_fp6_p2: &Fp3,
    gamma_fp6_p3: &Fp3,
) {
    use tower::{bw6_761_miller_loop, bw6_final_exp};
    let mut f = Fp6::zero();
    bw6_761_miller_loop(&mut f, &p.x, &p.y, &q.x, &q.y);
    bw6_final_exp(out, &f, gamma_fp3, gamma_fp6,
                  gamma_fp3_p2, gamma_fp6_p2, gamma_fp6_p3);
}

#[cfg(test)]
mod kat;
