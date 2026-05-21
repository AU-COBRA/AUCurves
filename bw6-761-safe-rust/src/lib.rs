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

/// G1/G2 group operations and scalar multiplication.
///
/// Backed by the verified field/tower bodies (`tower::bw6_761_*`,
/// `fp_*`).  Group-level formulas (Weierstrass affine add/double) are
/// reference Rust mirroring the Gallina specs in
/// `src/Bedrock/Curve/BW6_761Curve_G2.v` +
/// `src/Bedrock/Field/Synthesis/Examples/BW6_761_GroupOps.v`.
///
/// The group-level code in this module is NOT yet emitted from a
/// verified bedrock2 body; the underlying field/tower ops are.
/// Algebraic equivalence with the Gallina spec will be discharged in
/// a downstream `BW6_761_Group_proof.v` once the WP bodies land.
pub mod group {
    use super::*;
    use tower::{
        Fp as TFp, Fp3,
        bw6_761_add as fp_add_t, bw6_761_sub as fp_sub_t,
        bw6_761_mul as fp_mul_t, bw6_761_opp as fp_opp_t,
        bw6_761_inv as fp_inv_t, bw6_761_from_word as fp_from_word_t,
        bw6_761_zero as fp_zero_t, bw6_761_one as fp_one_t,
        bw6_761_Fp3_zero, bw6_761_Fp3_one, bw6_761_Fp3_add, bw6_761_Fp3_sub,
        bw6_761_Fp3_opp, bw6_761_Fp3_mul, bw6_761_Fp3_square,
        bw6_761_Fp3_inv, bw6_761_Fp3_felem_copy,
    };

    fn fp_is_zero(x: &TFp) -> bool { x.0.iter().all(|&w| w == 0) }
    fn fp3_is_zero(x: &Fp3) -> bool { fp_is_zero(&x.c0) && fp_is_zero(&x.c1) && fp_is_zero(&x.c2) }
    fn fp_eq(a: &TFp, b: &TFp) -> bool { a.0 == b.0 }
    fn fp3_eq(a: &Fp3, b: &Fp3) -> bool {
        fp_eq(&a.c0, &b.c0) && fp_eq(&a.c1, &b.c1) && fp_eq(&a.c2, &b.c2)
    }

    // ────────────────────── G1 affine ──────────────────────────────

    /// G1 affine point: either the point at infinity or (x, y) ∈ Fp².
    /// Matches the Gallina [BW6_G1_aff] = G1_inf | G1_pt(x, y).
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum G1Aff { Inf, Pt(TFp, TFp) }

    impl G1Aff {
        pub fn inf() -> Self { G1Aff::Inf }
        pub fn pt(x: TFp, y: TFp) -> Self { G1Aff::Pt(x, y) }
    }

    /// Negate a G1 affine point: (x, y) → (x, -y); inf → inf.
    pub fn g1_neg(P: &G1Aff) -> G1Aff {
        match P {
            G1Aff::Inf => G1Aff::Inf,
            G1Aff::Pt(x, y) => {
                let mut ny = TFp::zero();
                fp_opp_t(&mut ny, y);
                G1Aff::Pt(*x, ny)
            }
        }
    }

    /// G1 doubling on E: y² = x³ - 1 (a = 0).
    pub fn g1_double(P: &G1Aff) -> G1Aff {
        match P {
            G1Aff::Inf => G1Aff::Inf,
            G1Aff::Pt(x, y) => {
                if fp_is_zero(y) { return G1Aff::Inf; }
                // λ = 3·x² / (2·y)
                let mut x_sq = TFp::zero();
                fp_mul_t(&mut x_sq, x, x);
                let mut tmp = TFp::zero();
                fp_add_t(&mut tmp, &x_sq, &x_sq);
                let mut three_x_sq = TFp::zero();
                fp_add_t(&mut three_x_sq, &tmp, &x_sq);
                let mut two_y = TFp::zero();
                fp_add_t(&mut two_y, y, y);
                let mut inv_2y = TFp::zero();
                fp_inv_t(&mut inv_2y, &two_y);
                let mut lam = TFp::zero();
                fp_mul_t(&mut lam, &three_x_sq, &inv_2y);
                // x' = λ² - 2x
                let mut lam_sq = TFp::zero();
                fp_mul_t(&mut lam_sq, &lam, &lam);
                let mut twox = TFp::zero();
                fp_add_t(&mut twox, x, x);
                let mut xp = TFp::zero();
                fp_sub_t(&mut xp, &lam_sq, &twox);
                // y' = λ·(x - x') - y
                let mut dx = TFp::zero();
                fp_sub_t(&mut dx, x, &xp);
                let mut lam_dx = TFp::zero();
                fp_mul_t(&mut lam_dx, &lam, &dx);
                let mut yp = TFp::zero();
                fp_sub_t(&mut yp, &lam_dx, y);
                G1Aff::Pt(xp, yp)
            }
        }
    }

    /// G1 affine add (full case-split).
    pub fn g1_add(P: &G1Aff, Q: &G1Aff) -> G1Aff {
        match (P, Q) {
            (G1Aff::Inf, _) => *Q,
            (_, G1Aff::Inf) => *P,
            (G1Aff::Pt(x1, y1), G1Aff::Pt(x2, y2)) => {
                if fp_eq(x1, x2) {
                    if fp_eq(y1, y2) { g1_double(P) }
                    else { G1Aff::Inf }
                } else {
                    let mut dy = TFp::zero(); fp_sub_t(&mut dy, y2, y1);
                    let mut dx = TFp::zero(); fp_sub_t(&mut dx, x2, x1);
                    let mut inv_dx = TFp::zero(); fp_inv_t(&mut inv_dx, &dx);
                    let mut lam = TFp::zero(); fp_mul_t(&mut lam, &dy, &inv_dx);
                    let mut lam_sq = TFp::zero(); fp_mul_t(&mut lam_sq, &lam, &lam);
                    let mut tmp = TFp::zero(); fp_sub_t(&mut tmp, &lam_sq, x1);
                    let mut x3 = TFp::zero(); fp_sub_t(&mut x3, &tmp, x2);
                    let mut delta = TFp::zero(); fp_sub_t(&mut delta, x1, &x3);
                    let mut lam_delta = TFp::zero(); fp_mul_t(&mut lam_delta, &lam, &delta);
                    let mut y3 = TFp::zero(); fp_sub_t(&mut y3, &lam_delta, y1);
                    G1Aff::Pt(x3, y3)
                }
            }
        }
    }

    /// G1 scalar multiplication (binary, MSB-first, double-and-add).
    /// `scalar_be` is the scalar in big-endian bytes.  NOT constant-time.
    pub fn g1_scalar_mul(scalar_be: &[u8], P: &G1Aff) -> G1Aff {
        let mut acc = G1Aff::Inf;
        let mut started = false;
        for &byte in scalar_be {
            for i in 0..8 {
                let bit = (byte >> (7 - i)) & 1;
                if started { acc = g1_double(&acc); }
                if bit == 1 {
                    if started { acc = g1_add(&acc, P); }
                    else { acc = *P; started = true; }
                }
            }
        }
        acc
    }

    // ────────────────────── G2 affine ──────────────────────────────

    /// G2 affine point on the M-type cubic twist E': y² = x³ - 1/zeta over Fp3.
    /// Matches the Gallina [G2_aff_fp3] = G2f3_inf | G2f3_pt(x, y).
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum G2Aff { Inf, Pt(Fp3, Fp3) }

    impl G2Aff {
        pub fn inf() -> Self { G2Aff::Inf }
        pub fn pt(x: Fp3, y: Fp3) -> Self { G2Aff::Pt(x, y) }
    }

    pub fn g2_neg(P: &G2Aff) -> G2Aff {
        match P {
            G2Aff::Inf => G2Aff::Inf,
            G2Aff::Pt(x, y) => {
                let mut ny = Fp3::zero();
                bw6_761_Fp3_opp(&mut ny, y);
                G2Aff::Pt(*x, ny)
            }
        }
    }

    pub fn g2_double(P: &G2Aff) -> G2Aff {
        match P {
            G2Aff::Inf => G2Aff::Inf,
            G2Aff::Pt(x, y) => {
                if fp3_is_zero(y) { return G2Aff::Inf; }
                let mut x_sq = Fp3::zero(); bw6_761_Fp3_square(&mut x_sq, x);
                let mut tmp = Fp3::zero(); bw6_761_Fp3_add(&mut tmp, &x_sq, &x_sq);
                let mut three_x_sq = Fp3::zero(); bw6_761_Fp3_add(&mut three_x_sq, &tmp, &x_sq);
                let mut two_y = Fp3::zero(); bw6_761_Fp3_add(&mut two_y, y, y);
                let mut inv_2y = Fp3::zero(); bw6_761_Fp3_inv(&mut inv_2y, &two_y);
                let mut lam = Fp3::zero(); bw6_761_Fp3_mul(&mut lam, &three_x_sq, &inv_2y);
                let mut lam_sq = Fp3::zero(); bw6_761_Fp3_mul(&mut lam_sq, &lam, &lam);
                let mut twox = Fp3::zero(); bw6_761_Fp3_add(&mut twox, x, x);
                let mut xp = Fp3::zero(); bw6_761_Fp3_sub(&mut xp, &lam_sq, &twox);
                let mut dx = Fp3::zero(); bw6_761_Fp3_sub(&mut dx, x, &xp);
                let mut lam_dx = Fp3::zero(); bw6_761_Fp3_mul(&mut lam_dx, &lam, &dx);
                let mut yp = Fp3::zero(); bw6_761_Fp3_sub(&mut yp, &lam_dx, y);
                G2Aff::Pt(xp, yp)
            }
        }
    }

    pub fn g2_add(P: &G2Aff, Q: &G2Aff) -> G2Aff {
        match (P, Q) {
            (G2Aff::Inf, _) => *Q,
            (_, G2Aff::Inf) => *P,
            (G2Aff::Pt(x1, y1), G2Aff::Pt(x2, y2)) => {
                if fp3_eq(x1, x2) {
                    if fp3_eq(y1, y2) { g2_double(P) }
                    else { G2Aff::Inf }
                } else {
                    let mut dy = Fp3::zero(); bw6_761_Fp3_sub(&mut dy, y2, y1);
                    let mut dx = Fp3::zero(); bw6_761_Fp3_sub(&mut dx, x2, x1);
                    let mut inv_dx = Fp3::zero(); bw6_761_Fp3_inv(&mut inv_dx, &dx);
                    let mut lam = Fp3::zero(); bw6_761_Fp3_mul(&mut lam, &dy, &inv_dx);
                    let mut lam_sq = Fp3::zero(); bw6_761_Fp3_mul(&mut lam_sq, &lam, &lam);
                    let mut tmp = Fp3::zero(); bw6_761_Fp3_sub(&mut tmp, &lam_sq, x1);
                    let mut x3 = Fp3::zero(); bw6_761_Fp3_sub(&mut x3, &tmp, x2);
                    let mut delta = Fp3::zero(); bw6_761_Fp3_sub(&mut delta, x1, &x3);
                    let mut lam_delta = Fp3::zero(); bw6_761_Fp3_mul(&mut lam_delta, &lam, &delta);
                    let mut y3 = Fp3::zero(); bw6_761_Fp3_sub(&mut y3, &lam_delta, y1);
                    G2Aff::Pt(x3, y3)
                }
            }
        }
    }

    pub fn g2_scalar_mul(scalar_be: &[u8], P: &G2Aff) -> G2Aff {
        let mut acc = G2Aff::Inf;
        let mut started = false;
        for &byte in scalar_be {
            for i in 0..8 {
                let bit = (byte >> (7 - i)) & 1;
                if started { acc = g2_double(&acc); }
                if bit == 1 {
                    if started { acc = g2_add(&acc, P); }
                    else { acc = *P; started = true; }
                }
            }
        }
        acc
    }

    // ────────────────────── Hash to curve (stubs) ─────────────────────

    /// Hash to G1 — NOT YET IMPLEMENTED.  Spec mirrors RFC9380 with
    /// SWU + iso_map for BW6-761.  Returns `None` until the verified
    /// Gallina body lands (see [`BW6_761_GroupOps.v::HashToG1_spec`]).
    pub fn hash_to_g1(_msg: &[u8], _dst: &[u8]) -> Option<G1Aff> { None }

    /// Hash to G2 — NOT YET IMPLEMENTED.  Same status as `hash_to_g1`.
    pub fn hash_to_g2(_msg: &[u8], _dst: &[u8]) -> Option<G2Aff> { None }

    // Suppress unused-import warnings for items only used by future code.
    #[allow(dead_code)]
    fn _refs() {
        let _: fn(&mut TFp, u64) = fp_from_word_t;
        let _: fn(&mut TFp) = fp_zero_t;
        let _: fn(&mut TFp) = fp_one_t;
        let _: fn(&mut Fp3) = bw6_761_Fp3_zero;
        let _: fn(&mut Fp3) = bw6_761_Fp3_one;
        let _: fn(&mut Fp3, &Fp3) = bw6_761_Fp3_felem_copy;
    }
}

pub use group::{G1Aff, G2Aff, g1_add, g1_double, g1_neg, g1_scalar_mul,
                 g2_add, g2_double, g2_neg, g2_scalar_mul,
                 hash_to_g1, hash_to_g2};

#[cfg(test)]
mod kat;
