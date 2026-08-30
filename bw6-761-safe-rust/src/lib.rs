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
/// Wires the verified `bw6_761_miller_loop_optimal` (5-symbol
/// canonical Miller-loop body matching gnark-crypto's reference
/// algorithm — see [`BW6_761_MillerLoopOptimal.v`]) into the
/// verified `bw6_final_exp` (Hayashida-style final exponentiation —
/// see [`BW6_761_FinalExp.v`]).
///
/// The optimal-ate Miller loop expects six G2 quantities:
///   q0  = Q                                  (Fp3 ↦ (q0.x, q0.y))
///   q1  = (thirdRootOneG1 · Q.x, −Q.y)        (Fp3 ↦ (q1.x, q1.y))
///   q0Neg = (Q.x, −Q.y)                       (only `q0Neg.y` needed)
///   q1Neg = (q1.x, Q.y)                       (only `q1Neg.y` needed)
/// where `thirdRootOneG1` is the primitive cube root of unity over Fp
/// fixed by gnark.  We construct these inline from the caller's
/// `q.x`, `q.y`, plus the precomputed `third_root_one_g1` constant.
///
/// **Caveat**: the final-exponentiation step consumes 5 Frobenius
/// constants (`gamma_fp3`, `gamma_fp6`, `gamma_fp3_p2`,
/// `gamma_fp6_p2`, `gamma_fp6_p3`) plus the `half_fp = (p+1)/2`
/// constant used inside `g2_double_step`'s halving step.  These are
/// passed as caller-supplied Fp / Fp3 elements so the function is
/// reusable; the canonical BW6-761 values are populated by
/// [`kat`] for the gnark cross-check.
pub fn pairing(
    out: &mut Fp6,
    p: &G1, q: &G2,
    gamma_fp3: &Fp3, gamma_fp6: &Fp3,
    gamma_fp3_p2: &Fp3, gamma_fp6_p2: &Fp3,
    gamma_fp6_p3: &Fp3,
    third_root_one_g1: &TowerFp,
    half_fp: &TowerFp,
) {
    use tower::{bw6_761_miller_loop_optimal,
                bw6_761_Fp3_mul_fp, bw6_761_Fp3_opp,
                bw6_761_Fp3_felem_copy};

    // q1.X = thirdRootOneG1 · q0.X  (Fp3-scaled-by-Fp)
    // q1.Y = −q0.Y
    // q0Neg.Y = −q0.Y      (same as q1.Y, but the Miller loop signature
    //                       expects a separate slot)
    // q1Neg.Y = +q0.Y      (since q1.Y = −q0.Y, −q1.Y = q0.Y)
    let mut q1x = Fp3::zero();
    let mut q1y = Fp3::zero();
    let mut q0ny = Fp3::zero();
    let mut q1ny = Fp3::zero();
    bw6_761_Fp3_mul_fp(&mut q1x, &q.x, third_root_one_g1);
    bw6_761_Fp3_opp(&mut q1y, &q.y);
    bw6_761_Fp3_opp(&mut q0ny, &q.y);
    bw6_761_Fp3_felem_copy(&mut q1ny, &q.y);

    let mut f = Fp6::zero();
    bw6_761_miller_loop_optimal(
        &mut f,
        &p.x, &p.y,
        &q.x, &q.y,
        &q1x, &q1y,
        &q0ny, &q1ny,
        half_fp,
    );
    final_exponentiation(out, &f,
                         gamma_fp3, gamma_fp6,
                         gamma_fp3_p2, gamma_fp6_p2, gamma_fp6_p3);
}

// ─── BW6-761 Final Exponentiation ─────────────────────────────────
//
// gnark-crypto's BW6-761 pairing applies final exponent
//   d = s · (p³-1)(p+1)(p²-p+1)/r,   s = (x₀+1)
// = ((x₀+1) · (p²-p+1)/r) composed with the easy part.
//
// The verified-extracted `tower::bw6_final_exp_hard` body
// implements a SIMPLIFIED Hayashida-style chain that does NOT match
// gnark's Algorithm 4.4 normalization (it doesn't include the s
// cofactor and uses a different addition chain), so its output is a
// valid but distinct pairing value.  To pass the gnark KAT we
// implement gnark's Algorithm 4.4 here in Rust on top of the verified
// Fp6 leaf bodies.  This is the only piece of the pairing pipeline
// not produced by the bedrock2 extractor; see PENDING.md.

#[inline]
fn fp6_set_one(out: &mut Fp6) {
    use tower::{bw6_761_Fp6_zero, bw6_761_from_word};
    bw6_761_Fp6_zero(out);
    bw6_761_from_word(&mut out.c0.c0, 1u64);
}

/// Binary exponentiation of an Fp6 element by an arbitrary u64 scalar
/// (MSB-first square-and-multiply). Used for the small constants
/// `c1=11`, `c2=103` and `(x₀-1)/3 = 3195374304363544576` in
/// gnark's Algorithm 4.4.
fn fp6_pow_u64(out: &mut Fp6, x: &Fp6, exp: u64) {
    use tower::{bw6_761_Fp6_mul, bw6_761_Fp6_square, bw6_761_Fp6_felem_copy};
    if exp == 0 { fp6_set_one(out); return; }
    let bits = 64 - exp.leading_zeros() as i32;
    let mut acc = *x;
    let mut started = false;
    for i in (0..bits).rev() {
        if started {
            let tmp = acc;
            bw6_761_Fp6_square(&mut acc, &tmp);
        }
        let bit = (exp >> i) & 1;
        if bit == 1 {
            if !started {
                bw6_761_Fp6_felem_copy(&mut acc, x);
                started = true;
            } else {
                let tmp = acc;
                bw6_761_Fp6_mul(&mut acc, &tmp, x);
            }
        }
    }
    bw6_761_Fp6_felem_copy(out, &acc);
}

/// Multiplicative inverse on the cyclotomic subgroup (post easy
/// part).  Since we land in ker(p³-1)(p+1), `x · conj(x) = 1`, so
/// `x⁻¹ = conj(x)`.
#[inline]
fn fp6_cyclo_inv(out: &mut Fp6, x: &Fp6) {
    use tower::bw6_fp6_conjugate;
    bw6_fp6_conjugate(out, x);
}

/// x ↦ x^(x₀-1) for x in the cyclotomic subgroup.
/// `x^(x₀-1) = x^x₀ · x⁻¹ = pow_u(x) · conj(x)`.
fn fp6_pow_t_minus_1(out: &mut Fp6, x: &Fp6) {
    use tower::{bw6_fp6_pow_u, bw6_761_Fp6_mul, bw6_fp6_conjugate};
    let mut a = Fp6::zero();
    let mut c = Fp6::zero();
    bw6_fp6_pow_u(&mut a, x);
    bw6_fp6_conjugate(&mut c, x);
    bw6_761_Fp6_mul(out, &a, &c);
}

/// x ↦ x^(x₀+1) = pow_u(x) · x.
fn fp6_pow_t_plus_1(out: &mut Fp6, x: &Fp6) {
    use tower::{bw6_fp6_pow_u, bw6_761_Fp6_mul};
    let mut a = Fp6::zero();
    bw6_fp6_pow_u(&mut a, x);
    bw6_761_Fp6_mul(out, &a, x);
}

/// x ↦ x^((x₀-1)²). Apply `pow_t_minus_1` twice.
fn fp6_pow_t_minus_1_sq(out: &mut Fp6, x: &Fp6) {
    let mut t = Fp6::zero();
    fp6_pow_t_minus_1(&mut t, x);
    fp6_pow_t_minus_1(out, &t);
}

/// x ↦ x^((x₀-1)/3). Binary exp by 3195374304363544576 (62 bits).
fn fp6_pow_t_minus_1_div_3(out: &mut Fp6, x: &Fp6) {
    fp6_pow_u64(out, x, 3195374304363544576u64);
}

/// gnark's full FinalExponentiation (Algorithm 4.4 from
/// https://yelhousni.github.io/phd.pdf), implemented in safe Rust on
/// top of the verified Fp6 leaf bodies.
pub fn final_exponentiation(
    out: &mut Fp6, f: &Fp6,
    gamma_fp3: &Fp3, gamma_fp6: &Fp3,
    gamma_fp3_p2: &Fp3, gamma_fp6_p2: &Fp3,
    gamma_fp6_p3: &Fp3,
) {
    use tower::{bw6_761_Fp6_inv, bw6_761_Fp6_mul, bw6_761_Fp6_square,
                bw6_761_Fp6_felem_copy,
                bw6_fp6_conjugate, bw6_fp6_frob,
                bw6_fp6_frob_p2, bw6_fp6_frob_p3};

    // ─── Easy part: r := f^((p³-1)(p+1)) ───
    // buf := conj(f);
    // f   := inv(f);
    // buf := buf · f;             // = conj(f) / f = f^(p³-1)
    // r   := frob(buf);
    // r   := r · buf;              // = f^((p³-1)(p+1))
    let mut buf = Fp6::zero();
    let mut inv_f = Fp6::zero();
    bw6_fp6_conjugate(&mut buf, f);
    bw6_761_Fp6_inv(&mut inv_f, f);
    let t = buf;
    bw6_761_Fp6_mul(&mut buf, &t, &inv_f);
    let mut r = Fp6::zero();
    bw6_fp6_frob(&mut r, &buf, gamma_fp3, gamma_fp6);
    let t = r;
    bw6_761_Fp6_mul(&mut r, &t, &buf);

    // ─── Hard part (gnark Algorithm 4.4) ───
    // a := r^((x₀-1)²) · Frobenius(r)
    let mut a = Fp6::zero();
    fp6_pow_t_minus_1_sq(&mut a, &r);
    let mut t = Fp6::zero();
    bw6_fp6_frob(&mut t, &r, gamma_fp3, gamma_fp6);
    let aa = a;
    bw6_761_Fp6_mul(&mut a, &aa, &t);

    // b := a^(x₀+1) · conj(r)
    let mut b = Fp6::zero();
    fp6_pow_t_plus_1(&mut b, &a);
    bw6_fp6_conjugate(&mut t, &r);
    let bb = b;
    bw6_761_Fp6_mul(&mut b, &bb, &t);

    // a := a · CycloSquare(a)        // = a · a² = a³
    bw6_761_Fp6_square(&mut t, &a);
    let aa = a;
    bw6_761_Fp6_mul(&mut a, &aa, &t);

    // c := b^((x₀-1)/3)
    let mut c = Fp6::zero();
    fp6_pow_t_minus_1_div_3(&mut c, &b);

    // d := c^(x₀-1)
    let mut d = Fp6::zero();
    fp6_pow_t_minus_1(&mut d, &c);

    // e := d^((x₀-1)²) · d           // = d^((x₀-1)²+1)
    let mut e = Fp6::zero();
    fp6_pow_t_minus_1_sq(&mut e, &d);
    let ee = e;
    bw6_761_Fp6_mul(&mut e, &ee, &d);

    // d := conj(d)
    let dd = d;
    bw6_fp6_conjugate(&mut d, &dd);

    // f' := d · b                    (use `fpfp` for clarity)
    let mut fpfp = Fp6::zero();
    bw6_761_Fp6_mul(&mut fpfp, &d, &b);

    // g := e^(x₀+1) · f'
    let mut g = Fp6::zero();
    fp6_pow_t_plus_1(&mut g, &e);
    let gg = g;
    bw6_761_Fp6_mul(&mut g, &gg, &fpfp);

    // h := g · c
    let mut h = Fp6::zero();
    bw6_761_Fp6_mul(&mut h, &g, &c);

    // i := (g · d)^(x₀+1) · conj(f')
    let mut i = Fp6::zero();
    bw6_761_Fp6_mul(&mut i, &g, &d);
    let ii = i;
    fp6_pow_t_plus_1(&mut i, &ii);
    bw6_fp6_conjugate(&mut t, &fpfp);
    let ii = i;
    bw6_761_Fp6_mul(&mut i, &ii, &t);

    // j := h^c1 · e          (c1 = 11)
    let mut j = Fp6::zero();
    fp6_pow_u64(&mut j, &h, 11u64);
    let jj = j;
    bw6_761_Fp6_mul(&mut j, &jj, &e);

    // k := CycloSquare(j) · j · b · Expc2(i)         (c2 = 103)
    let mut k = Fp6::zero();
    bw6_761_Fp6_square(&mut k, &j);
    let kk = k;
    bw6_761_Fp6_mul(&mut k, &kk, &j);
    let kk = k;
    bw6_761_Fp6_mul(&mut k, &kk, &b);
    fp6_pow_u64(&mut t, &i, 103u64);
    let kk = k;
    bw6_761_Fp6_mul(&mut k, &kk, &t);

    // result := a · k
    bw6_761_Fp6_mul(out, &a, &k);

    // (gnark also does an "early-out if result.Equal(&one)" — we
    // omit that branch since it's a perf hint not a correctness one.)
    let _ = (gamma_fp3_p2, gamma_fp6_p2, gamma_fp6_p3); // silence unused
    // (frob_p2/frob_p3 + their gamma args were used by the
    // verified-extracted hard part; gnark's Algorithm 4.4 only uses
    // Frobenius (= pi^1).  We accept them as args for API stability.)
    let _ = (bw6_fp6_frob_p2, bw6_fp6_frob_p3);
    let _ = bw6_761_Fp6_felem_copy;
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

    /// G1 scalar multiplication in AFFINE coordinates (binary,
    /// MSB-first, double-and-add).  `scalar_be` is the scalar in
    /// big-endian bytes.  NOT constant-time.
    ///
    /// Retained as the differential reference for
    /// [`g1_scalar_mul`], which computes the same function
    /// projectively.  It pays one [`fp_inv`] per doubling and one per
    /// addition — roughly 570 inversions for a 377-bit scalar — so it
    /// is about an order of magnitude slower; see
    /// `examples/bench_g1.rs`.
    pub fn g1_scalar_mul_affine(scalar_be: &[u8], P: &G1Aff) -> G1Aff {
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

    // ──────────── G1 homogeneous projective (RCB, a = 0) ──────────────

    /// Homogeneous projective G1 point `(X : Y : Z)`; `Z = 0` is the
    /// identity and the affine image is `(X/Z, Y/Z)`.
    ///
    /// HOMOGENEOUS, not Jacobian.  This is the coordinate system of
    /// `ladderstep_gallina` in
    /// `src/Bedrock/Group/CurveAdd/CurveAdd.v` and of
    /// `rcb_double_a0_gallina` in
    /// `src/Bedrock/Group/CurveAdd/PointDoubleA0.v`; the two bodies
    /// below are line-by-line transcriptions of those, so the Gallina
    /// equality `rcb_double_a0_eq_ladderstep` (proved in
    /// `PointDoubleA0.v`) is a statement about exactly this code.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct G1Proj { pub x: TFp, pub y: TFp, pub z: TFp }

    /// `3b` for BW6-761 G1: the curve is `y² = x³ − 1`, so `b = −1`
    /// and `3b = −3`.  (`kat.rs::g1_curve_b_is_minus_one` checks that
    /// the generator satisfies `y² = x³ − 1`.)
    pub fn g1_three_b() -> TFp {
        let mut three = TFp::zero(); fp_from_word_t(&mut three, 3u64);
        let mut out = TFp::zero(); fp_opp_t(&mut out, &three);
        out
    }

    /// Complete projective addition for `a = 0` (Renes–Costello–Batina
    /// 2015, Algorithm 7): 12 M + 2 m_3b + 19 add/sub.
    ///
    /// Transcribed line by line from `ladderstep_gallina`
    /// (`src/Bedrock/Group/CurveAdd/CurveAdd.v`), which
    /// `BN254_wNAF_Laws.bn254_curve_add_is_cadd` proves equal to
    /// fiat-crypto's `Projective.add`.  Complete: no special case for
    /// the identity or for `P + (−P)`.
    pub fn g1_proj_add(P: &G1Proj, Q: &G1Proj, b3: &TFp) -> G1Proj {
        let (x1, y1, z1) = (P.x, P.y, P.z);
        let (x2, y2, z2) = (Q.x, Q.y, Q.z);
        let mut u = TFp::zero();
        let mut t0 = TFp::zero(); fp_mul_t(&mut t0, &x1, &x2);
        let mut t1 = TFp::zero(); fp_mul_t(&mut t1, &y1, &y2);
        let mut t2 = TFp::zero(); fp_mul_t(&mut t2, &z1, &z2);
        let mut t3 = TFp::zero(); fp_add_t(&mut t3, &x1, &y1);
        let mut t4 = TFp::zero(); fp_add_t(&mut t4, &x2, &y2);
        fp_mul_t(&mut u, &t3, &t4); t3 = u;
        fp_add_t(&mut u, &t0, &t1); t4 = u;
        fp_sub_t(&mut u, &t3, &t4); t3 = u;
        fp_add_t(&mut u, &x1, &z1); t4 = u;
        let mut t5 = TFp::zero(); fp_add_t(&mut t5, &x2, &z2);
        fp_mul_t(&mut u, &t4, &t5); t4 = u;
        fp_add_t(&mut u, &t0, &t2); t5 = u;
        fp_sub_t(&mut u, &t4, &t5); t4 = u;
        fp_add_t(&mut u, &y1, &z1); t5 = u;
        let mut xo = TFp::zero(); fp_add_t(&mut xo, &y2, &z2);
        fp_mul_t(&mut u, &t5, &xo); t5 = u;
        fp_add_t(&mut u, &t1, &t2); xo = u;
        fp_sub_t(&mut u, &t5, &xo); t5 = u;
        let mut zo = TFp::zero(); fp_mul_t(&mut zo, b3, &t2);
        fp_sub_t(&mut u, &t1, &zo); xo = u;
        fp_add_t(&mut u, &zo, &t1); zo = u;
        let mut yo = TFp::zero(); fp_mul_t(&mut yo, &xo, &zo);
        fp_add_t(&mut u, &t0, &t0); t1 = u;
        fp_add_t(&mut u, &t1, &t0); t1 = u;
        fp_mul_t(&mut u, b3, &t4); t4 = u;
        fp_mul_t(&mut u, &t1, &t4); t0 = u;
        fp_add_t(&mut u, &yo, &t0); yo = u;
        fp_mul_t(&mut u, &t5, &t4); t0 = u;
        fp_mul_t(&mut u, &t3, &xo); xo = u;
        fp_sub_t(&mut u, &xo, &t0); xo = u;
        fp_mul_t(&mut u, &t3, &t1); t0 = u;
        fp_mul_t(&mut u, &t5, &zo); zo = u;
        fp_add_t(&mut u, &zo, &t0); zo = u;
        G1Proj { x: xo, y: yo, z: zo }
    }

    // Complete projective DOUBLING for `a = 0` (Renes–Costello–Batina
    // 2015, Algorithm 9): 8 M + 1 m_3b + 9 add/sub — 18 field
    // operations against the 33 of `g1_proj_add(P, P)`, and 9
    // multiplications against 14.
    //
    // There is no hand-written `g1_proj_double` here any more.  The
    // shipping body is the ROCQ-EMITTED
    // `crate::g1_double_a0_extracted::g1_proj_double_extracted`,
    // printed by `rs_body_extract` from
    // `src/Bedrock/Curve/CurveDoubleA0RustCmd.v`.  It takes no `b3`
    // argument: `3b` is baked into the emitted text as the `cB3` byte
    // constant, `mont_bytes 12 bw6_761_m ((3*b) mod m)` with `b = m−1`.
    //
    // The hand transcription it replaced agreed with it on every input
    // tested (`kat::g1_alg9_extracted_matches_handwritten`) and
    // measured 1.1% SLOWER (7040 against 6954 cycles;
    // `examples/bench_double_a0.rs`), so per the repo's
    // verified-extraction-first policy it was removed from the
    // shipping surface.  It survives as the test oracle
    // `kat::g1_proj_double_handwritten`, which is what keeps that
    // differential test meaningful.

    /// The projective identity `(0 : 1 : 0)`.
    pub fn g1_proj_inf() -> G1Proj {
        let mut one = TFp::zero(); fp_one_t(&mut one);
        G1Proj { x: TFp::zero(), y: one, z: TFp::zero() }
    }

    pub fn g1_to_proj(P: &G1Aff) -> G1Proj {
        match P {
            G1Aff::Inf => g1_proj_inf(),
            G1Aff::Pt(x, y) => {
                let mut one = TFp::zero(); fp_one_t(&mut one);
                G1Proj { x: *x, y: *y, z: one }
            }
        }
    }

    /// Projective → affine.  The ONE inversion of a scalar
    /// multiplication.
    pub fn g1_from_proj(P: &G1Proj) -> G1Aff {
        if fp_is_zero(&P.z) { return G1Aff::Inf; }
        let mut zi = TFp::zero(); fp_inv_t(&mut zi, &P.z);
        let mut x = TFp::zero(); fp_mul_t(&mut x, &P.x, &zi);
        let mut y = TFp::zero(); fp_mul_t(&mut y, &P.y, &zi);
        G1Aff::Pt(x, y)
    }

    /// G1 scalar multiplication (binary, MSB-first, double-and-add),
    /// carried out in homogeneous projective coordinates with a single
    /// inversion at the end.  `scalar_be` is the scalar in big-endian
    /// bytes.  NOT constant-time: the addition is still branched on the
    /// scalar bit (the arithmetic itself is uniform, so a `select`
    /// would close that).
    ///
    /// Same function as [`g1_scalar_mul_affine`]; `kat.rs`'s
    /// `g1_scalar_mul_projective_matches_affine` checks that
    /// differentially.  Because Algorithms 7 and 9 are complete, the
    /// `started` flag of the affine version is gone: doubling the
    /// identity and adding to the identity are handled by the formulas.
    pub fn g1_scalar_mul(scalar_be: &[u8], P: &G1Aff) -> G1Aff {
        let b3 = g1_three_b();
        let pp = g1_to_proj(P);
        let mut acc = g1_proj_inf();
        for &byte in scalar_be {
            for i in 0..8 {
                let bit = (byte >> (7 - i)) & 1;
                acc = crate::g1_double_a0_extracted::g1_proj_double_extracted(&acc);
                if bit == 1 { acc = g1_proj_add(&acc, &pp, &b3); }
            }
        }
        g1_from_proj(&acc)
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

/// Byte-ABI shims (`*mut u8` / `*const u8` over `[u8; 96]` slots) for
/// the Rocq-emitted bodies, over the crate's own verified leaves.
pub mod extracted_leaves;
/// Rocq-emitted RCB Algorithm 9 complete doubling (a = 0).
pub mod g1_double_a0_extracted;

pub use g1_double_a0_extracted::g1_proj_double_extracted;

pub use group::{G1Aff, G1Proj, G2Aff, g1_add, g1_double, g1_neg,
                 g1_scalar_mul, g1_scalar_mul_affine,
                 g1_proj_add, g1_proj_inf, g1_three_b,
                 g1_to_proj, g1_from_proj,
                 g2_add, g2_double, g2_neg, g2_scalar_mul,
                 hash_to_g1, hash_to_g2};

#[cfg(test)]
mod kat;
