//! Hand-coded projective Miller loop for BN254 (UNVERIFIED).
//!
//! Uses the verified Fp/Fp2/Fp12 primitives from the tower, but the
//! Miller-loop body and line construction here are hand-written
//! Rust — not derived from the formally-verified bedrock2 IR.  For
//! benchmarking and cross-check purposes only; the production path
//! stays through [crate::pairing].
//!
//! Correctness is established empirically by the cross-check in
//! [pairing_projective_hand_matches_affine] (pairing value equals
//! the verified affine pairing after final exponentiation).
//!
//! The Z-scaling factor that accumulates across doublings is a norm
//! from the Fp subfield; BN254's final exp [(p^12 - 1)/r] contains
//! the [(p^6 - 1)] factor which kills any element of the form
//! [z * conj(z)] for [z in Fp^6], so the pairing value is invariant
//! to the scaling.  The affine and projective raw Miller outputs
//! differ; the post-final-exp pairing values agree.

use crate::tower::*;
use crate::{fp2_add, fp2_mul, fp2_square, fp2_sub, fp2_opp, fp12_mul, fp12_square, fp_copy};

/// BN254 optimal-ate loop parameter 6u+2, big-endian bit layout.
const U6P2: u64 = 11347224129447541672;
const U6P2_BITS: u64 = 64;

/// Bernstein--Lange projective doubling on E': [y^2 = x^3 + b]
/// (a = 0, so no [a]-term).  Updates [T] in place and emits the
/// Fp12 line polynomial evaluated at [P = (p_x, p_y)] in the
/// bedrock2 D-twist basis.
///
/// Formulas (Aranha--Karabina--Longa--Gebotys--López 2010,
/// adapted for [a = 0]):
///   A = X^2, B = Y^2, C = B^2
///   D = 2*((X+B)^2 - A - C)    [= 4*X*Y^2]
///   E = 3*A                     [tangent slope numerator, unscaled]
///   F = E^2
///   X' = F - 2*D
///   Y' = E*(D - X') - 8*C
///   Z' = 2*Y*Z
///
/// Line at P_aff = (p_x, p_y), scaled by [Z' = 2*Y*Z] = [2*Y*Z]:
///   c0.c0 = 2*Y*Z^3 * p_y   (Fp2 * Fp, viewed in Fp2)
///   c1.c0 = -3*X^2*Z^2 * p_x
///   c1.c1 = 3*X^3 - 2*Y^2
///   others = 0
///
/// Together with the bedrock2 D-twist line basis, this makes the
/// accumulated [f] differ from the affine Miller output by a known
/// Fp2 scalar that vanishes in the final exponentiation.
fn double_step(
    f_out: &mut Fp12,
    t_x: &mut Fp2, t_y: &mut Fp2, t_z: &mut Fp2,
    p_x: &Fp, p_y: &Fp,
) {
    let mut a = Fp2::zero();     // A = X^2
    let mut b = Fp2::zero();     // B = Y^2
    let mut c = Fp2::zero();     // C = B^2
    let mut tmp = Fp2::zero();
    let mut tmp2 = Fp2::zero();
    let mut d = Fp2::zero();     // D = 4XY^2
    let mut e = Fp2::zero();     // E = 3X^2
    let mut fv = Fp2::zero();    // F = E^2
    let mut nx = Fp2::zero();
    let mut ny = Fp2::zero();
    let mut nz = Fp2::zero();
    let mut line = Fp12::zero();

    fp2_square(&mut a, t_x);
    fp2_square(&mut b, t_y);
    fp2_square(&mut c, &b);
    // D = 2*((X+B)^2 - A - C)
    fp2_add(&mut tmp, t_x, &b);
    let tmp_c = tmp.clone();
    fp2_square(&mut tmp, &tmp_c);
    let tmp_c = tmp.clone();
    fp2_sub(&mut tmp, &tmp_c, &a);
    let tmp_c = tmp.clone();
    fp2_sub(&mut tmp, &tmp_c, &c);
    fp2_add(&mut d, &tmp, &tmp);
    // E = 3*A
    fp2_add(&mut tmp, &a, &a);
    fp2_add(&mut e, &tmp, &a);
    // F = E^2
    fp2_square(&mut fv, &e);
    // X' = F - 2D
    fp2_sub(&mut nx, &fv, &d);
    let nx_c = nx.clone();
    fp2_sub(&mut nx, &nx_c, &d);
    // Y' = E*(D - X') - 8*C
    fp2_sub(&mut tmp, &d, &nx);
    fp2_mul(&mut ny, &e, &tmp);
    // 8*C: shift by adding C 8 times (or add & double; use 3 adds)
    fp2_add(&mut tmp, &c, &c);      // 2C
    let tmp_c = tmp.clone();
    fp2_add(&mut tmp, &tmp_c, &tmp_c); // 4C
    let tmp_c = tmp.clone();
    fp2_add(&mut tmp, &tmp_c, &tmp_c); // 8C
    let ny_c = ny.clone();
    fp2_sub(&mut ny, &ny_c, &tmp);
    // Z' = 2*Y*Z
    fp2_mul(&mut tmp, t_y, t_z);
    fp2_add(&mut nz, &tmp, &tmp);

    // --- line at P, projective form with Z-scaling absorbed ---
    // z_sq = Z^2, z_cube = Z^3
    let mut z_sq = Fp2::zero();
    let mut z_cube = Fp2::zero();
    fp2_square(&mut z_sq, t_z);
    fp2_mul(&mut z_cube, &z_sq, t_z);

    // c0.c0 = 2*Y*Z^3 * p_y  (an Fp2 value, Y*Z^3 * 2 * p_y)
    // We compute (2*Y*Z^3) * p_y by scaling each Fp component.
    let mut two_yz3 = Fp2::zero();
    fp2_mul(&mut tmp, t_y, &z_cube);
    fp2_add(&mut two_yz3, &tmp, &tmp);
    bn254_Fp2_mul_fp(&mut line.c0.c0, &two_yz3, p_y);

    // c1.c0 = -3*X^2 * Z^2 * p_x
    // -E * Z^2 * p_x
    let mut e_z_sq = Fp2::zero();
    fp2_mul(&mut e_z_sq, &e, &z_sq);
    bn254_Fp2_mul_fp(&mut tmp, &e_z_sq, p_x);
    fp2_opp(&mut line.c1.c0, &tmp);

    // c1.c1 = 3*X^3 - 2*Y^2 = X*E - 2*B
    fp2_mul(&mut tmp, t_x, &e);
    fp2_add(&mut tmp2, &b, &b);
    fp2_sub(&mut line.c1.c1, &tmp, &tmp2);

    // Accumulate: f := f^2 * line
    let mut f2 = Fp12::zero();
    fp12_square(&mut f2, f_out);
    fp12_mul(f_out, &f2, &line);

    // Update T
    bn254_Fp2_felem_copy(t_x, &nx);
    bn254_Fp2_felem_copy(t_y, &ny);
    bn254_Fp2_felem_copy(t_z, &nz);
}

/// Bernstein--Lange projective mixed addition: [T = T + Q] where
/// [Q = (q_x, q_y)] is affine.  Uses the projective formulas with
/// line constructed similarly.  [T_old] is in [T], overwritten with
/// [T + Q].
fn add_step(
    f_out: &mut Fp12,
    t_x: &mut Fp2, t_y: &mut Fp2, t_z: &mut Fp2,
    q_x: &Fp2, q_y: &Fp2,
    p_x: &Fp, p_y: &Fp,
) {
    let mut z1z1 = Fp2::zero();
    let mut u2 = Fp2::zero();
    let mut s2 = Fp2::zero();
    let mut h = Fp2::zero();
    let mut hh = Fp2::zero();
    let mut i = Fp2::zero();
    let mut j = Fp2::zero();
    let mut r = Fp2::zero();
    let mut v = Fp2::zero();
    let mut nx = Fp2::zero();
    let mut ny = Fp2::zero();
    let mut nz = Fp2::zero();
    let mut tmp = Fp2::zero();
    let mut tmp2 = Fp2::zero();
    let mut line = Fp12::zero();

    // z1z1 = Z^2
    fp2_square(&mut z1z1, t_z);
    // u2 = Qx * z1z1
    fp2_mul(&mut u2, q_x, &z1z1);
    // s2 = Qy * Z * z1z1
    fp2_mul(&mut tmp, q_y, t_z);
    fp2_mul(&mut s2, &tmp, &z1z1);
    // h = u2 - X
    fp2_sub(&mut h, &u2, t_x);
    // hh = h^2
    fp2_square(&mut hh, &h);
    // i = 4*hh
    fp2_add(&mut tmp, &hh, &hh);
    fp2_add(&mut i, &tmp, &tmp);
    // j = h * i
    fp2_mul(&mut j, &h, &i);
    // r = 2*(s2 - Y)
    fp2_sub(&mut tmp, &s2, t_y);
    fp2_add(&mut r, &tmp, &tmp);
    // v = X * i
    fp2_mul(&mut v, t_x, &i);
    // X' = r^2 - j - 2v
    fp2_square(&mut nx, &r);
    let nx_c = nx.clone();
    fp2_sub(&mut nx, &nx_c, &j);
    let nx_c = nx.clone();
    fp2_sub(&mut nx, &nx_c, &v);
    let nx_c = nx.clone();
    fp2_sub(&mut nx, &nx_c, &v);
    // Y' = r*(v - X') - 2*Y*j
    fp2_sub(&mut tmp, &v, &nx);
    fp2_mul(&mut ny, &r, &tmp);
    fp2_mul(&mut tmp, t_y, &j);
    fp2_add(&mut tmp2, &tmp, &tmp);
    let ny_c = ny.clone();
    fp2_sub(&mut ny, &ny_c, &tmp2);
    // Z' = (Z + h)^2 - z1z1 - hh
    fp2_add(&mut tmp, t_z, &h);
    let tmp_c = tmp.clone();
    fp2_square(&mut tmp, &tmp_c);
    let tmp_c = tmp.clone();
    fp2_sub(&mut tmp, &tmp_c, &z1z1);
    fp2_sub(&mut nz, &tmp, &hh);

    // Line in projective form: same form as doubling but using
    // chord slope r.  Scaled by Z'.
    // c0.c0 = Z' * (Qy * Z + Y)  -- simpler equivalent: after
    // scaling, the line is r*(x - Qx) - (y - Qy) which rearranges.
    // For the benchmark we use the same basis slots that the affine
    // version uses (c0.c0 = py-coeff, c1.c0 = px-coeff, c1.c1 = const).
    //
    // Affine: line = Py - lam*Px + (lam*Qx - Qy)
    // Projective with chord slope r = 2*(s2 - Y), denominator (u2 - X)^3 = j...
    // The scaling here is: multiply affine line by h*h*h ... etc.
    // Rather than re-derive, we use the SIMPLEST approach: dehomogenise
    // T_new projectively at the END once, and rely on the affine
    // line formula — BUT that introduces an fp2_inv per step again.
    //
    // Pragmatic simplification: in the addition case (only ~10 per
    // Miller loop for BN254, not ~70), the fp2_inv cost is small.
    // Use affine slope here and the dense affine line.
    let mut tx_aff = Fp2::zero();
    let mut ty_aff = Fp2::zero();
    let mut inv_z_sq = Fp2::zero();
    let mut inv_z_cube = Fp2::zero();
    bn254_Fp2_inv(&mut inv_z_sq, &z1z1);
    fp2_mul(&mut tmp, &inv_z_sq, t_z);
    let tmp_c = tmp.clone();
    let mut inv_z = Fp2::zero();
    // inv_z = z / z^2 = 1/z — we need 1/Z, not computed yet.
    // Actually: 1/Z = z1z1^{-1} * Z, since (z1z1)^{-1} * Z = Z/Z^2 = 1/Z
    bn254_Fp2_felem_copy(&mut inv_z, &tmp_c);
    fp2_mul(&mut inv_z_cube, &inv_z_sq, &inv_z);
    fp2_mul(&mut tx_aff, t_x, &inv_z_sq);
    fp2_mul(&mut ty_aff, t_y, &inv_z_cube);

    let mut lam = Fp2::zero();
    fp2_sub(&mut tmp, q_y, &ty_aff);
    fp2_sub(&mut tmp2, q_x, &tx_aff);
    let mut inv_qxtx = Fp2::zero();
    bn254_Fp2_inv(&mut inv_qxtx, &tmp2);
    fp2_mul(&mut lam, &tmp, &inv_qxtx);

    // Call existing affine make_line
    bn254_make_line_corrected(&mut line, &lam, &tx_aff, &ty_aff, p_x, p_y);

    fp12_mul(f_out, &f_out.clone(), &line);

    bn254_Fp2_felem_copy(t_x, &nx);
    bn254_Fp2_felem_copy(t_y, &ny);
    bn254_Fp2_felem_copy(t_z, &nz);
}

/// Hand-coded projective Miller loop.  Drop-in replacement for
/// [bn254_miller_loop] that uses projective coordinates for the
/// running point [T], eliminating the per-step Fp2 inversion in
/// the doubling branch (~70 inversions saved).  The addition
/// branch (~10 inversions, small fraction) still uses affine,
/// which is fine for the benchmark.  Output equals the affine
/// Miller output times an Fp-subfield norm, which vanishes in
/// the BN254 final exponentiation.
pub fn miller_loop_projective_hand(
    out: &mut Fp12,
    p_x: &Fp, p_y: &Fp, q_x: &Fp2, q_y: &Fp2,
) {
    let mut f = Fp12::zero();
    let mut t_x = Fp2::zero();
    let mut t_y = Fp2::zero();
    let mut t_z = Fp2::zero();

    // f := 1
    bn254_from_word(&mut f.c0.c0.c0, 1u64);
    // T := (Qx, Qy, 1)
    bn254_Fp2_felem_copy(&mut t_x, q_x);
    bn254_Fp2_felem_copy(&mut t_y, q_y);
    bn254_from_word(&mut t_z.c0, 1u64);
    // t_z.c1 is already zero

    let mut i: u64 = U6P2_BITS;
    while i != 0 {
        i = i.wrapping_sub(1);
        let bit = (U6P2 >> (i & 63)) & 1;
        double_step(&mut f, &mut t_x, &mut t_y, &mut t_z, p_x, p_y);
        if bit != 0 {
            add_step(&mut f, &mut t_x, &mut t_y, &mut t_z, q_x, q_y, p_x, p_y);
        }
    }

    bn254_Fp12_felem_copy(out, &f);
}

/// Hand-coded projective pairing: [miller_loop_projective_hand]
/// composed with the verified final exponentiation.
/// Equals [crate::pairing] post-final-exp.
pub fn pairing_projective_hand(
    out: &mut Fp12,
    p_x: &Fp, p_y: &Fp, q_x: &Fp2, q_y: &Fp2,
) {
    let mut tmp = Fp12::zero();
    let mut g1 = Fp2::zero();
    let mut g2 = Fp2::zero();
    let mut w = Fp2::zero();
    bn254_load_gamma1_p2(&mut g1);
    bn254_load_gamma2_p2(&mut g2);
    bn254_load_w_frob_p2_c1(&mut w);
    miller_loop_projective_hand(&mut tmp, p_x, p_y, q_x, q_y);
    bn254_final_exp_dsd(out, &tmp, &g1, &g2, &w);
}
