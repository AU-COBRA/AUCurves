//! BLS12-381 pairing — safe Rust tower over verified bedrock2 leaves.
//!
//! Architecture mirrors bn254-safe-rust:
//!   tower functions (Fp2→Fp6→Fp12→pairing): safe Rust, 0 unsafe
//!   leaf Fp ops: thin unsafe wrappers → assembly (or stubs)
//!
//! Differences from BN254:
//!   - 6 limbs (381-bit prime) instead of 4 (254-bit)
//!   - xi = 1 + u (BLS12 nonresidue) instead of 9 + u
//!   - optimal ate Miller loop parameter |u| with Hamming weight 6
//!   - DSD final exponentiation specific to BLS12

#![allow(non_snake_case, non_camel_case_types)]
#![allow(unused_assignments, unused_variables, unused_mut, unused_parens, dead_code)]

mod tower {
    include!(concat!(env!("CARGO_MANIFEST_DIR"), "/generated/bls12_safe_tower.rs"));
}

mod stubs;

/// Byte-ABI shims (`*mut u8` / `*const u8` over the leaf byte slots)
/// for the Rocq-emitted bodies, over the crate's own leaves.
pub mod extracted_leaves;
/// Rocq-emitted RCB Algorithm 9 complete doubling (a = 0).
pub mod g1_double_a0_extracted;
#[cfg(test)]
mod g1_double_a0_test;

pub mod shake128;

pub use tower::{Fp, Fp2, Fp6, Fp12};

pub fn fp_add(out: &mut Fp, x: &Fp, y: &Fp) { tower::bls12_add(out, x, y) }
pub fn fp_sub(out: &mut Fp, x: &Fp, y: &Fp) { tower::bls12_sub(out, x, y) }
pub fn fp_mul(out: &mut Fp, x: &Fp, y: &Fp) { tower::bls12_mul(out, x, y) }
pub fn fp_square(out: &mut Fp, x: &Fp) { tower::bls12_square(out, x) }
pub fn fp_opp(out: &mut Fp, x: &Fp) { tower::bls12_opp(out, x) }
pub fn fp2_mul(out: &mut Fp2, x: &Fp2, y: &Fp2) { tower::bls12_Fp2_mul(out, x, y) }
pub fn fp2_square(out: &mut Fp2, x: &Fp2) { tower::bls12_Fp2_square(out, x) }
pub fn fp2_inv(out: &mut Fp2, x: &Fp2) { tower::bls12_Fp2_inv(out, x) }
pub fn fp2_add(out: &mut Fp2, x: &Fp2, y: &Fp2) { tower::bls12_Fp2_add(out, x, y) }
pub fn fp2_sub(out: &mut Fp2, x: &Fp2, y: &Fp2) { tower::bls12_Fp2_sub(out, x, y) }
pub fn fp6_mul(out: &mut Fp6, x: &Fp6, y: &Fp6) { tower::bls12_Fp6_mul(out, x, y) }
pub fn fp6_inv(out: &mut Fp6, x: &Fp6) { tower::bls12_Fp6_inv(out, x) }
pub fn fp12_square(out: &mut Fp12, x: &Fp12) { tower::bls12_Fp12_square(out, x) }
pub fn fp12_mul(out: &mut Fp12, x: &Fp12, y: &Fp12) { tower::bls12_Fp12_mul(out, x, y) }
pub fn fp12_inv(out: &mut Fp12, x: &Fp12) { tower::bls12_Fp12_inv(out, x) }

/// Encode a small integer into Montgomery form.
pub fn fp_from_word(out: &mut Fp, w: u64) {
    tower::bls12_from_word(out, w);
}

pub fn pairing(out: &mut Fp12, p_x: &Fp, p_y: &Fp, q_x: &Fp2, q_y: &Fp2) {
    tower::bls12_pairing(out, p_x, p_y, q_x, q_y)
}

pub fn miller_loop(out: &mut Fp12, p_x: &Fp, p_y: &Fp, q_x: &Fp2, q_y: &Fp2) {
    tower::bls12_miller_loop(out, p_x, p_y, q_x, q_y)
}

/// Projective Miller loop (uses Fp12_mul_by_024 sparse multiply).
///
/// **UNVERIFIED**: the bedrock2 body `bls12_miller_loop_proj` (defined in
/// `src/Bedrock/Field/Synthesis/Examples/BLS12_Pairing.v:1428`) has no
/// matching `spec_of_bls12_miller_loop_proj` / `bls12_miller_loop_proj_ok`
/// theorem in `BLS12_MillerLoop.v` (which Qed's only the affine
/// `bls12_miller_loop`).  Observed to disagree with `pairing` (affine)
/// on synthetic inputs — see
/// `~/Claude/catcrypt-private/docs/kzg-aucurves-pairing-perf-notes.md`
/// "pairing_proj upstream-bug investigation" punch-list item.  Do not
/// rely on this in verified contexts.
#[deprecated(note = "unverified — bedrock2 body has no Qed'd correctness theorem; use miller_loop (affine) instead")]
pub fn miller_loop_proj(out: &mut Fp12, p_x: &Fp, p_y: &Fp, q_x: &Fp2, q_y: &Fp2) {
    tower::bls12_miller_loop_proj(out, p_x, p_y, q_x, q_y)
}

/// Final exponentiation on an Fp12 value (typically a Miller-loop output).
///
/// Thin wrapper around the verified `tower::bls12_final_exp` that loads
/// the gamma / frobenius constants. Exposed so callers can implement
/// pairing-equality checks as `final_exp(m1 * m2^{-1}) == Fp12::one()`
/// (one final-exp instead of two — the same shortcut blst's
/// `blst_fp12_finalverify` uses).
pub fn final_exp(out: &mut Fp12, f: &Fp12) {
    let mut g1p2 = Fp2::zero();
    let mut g2p2 = Fp2::zero();
    let mut wfp2 = Fp2::zero();
    tower::bls12_load_gamma1_p2(&mut g1p2);
    tower::bls12_load_gamma2_p2(&mut g2p2);
    tower::bls12_load_w_frob_p2_c1(&mut wfp2);
    tower::bls12_final_exp(out, f, &g1p2, &g2p2, &wfp2);
}

/// Pairing using the projective miller loop variant.
///
/// **UNVERIFIED** — same gap as [`miller_loop_proj`]: the bedrock2 body
/// is in tree but has no `_ok` theorem and disagrees with the affine
/// `pairing` on synthetic inputs.  Use [`pairing`] in verified contexts.
#[deprecated(note = "unverified — calls miller_loop_proj which has no Qed'd correctness theorem; use pairing (affine) instead")]
#[allow(deprecated)]
pub fn pairing_proj(out: &mut Fp12, p_x: &Fp, p_y: &Fp, q_x: &Fp2, q_y: &Fp2) {
    let mut tmp = Fp12::zero();
    let mut g1p2 = Fp2::zero();
    let mut g2p2 = Fp2::zero();
    let mut wfp2 = Fp2::zero();
    tower::bls12_load_gamma1_p2(&mut g1p2);
    tower::bls12_load_gamma2_p2(&mut g2p2);
    tower::bls12_load_w_frob_p2_c1(&mut wfp2);
    tower::bls12_miller_loop_proj(&mut tmp, p_x, p_y, q_x, q_y);
    tower::bls12_final_exp(out, &tmp, &g1p2, &g2p2, &wfp2);
}

#[cfg(test)]
mod tests {
    use super::*;

    /// 1 in BLS12-381 Montgomery form (= R mod p, R = 2^384).
    pub(crate) const MONT_ONE: Fp = Fp([
        0x760900000002fffd,
        0xebf4000bc40c0002,
        0x5f48985753c758ba,
        0x77ce585370525745,
        0x5c071a97a256ec6d,
        0x15f65ec3fa80e493,
    ]);

    pub(crate) fn mont_of(w: u64) -> Fp {
        unsafe extern "C" {
            fn _bls12_from_word(o: *mut u64, w: u64);
        }
        let mut x = Fp::zero();
        unsafe { _bls12_from_word(x.0.as_mut_ptr(), w); }
        x
    }

    #[test]
    fn test_mont_mul_3_times_5_is_15() {
        unsafe extern "C" {
            fn _bls12_from_word(o: *mut u64, w: u64);
            fn _bls12_mul(o: *mut u64, x: *const u64, y: *const u64);
        }
        unsafe {
            let mut three = [0u64; 6];
            let mut five = [0u64; 6];
            let mut fifteen_expected = [0u64; 6];
            let mut fifteen_actual = [0u64; 6];
            _bls12_from_word(three.as_mut_ptr(), 3);
            _bls12_from_word(five.as_mut_ptr(), 5);
            _bls12_from_word(fifteen_expected.as_mut_ptr(), 15);
            _bls12_mul(fifteen_actual.as_mut_ptr(), three.as_ptr(), five.as_ptr());
            assert_eq!(fifteen_expected, fifteen_actual);
        }
    }

    #[test]
    fn test_fp_add_disjoint() {
        let a = Fp([1, 2, 3, 4, 5, 6]);
        let b = Fp([10, 20, 30, 40, 50, 60]);
        let mut c = Fp::zero();
        fp_add(&mut c, &a, &b);
        assert_eq!(c.0, [11, 22, 33, 44, 55, 66]);
    }

    #[test]
    fn test_fp2_mul_one_one_is_one() {
        let one_fp2 = Fp2 { c0: MONT_ONE, c1: Fp::zero() };
        let mut out = Fp2::zero();
        tower::bls12_Fp2_mul(&mut out, &one_fp2, &one_fp2);
        assert_eq!(out.c0, MONT_ONE);
        assert_eq!(out.c1, Fp::zero());
    }

    #[test]
    fn test_fp6_mul_inv() {
        let three = mont_of(3);
        let four  = mont_of(4);
        let five  = mont_of(5);
        let six   = mont_of(6);
        let seven = mont_of(7);
        let a = Fp6 {
            c0: Fp2 { c0: three, c1: four },
            c1: Fp2 { c0: five,  c1: six  },
            c2: Fp2 { c0: MONT_ONE, c1: three },
        };
        let b = Fp6 {
            c0: Fp2 { c0: five,  c1: MONT_ONE },
            c1: Fp2 { c0: three, c1: four     },
            c2: Fp2 { c0: six,   c1: seven    },
        };
        let mut ab = Fp6::zero();
        tower::bls12_Fp6_mul(&mut ab, &a, &b);
        let mut b_inv = Fp6::zero();
        tower::bls12_Fp6_inv(&mut b_inv, &b);
        let mut result = Fp6::zero();
        tower::bls12_Fp6_mul(&mut result, &ab, &b_inv);
        assert_eq!(result.c0.c0, a.c0.c0);
        assert_eq!(result.c0.c1, a.c0.c1);
        assert_eq!(result.c1.c0, a.c1.c0);
        assert_eq!(result.c1.c1, a.c1.c1);
        assert_eq!(result.c2.c0, a.c2.c0);
        assert_eq!(result.c2.c1, a.c2.c1);
    }

    #[test]
    fn test_fp12_mul_inv() {
        let three = mont_of(3); let four = mont_of(4); let five = mont_of(5);
        let six = mont_of(6); let seven = mont_of(7);
        let a = Fp12 {
            c0: Fp6 {
                c0: Fp2 { c0: three, c1: four },
                c1: Fp2 { c0: five,  c1: six  },
                c2: Fp2 { c0: MONT_ONE, c1: three },
            },
            c1: Fp6 {
                c0: Fp2 { c0: four, c1: five },
                c1: Fp2 { c0: six,  c1: MONT_ONE },
                c2: Fp2 { c0: three, c1: six },
            },
        };
        let b = Fp12 {
            c0: Fp6 {
                c0: Fp2 { c0: five, c1: MONT_ONE },
                c1: Fp2 { c0: three, c1: four },
                c2: Fp2 { c0: six,  c1: five },
            },
            c1: Fp6 {
                c0: Fp2 { c0: MONT_ONE, c1: six },
                c1: Fp2 { c0: four, c1: three },
                c2: Fp2 { c0: five, c1: seven },
            },
        };
        let mut ab = Fp12::zero();
        tower::bls12_Fp12_mul(&mut ab, &a, &b);
        let mut b_inv = Fp12::zero();
        tower::bls12_Fp12_inv(&mut b_inv, &b);
        let mut result = Fp12::zero();
        tower::bls12_Fp12_mul(&mut result, &ab, &b_inv);
        assert_eq!(result.c0.c0.c0, a.c0.c0.c0);
        assert_eq!(result.c1.c2.c1, a.c1.c2.c1);
    }

    #[test]
    fn test_pairing_runs() {
        // Smoke test only — pairing on degenerate inputs may not be meaningful.
        let p_x = Fp([1, 0, 0, 0, 0, 0]);
        let p_y = Fp([2, 0, 0, 0, 0, 0]);
        let q_x = Fp2::zero();
        let q_y = Fp2::zero();
        let mut out = Fp12::zero();
        pairing(&mut out, &p_x, &p_y, &q_x, &q_y);
        let _ = out;
    }
}
