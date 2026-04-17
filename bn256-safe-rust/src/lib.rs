//! BN256 pairing — safe Rust tower over verified bedrock2 leaves.
//!
//! Architecture mirrors bn254-safe-rust / bls12-381-safe-rust:
//!   tower functions (Fp2→Fp6→Fp12→pairing): safe Rust, 0 unsafe
//!   leaf Fp ops: thin unsafe wrappers → pure-Rust Montgomery stubs
//!
//! 5 limbs (256-bit prime padded to 320 bits for Montgomery WBW).
//! Curve: BN with seed u = 0x5A76AE9AEC588301.

#![allow(non_snake_case, non_camel_case_types)]
#![allow(unused_assignments, unused_variables, unused_mut, unused_parens, dead_code)]

mod tower {
    include!(concat!(env!("CARGO_MANIFEST_DIR"), "/generated/bn256_safe_tower.rs"));
}

mod stubs;

pub use tower::{Fp, Fp2, Fp6, Fp12};

pub fn fp_add(out: &mut Fp, x: &Fp, y: &Fp) { tower::bn256_add(out, x, y) }
pub fn fp_sub(out: &mut Fp, x: &Fp, y: &Fp) { tower::bn256_sub(out, x, y) }
pub fn fp_mul(out: &mut Fp, x: &Fp, y: &Fp) { tower::bn256_mul(out, x, y) }
pub fn fp_square(out: &mut Fp, x: &Fp) { tower::bn256_square(out, x) }
pub fn fp_opp(out: &mut Fp, x: &Fp) { tower::bn256_opp(out, x) }
pub fn fp_inv(out: &mut Fp, x: &Fp) { tower::bn256_inv(out, x) }
pub fn fp_from_word(out: &mut Fp, w: u64) { tower::bn256_from_word(out, w) }
pub fn fp_copy(out: &mut Fp, x: &Fp) { tower::bn256_felem_copy(out, x) }

pub fn fp2_add(out: &mut Fp2, x: &Fp2, y: &Fp2) { tower::bn256_Fp2_add(out, x, y) }
pub fn fp2_sub(out: &mut Fp2, x: &Fp2, y: &Fp2) { tower::bn256_Fp2_sub(out, x, y) }
pub fn fp2_mul(out: &mut Fp2, x: &Fp2, y: &Fp2) { tower::bn256_Fp2_mul(out, x, y) }
pub fn fp2_square(out: &mut Fp2, x: &Fp2) { tower::bn256_Fp2_square(out, x) }

pub fn pairing(out: &mut Fp12, p_x: &Fp, p_y: &Fp, q_x: &Fp2, q_y: &Fp2) {
    tower::bn256_pairing_dsd(out, p_x, p_y, q_x, q_y)
}

pub fn miller_loop(out: &mut Fp12, p_x: &Fp, p_y: &Fp, q_x: &Fp2, q_y: &Fp2) {
    tower::bn256_miller_loop(out, p_x, p_y, q_x, q_y)
}
