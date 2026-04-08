//! BN254 pairing library — fully safe Rust tower over verified Jasmin leaves.
//!
//! Architecture:
//!   - 47 tower functions (Fp2 → Fp6 → Fp12 → pairing): **safe Rust**,
//!     generated from bedrock2 via bn254_safe_tower.ml. Zero `unsafe`.
//!   - 8 leaf Fp ops (add/sub/mul/square/opp/copy/from_word/select):
//!     thin `unsafe` wrappers around `extern "C"` symbols (Jasmin assembly).
//!   - Borrow checker enforces bedrock2 separation-logic non-aliasing.

#![allow(non_snake_case, non_camel_case_types)]
#![allow(unused_assignments, unused_variables, unused_mut, unused_parens, dead_code)]

// Stubs for testing. Replace with Jasmin .o via build.rs for production.
#[cfg(not(feature = "jasmin"))]
mod stubs;

mod tower {
    include!(concat!(env!("CARGO_MANIFEST_DIR"), "/generated/bn254_safe_tower.rs"));
}

pub use tower::{Fp, Fp2, Fp6, Fp12};

pub fn fp_add(out: &mut Fp, x: &Fp, y: &Fp) { tower::bn254_add(out, x, y) }
pub fn fp_sub(out: &mut Fp, x: &Fp, y: &Fp) { tower::bn254_sub(out, x, y) }
pub fn fp_mul(out: &mut Fp, x: &Fp, y: &Fp) { tower::bn254_mul(out, x, y) }
pub fn fp_square(out: &mut Fp, x: &Fp) { tower::bn254_square(out, x) }

pub fn pairing(out: &mut Fp12, p_x: &Fp, p_y: &Fp, q_x: &Fp2, q_y: &Fp2) {
    tower::bn254_pairing_dsd(out, p_x, p_y, q_x, q_y)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fp_add_disjoint() {
        let a = Fp([1, 2, 3, 4]);
        let b = Fp([5, 6, 7, 8]);
        let mut c = Fp::zero();
        fp_add(&mut c, &a, &b);
        assert_eq!(c.0, [6, 8, 10, 12]);
    }

    #[test]
    fn test_pairing_runs() {
        let p_x = Fp([1, 0, 0, 0]);
        let p_y = Fp([2, 0, 0, 0]);
        let q_x = Fp2::zero();
        let q_y = Fp2::zero();
        let mut out = Fp12::zero();
        pairing(&mut out, &p_x, &p_y, &q_x, &q_y);
        // With stubs, mul/square return 0, so pairing output is trivial.
        // With real Jasmin leaves, this would be non-zero.
        let _ = out;
    }
}
