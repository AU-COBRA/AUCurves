//! `fe25519_invert` — emitted from a verified Lean `RustCmd` AST.
//!
//! Source AST: `SSProve-lean/CatCrypt/Crypto/Jasmin/Examples/Fe25519Invert.lean`
//! Emitter:    `RustEmit.ppRustFunction` (per-constructor structural map)
//! Trust:      single named axiom `RustcExec_correct` in
//!             `JasminToRustEmitSimulates.lean` (Lean ⊢ Qed).
//!
//! Computes `out := a^(p-2) mod p`, p = 2^255 - 19.  254-square +
//! 11-multiplication standard chain (Bernstein / dalek / libjade).
//!
//! Replaces the hand-coded version at `mont_to_edwards.rs::fe25519_invert`
//! when feature `lean_emitted_invert` is on.  KAT'd against the
//! hand-coded version + dalek in this module's unit tests.
//!
//! The emitter renders the type `TFp25519` as `Fp25519`; we alias it
//! to fiat's tight element type below.  The leaves
//! (`fe25519_sqr`, `fe25519_mul`, `fe25519_copy`) are taken from this
//! module so the AST-emitted code links against verified primitives.

#![cfg(feature = "lean_emitted_invert")]
#![allow(non_snake_case)]

use fiat_crypto::curve25519_64::{
    fiat_25519_carry_mul, fiat_25519_carry_square, fiat_25519_relax,
    fiat_25519_loose_field_element, fiat_25519_tight_field_element,
};

/// The type the Lean emitter renders `TFp25519` as.
pub type Fp25519 = fiat_25519_tight_field_element;

trait FpZero { fn zero() -> Self; }
impl FpZero for Fp25519 {
    #[inline(always)]
    fn zero() -> Self { fiat_25519_tight_field_element([0; 5]) }
}

#[inline(always)]
fn fe25519_sqr(out: &mut Fp25519, a: &Fp25519) {
    let mut al = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_relax(&mut al, a);
    fiat_25519_carry_square(out, &al);
}

#[inline(always)]
fn fe25519_mul(out: &mut Fp25519, a: &Fp25519, b: &Fp25519) {
    let mut al = fiat_25519_loose_field_element([0; 5]);
    let mut bl = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_relax(&mut al, a);
    fiat_25519_relax(&mut bl, b);
    fiat_25519_carry_mul(out, &al, &bl);
}

#[inline(always)]
fn fe25519_copy(out: &mut Fp25519, src: &Fp25519) {
    out.0[0] = src.0[0]; out.0[1] = src.0[1]; out.0[2] = src.0[2];
    out.0[3] = src.0[3]; out.0[4] = src.0[4];
}

// ============================================================
// === EMITTED VERBATIM from /tmp/fe25519_invert.rs ===========
// === Source AST: Fe25519Invert.lean::fe25519InvertBody ======
// ============================================================

pub fn fe25519_invert(a : &Fp25519, out : &mut Fp25519) {
    let mut tmp : Fp25519 = Fp25519::zero();

    let mut scratch : Fp25519 = Fp25519::zero();

    let mut z2 : Fp25519 = Fp25519::zero();

    let mut z9 : Fp25519 = Fp25519::zero();

    let mut z11 : Fp25519 = Fp25519::zero();

    let mut z2_5_0 : Fp25519 = Fp25519::zero();

    let mut z2_10_0 : Fp25519 = Fp25519::zero();

    let mut z2_20_0 : Fp25519 = Fp25519::zero();

    let mut z2_40_0 : Fp25519 = Fp25519::zero();

    let mut z2_50_0 : Fp25519 = Fp25519::zero();

    let mut z2_100_0 : Fp25519 = Fp25519::zero();

    let mut t2 : Fp25519 = Fp25519::zero();

    let mut t3 : Fp25519 = Fp25519::zero();

    fe25519_sqr(&mut z2, a);
    fe25519_sqr(&mut tmp, &z2);
    fe25519_sqr(&mut scratch, &tmp);
    fe25519_copy(&mut tmp, &scratch);
    fe25519_mul(&mut z9, &tmp, a);
    fe25519_mul(&mut z11, &z9, &z2);
    fe25519_sqr(&mut tmp, &z11);
    fe25519_mul(&mut z2_5_0, &tmp, &z9);
    fe25519_sqr(&mut tmp, &z2_5_0);
    for _i in 0u64..4u64 {
        fe25519_sqr(&mut scratch, &tmp);
        fe25519_copy(&mut tmp, &scratch);
    }
    fe25519_mul(&mut z2_10_0, &tmp, &z2_5_0);
    fe25519_sqr(&mut tmp, &z2_10_0);
    for _i in 0u64..9u64 {
        fe25519_sqr(&mut scratch, &tmp);
        fe25519_copy(&mut tmp, &scratch);
    }
    fe25519_mul(&mut z2_20_0, &tmp, &z2_10_0);
    fe25519_sqr(&mut tmp, &z2_20_0);
    for _i in 0u64..19u64 {
        fe25519_sqr(&mut scratch, &tmp);
        fe25519_copy(&mut tmp, &scratch);
    }
    fe25519_mul(&mut z2_40_0, &tmp, &z2_20_0);
    fe25519_sqr(&mut tmp, &z2_40_0);
    for _i in 0u64..9u64 {
        fe25519_sqr(&mut scratch, &tmp);
        fe25519_copy(&mut tmp, &scratch);
    }
    fe25519_mul(&mut z2_50_0, &tmp, &z2_10_0);
    fe25519_sqr(&mut tmp, &z2_50_0);
    for _i in 0u64..49u64 {
        fe25519_sqr(&mut scratch, &tmp);
        fe25519_copy(&mut tmp, &scratch);
    }
    fe25519_mul(&mut z2_100_0, &tmp, &z2_50_0);
    fe25519_sqr(&mut tmp, &z2_100_0);
    for _i in 0u64..99u64 {
        fe25519_sqr(&mut scratch, &tmp);
        fe25519_copy(&mut tmp, &scratch);
    }
    fe25519_mul(&mut t2, &tmp, &z2_100_0);
    fe25519_sqr(&mut tmp, &t2);
    for _i in 0u64..49u64 {
        fe25519_sqr(&mut scratch, &tmp);
        fe25519_copy(&mut tmp, &scratch);
    }
    fe25519_mul(&mut t3, &tmp, &z2_50_0);
    fe25519_sqr(&mut tmp, &t3);
    for _i in 0u64..4u64 {
        fe25519_sqr(&mut scratch, &tmp);
        fe25519_copy(&mut tmp, &scratch);
    }
    fe25519_mul(out, &tmp, &z11);
}

// ============================================================
// === END EMITTED ============================================
// ============================================================

#[cfg(test)]
mod tests {
    use super::*;
    use fiat_crypto::curve25519_64::{
        fiat_25519_from_bytes, fiat_25519_to_bytes,
    };

    /// KAT against the hand-coded fe25519_invert in mont_to_edwards.rs.
    /// Both must produce identical output for any input.
    #[test]
    fn lean_emitted_matches_hand_coded() {
        for seed in [0x01u8, 0x42, 0x77, 0xa5, 0xfe] {
            let mut bytes = [seed; 32];
            bytes[31] &= 0x7f;
            let mut x = Fp25519::zero();
            fiat_25519_from_bytes(&mut x, &bytes);

            let mut emitted = Fp25519::zero();
            fe25519_invert(&x, &mut emitted);

            let mut hand = Fp25519::zero();
            crate::mont_to_edwards::fe25519_invert(&mut hand, &x);

            let mut e_bytes = [0u8; 32];
            let mut h_bytes = [0u8; 32];
            fiat_25519_to_bytes(&mut e_bytes, &emitted);
            fiat_25519_to_bytes(&mut h_bytes, &hand);
            assert_eq!(e_bytes, h_bytes,
                "lean-emitted vs hand-coded fe25519_invert divergence at seed 0x{seed:02x}");
        }
    }
}
