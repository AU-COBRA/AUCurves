//! `mont_u_to_edwards_compressed` — emitted-Lean field-arithmetic core.
//!
//! Source AST: `SSProve-lean/CatCrypt/Crypto/Jasmin/Examples/MontUToEdwards.lean`
//! Emitter:    `RustEmit.ppRustFunction` (per-constructor structural map)
//! Trust:      single named axiom `RustcExec_correct` in Lean's
//!             `JasminToRustEmitSimulates.lean`.
//!
//! Replaces the field-arithmetic core of
//! `mont_to_edwards::mont_u_to_edwards_compressed` (the
//! `y = (u-1)·(u+1)^(-1)` computation) with a Lean-emitted body.  The
//! outer `[u8; 32]` <-> `Fp25519` boundary, the rejection of
//! `u + 1 == 0`, and the sign-bit OR on the encoded y bytes stay in
//! the hand-coded shim below — these are byte-level operations that
//! the current IR does not express directly.
//!
//! Active under feature `lean_emitted_mont_to_edwards`.  KAT'd against
//! the hand-coded version (which is itself KAT'd against dalek) in
//! this module's unit tests.

#![cfg(feature = "lean_emitted_mont_to_edwards")]
#![allow(non_snake_case)]

use fiat_crypto::curve25519_64::{
    fiat_25519_add, fiat_25519_carry, fiat_25519_carry_mul, fiat_25519_from_bytes,
    fiat_25519_loose_field_element, fiat_25519_relax, fiat_25519_sub,
    fiat_25519_tight_field_element, fiat_25519_to_bytes,
};

/// The type the Lean emitter renders `TFp25519` as.
pub type Fp25519 = fiat_25519_tight_field_element;

trait FpZero { fn zero() -> Self; }
impl FpZero for Fp25519 {
    #[inline(always)]
    fn zero() -> Self { fiat_25519_tight_field_element([0; 5]) }
}

#[inline(always)]
fn fe25519_set_one(out: &mut Fp25519) {
    // Tight fiat-25519 layout: radix-2^51 limbs, value 1 = [1, 0, 0, 0, 0].
    out.0[0] = 1;
    out.0[1] = 0;
    out.0[2] = 0;
    out.0[3] = 0;
    out.0[4] = 0;
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
fn fe25519_sub_then_carry(out: &mut Fp25519, a: &Fp25519, b: &Fp25519) {
    let mut loose = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_sub(&mut loose, a, b);
    fiat_25519_carry(out, &loose);
}

#[inline(always)]
fn fe25519_add_then_carry(out: &mut Fp25519, a: &Fp25519, b: &Fp25519) {
    let mut loose = fiat_25519_loose_field_element([0; 5]);
    fiat_25519_add(&mut loose, a, b);
    fiat_25519_carry(out, &loose);
}

#[inline(always)]
fn fe25519_copy(out: &mut Fp25519, src: &Fp25519) {
    out.0[0] = src.0[0]; out.0[1] = src.0[1]; out.0[2] = src.0[2];
    out.0[3] = src.0[3]; out.0[4] = src.0[4];
}

/// `fe25519_invert` leaf used by the emitted body.  Delegates to the
/// previously Lean-emitted `fe25519_invert` if available (so the AST
/// composes: Lean-emitted body calls Lean-emitted body); else falls
/// back to the hand-coded `mont_to_edwards::fe25519_invert` (same
/// 254-square + 11-mul addition chain).
///
/// Both implementations are KAT-tied: the Lean-emitted `fe25519_invert`
/// has its own unit test against the hand-coded version, so under
/// either branch the field semantics are pinned.
#[inline(always)]
fn fe25519_invert(out: &mut Fp25519, a: &Fp25519) {
    #[cfg(feature = "lean_emitted_invert")]
    {
        // Lean-emitted body: out is 2nd arg in that emitter's signature.
        crate::ed25519_rustcmd::fe25519_invert_emitted::fe25519_invert(a, out);
    }
    #[cfg(not(feature = "lean_emitted_invert"))]
    {
        crate::mont_to_edwards::fe25519_invert(out, a);
    }
}

// ============================================================
// === EMITTED VERBATIM from /tmp/mont_u_to_edwards_field.rs ==
// === Source AST: MontUToEdwards.lean::montUToEdwardsBody ====
// ============================================================

pub fn mont_u_to_edwards_field(u : &Fp25519, y_out : &mut Fp25519, den_out : &mut Fp25519) {
    let mut one : Fp25519 = Fp25519::zero();
    let mut num : Fp25519 = Fp25519::zero();
    let mut den : Fp25519 = Fp25519::zero();
    let mut inv_den : Fp25519 = Fp25519::zero();
    fe25519_set_one(&mut one);
    fe25519_sub_then_carry(&mut num, u, &one);
    fe25519_add_then_carry(&mut den, u, &one);
    fe25519_invert(&mut inv_den, &den);
    fe25519_mul(y_out, &num, &inv_den);
    fe25519_copy(den_out, &den);
}

// ============================================================
// === END EMITTED ============================================
// ============================================================

/// Outer shim around the emitted field-arithmetic core.  Performs:
///   * top-bit mask on input (Montgomery encoding uses bits 0..254);
///   * `[u8; 32]` -> `Fp25519` decode of input;
///   * call to the emitted body;
///   * rejection of `u + 1 == 0` via byte-encoded zero test on `den`;
///   * `Fp25519` -> `[u8; 32]` encode of `y`;
///   * `out[31] = (out[31] & 0x7f) | ((sign_bit & 1) << 7)` sign-bit OR.
///
/// Returns `None` iff `u + 1 == 0` (i.e. `u == -1` mod p).
pub fn mont_u_to_edwards_compressed(u_bytes: &[u8; 32], sign_bit: u8) -> Option<[u8; 32]> {
    // Mask off the unused top bit (Montgomery encoding uses bits 0..254).
    let mut u_in = *u_bytes;
    u_in[31] &= 0x7f;

    let mut u = Fp25519::zero();
    fiat_25519_from_bytes(&mut u, &u_in);

    let mut y = Fp25519::zero();
    let mut den = Fp25519::zero();
    mont_u_to_edwards_field(&u, &mut y, &mut den);

    // Reject u == -1 (denom == 0): in canonical form, all output bytes are 0.
    let mut den_bytes = [0u8; 32];
    fiat_25519_to_bytes(&mut den_bytes, &den);
    if den_bytes.iter().all(|&b| b == 0) {
        return None;
    }

    // Encode y as 32 LE bytes, set top bit to sign_bit.
    let mut out = [0u8; 32];
    fiat_25519_to_bytes(&mut out, &y);
    out[31] = (out[31] & 0x7f) | ((sign_bit & 1) << 7);
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// KAT against the hand-coded `mont_to_edwards::mont_u_to_edwards_compressed`.
    /// Both must produce identical output for any input.
    #[test]
    fn lean_emitted_matches_hand_coded() {
        for seed in [0x01u8, 0x42, 0x77, 0xa5, 0xfe] {
            // Build a valid Montgomery u-coordinate via the X25519 base
            // scalarmult, exactly as the hand-coded module's test does.
            let priv_key = [seed; 32];
            let pub_u = crate::x25519_jasmin_base(&priv_key);

            for &sign_bit in &[0u8, 1] {
                let ours = mont_u_to_edwards_compressed(&pub_u, sign_bit);
                let theirs =
                    crate::mont_to_edwards::mont_u_to_edwards_compressed(&pub_u, sign_bit);
                assert_eq!(ours, theirs,
                    "Lean-emitted vs hand-coded mont→edwards mismatch at seed 0x{:02x}, sign {}",
                    seed, sign_bit);
            }
        }
    }

    #[test]
    fn rejects_u_eq_neg_one_matches_hand_coded() {
        // u = -1 mod p.
        let mut u = [0u8; 32];
        u[0] = 0xec;
        for b in u.iter_mut().skip(1).take(30) { *b = 0xff; }
        u[31] = 0x7f;
        assert!(mont_u_to_edwards_compressed(&u, 0).is_none(),
                "Lean-emitted: u = -1 should be rejected");
        assert!(crate::mont_to_edwards::mont_u_to_edwards_compressed(&u, 0).is_none(),
                "hand-coded: u = -1 should be rejected");
    }
}
