//! `Scalar25519` operations — emitted from verified Lean `RustCmd` ASTs.
//!
//! Source ASTs: `SSProve-lean/CatCrypt/Crypto/Jasmin/Examples/Scalar25519Ops.lean`
//! Emitter:     `RustEmit.ppRustFunction` (per-constructor structural map)
//! Trust:       single named axiom `RustcExec_correct` in Lean's
//!              `JasminToRustEmitSimulates.lean`.
//!
//! Six per-method bodies (each a single fiat-crypto leaf call):
//!   * `scalar25519_from_bytes_mod_order_emit`
//!   * `scalar25519_to_bytes_emit`
//!   * `scalar25519_mul_emit`
//!   * `scalar25519_add_emit`
//!   * `scalar25519_sub_emit`
//!   * `scalar25519_negate_emit`
//!
//! Wide reduction (`from_bytes_mod_order_wide`) is composed in Rust over
//! the 6 primitives below; see [`from_bytes_mod_order_wide_emit`] —
//! the IR's TBytes / TArr do not expose 64-byte slicing, and per the
//! task spec's "Hax-readiness" constraint we don't extend the IR.
//!
//! Active under feature `lean_emitted_scalar25519`.  KAT'd against the
//! hand-coded `Scalar25519::*` API on 5+ random inputs per method.

#![cfg(feature = "lean_emitted_scalar25519")]
#![allow(non_snake_case)]

use fiat_crypto::curve25519_scalar_64::{
    fiat_25519_scalar_add, fiat_25519_scalar_from_bytes,
    fiat_25519_scalar_from_montgomery, fiat_25519_scalar_mul,
    fiat_25519_scalar_montgomery_domain_field_element,
    fiat_25519_scalar_non_montgomery_domain_field_element,
    fiat_25519_scalar_opp, fiat_25519_scalar_sub, fiat_25519_scalar_to_bytes,
    fiat_25519_scalar_to_montgomery,
};

/// The type the Lean emitter renders `TFpL25519` as.
pub type FpL25519 = fiat_25519_scalar_montgomery_domain_field_element;
type NonMont    = fiat_25519_scalar_non_montgomery_domain_field_element;

trait FpZero { fn zero() -> Self; }
impl FpZero for FpL25519 {
    #[inline(always)]
    fn zero() -> Self { fiat_25519_scalar_montgomery_domain_field_element([0; 4]) }
}

#[inline(always)]
fn zero_nm() -> NonMont {
    fiat_25519_scalar_non_montgomery_domain_field_element([0; 4])
}

// --- leaf wrappers ----------------------------------------------------

#[inline(always)]
fn scalar25519_bytes_to_mont(out: &mut FpL25519, bytes_in: &[u8; 32]) {
    let mut nm = zero_nm();
    fiat_25519_scalar_from_bytes(&mut nm.0, bytes_in);
    fiat_25519_scalar_to_montgomery(out, &nm);
}

#[inline(always)]
fn scalar25519_mont_to_bytes(out: &mut [u8; 32], mont: &FpL25519) {
    let mut nm = zero_nm();
    fiat_25519_scalar_from_montgomery(&mut nm, mont);
    fiat_25519_scalar_to_bytes(out, &nm.0);
}

#[inline(always)]
fn scalar25519_mul_mont(out: &mut FpL25519, a: &FpL25519, b: &FpL25519) {
    fiat_25519_scalar_mul(out, a, b);
}

#[inline(always)]
fn scalar25519_add_mont(out: &mut FpL25519, a: &FpL25519, b: &FpL25519) {
    fiat_25519_scalar_add(out, a, b);
}

#[inline(always)]
fn scalar25519_sub_mont(out: &mut FpL25519, a: &FpL25519, b: &FpL25519) {
    fiat_25519_scalar_sub(out, a, b);
}

#[inline(always)]
fn scalar25519_opp_mont(out: &mut FpL25519, a: &FpL25519) {
    fiat_25519_scalar_opp(out, a);
}

// ============================================================
// === EMITTED VERBATIM from /tmp/scalar25519_emitted.rs ======
// === Source ASTs: Scalar25519Ops.lean::{emit{...}Body} ======
// ============================================================

pub fn scalar25519_from_bytes_mod_order_emit(bytes_in : &[u8; 32], out : &mut FpL25519) {
    scalar25519_bytes_to_mont(out, bytes_in);
}

pub fn scalar25519_to_bytes_emit(mont : &FpL25519, out : &mut [u8; 32]) {
    scalar25519_mont_to_bytes(out, mont);
}

pub fn scalar25519_mul_emit(a : &FpL25519, b : &FpL25519, out : &mut FpL25519) {
    scalar25519_mul_mont(out, a, b);
}

pub fn scalar25519_add_emit(a : &FpL25519, b : &FpL25519, out : &mut FpL25519) {
    scalar25519_add_mont(out, a, b);
}

pub fn scalar25519_sub_emit(a : &FpL25519, b : &FpL25519, out : &mut FpL25519) {
    scalar25519_sub_mont(out, a, b);
}

pub fn scalar25519_negate_emit(a : &FpL25519, out : &mut FpL25519) {
    scalar25519_opp_mont(out, a);
}

// ============================================================
// === END EMITTED ============================================
// ============================================================

/// Wide-reduction composition over the 6 emitted primitives.
///
/// Splits `bytes_in : [u8; 64]` into 32-byte halves `lo || hi`,
/// reduces each via `from_bytes_mod_order_emit`, then computes
/// `out = hi · c256 + lo` where `c256 = -16 · L_extra mod L =
/// 2^256 mod L`.  `L_extra = L - 2^252` is precomputed at AST-leaf
/// granularity; `c256` is derived inline (no large hex constant).
pub fn from_bytes_mod_order_wide_emit(bytes_in: &[u8; 64], out: &mut FpL25519) {
    let mut lo_bytes = [0u8; 32];
    let mut hi_bytes = [0u8; 32];
    lo_bytes.copy_from_slice(&bytes_in[..32]);
    hi_bytes.copy_from_slice(&bytes_in[32..]);

    let mut lo = FpL25519::zero();
    let mut hi = FpL25519::zero();
    scalar25519_from_bytes_mod_order_emit(&lo_bytes, &mut lo);
    scalar25519_from_bytes_mod_order_emit(&hi_bytes, &mut hi);

    // L_extra = L - 2^252 = 27742317777372353535851937790883648493
    // Hex: 0x14def9dea2f79cd65812631a5cf5d3ed (128-bit value).
    const L_EXTRA_LE: [u8; 32] = [
        0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58,
        0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    ];
    const SIXTEEN_LE: [u8; 32] = [
        16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ];

    let mut l_extra = FpL25519::zero();
    let mut sixteen = FpL25519::zero();
    scalar25519_from_bytes_mod_order_emit(&L_EXTRA_LE, &mut l_extra);
    scalar25519_from_bytes_mod_order_emit(&SIXTEEN_LE, &mut sixteen);

    // c256 = -(16 · L_extra)  mod L  =  2^256  mod L
    let mut t = FpL25519::zero();
    scalar25519_mul_emit(&l_extra, &sixteen, &mut t);
    let mut c256 = FpL25519::zero();
    scalar25519_negate_emit(&t, &mut c256);

    // out = hi · c256 + lo
    let mut hi_c256 = FpL25519::zero();
    scalar25519_mul_emit(&hi, &c256, &mut hi_c256);
    scalar25519_add_emit(&hi_c256, &lo, out);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scalar25519::Scalar25519;

    fn rand_bytes(seed: u64) -> [u8; 32] {
        let mut b = [0u8; 32];
        let mut x = seed.wrapping_mul(0x9E3779B97F4A7C15);
        for chunk in b.chunks_mut(8) {
            x = x.wrapping_mul(0x6A09E667F3BCC909).wrapping_add(1);
            chunk.copy_from_slice(&x.to_le_bytes());
        }
        b
    }

    fn rand_bytes_64(seed: u64) -> [u8; 64] {
        let mut b = [0u8; 64];
        b[..32].copy_from_slice(&rand_bytes(seed));
        b[32..].copy_from_slice(&rand_bytes(seed.wrapping_add(1)));
        b
    }

    /// Take a hand-coded Scalar25519 and extract its Mont domain rep.
    /// Used to compare against the emitted body's Mont output.
    fn mont_of(s: &Scalar25519) -> [u64; 4] { s.0.0 }

    #[test]
    fn emitted_from_bytes_mod_order_matches_hand_coded() {
        for seed in 0..5u64 {
            let bytes = rand_bytes(seed);

            let mut ours = FpL25519::zero();
            scalar25519_from_bytes_mod_order_emit(&bytes, &mut ours);

            let theirs = Scalar25519::from_bytes_mod_order(&bytes);

            assert_eq!(ours.0, mont_of(&theirs),
                "from_bytes_mod_order_emit divergence at seed {seed}");
        }
    }

    #[test]
    fn emitted_to_bytes_matches_hand_coded() {
        for seed in 0..5u64 {
            let bytes = rand_bytes(seed);
            let theirs = Scalar25519::from_bytes_mod_order(&bytes);

            // Lift to emit Mont via the emitted from_bytes path.
            let mut mont = FpL25519::zero();
            scalar25519_from_bytes_mod_order_emit(&bytes, &mut mont);

            let mut ours_bytes = [0u8; 32];
            scalar25519_to_bytes_emit(&mont, &mut ours_bytes);
            assert_eq!(ours_bytes, theirs.to_bytes(),
                "to_bytes_emit divergence at seed {seed}");
        }
    }

    #[test]
    fn emitted_mul_matches_hand_coded() {
        for seed in 0..5u64 {
            let a = rand_bytes(seed);
            let b = rand_bytes(seed.wrapping_add(101));

            let mut a_m = FpL25519::zero();
            let mut b_m = FpL25519::zero();
            scalar25519_from_bytes_mod_order_emit(&a, &mut a_m);
            scalar25519_from_bytes_mod_order_emit(&b, &mut b_m);

            let mut prod_m = FpL25519::zero();
            scalar25519_mul_emit(&a_m, &b_m, &mut prod_m);

            let mut ours = [0u8; 32];
            scalar25519_to_bytes_emit(&prod_m, &mut ours);

            let theirs = Scalar25519::from_bytes_mod_order(&a)
                .mul(&Scalar25519::from_bytes_mod_order(&b))
                .to_bytes();
            assert_eq!(ours, theirs, "mul_emit divergence at seed {seed}");
        }
    }

    #[test]
    fn emitted_add_matches_hand_coded() {
        for seed in 0..5u64 {
            let a = rand_bytes(seed);
            let b = rand_bytes(seed.wrapping_add(202));

            let mut a_m = FpL25519::zero();
            let mut b_m = FpL25519::zero();
            scalar25519_from_bytes_mod_order_emit(&a, &mut a_m);
            scalar25519_from_bytes_mod_order_emit(&b, &mut b_m);

            let mut sum_m = FpL25519::zero();
            scalar25519_add_emit(&a_m, &b_m, &mut sum_m);

            let mut ours = [0u8; 32];
            scalar25519_to_bytes_emit(&sum_m, &mut ours);

            let theirs = Scalar25519::from_bytes_mod_order(&a)
                .add(&Scalar25519::from_bytes_mod_order(&b))
                .to_bytes();
            assert_eq!(ours, theirs, "add_emit divergence at seed {seed}");
        }
    }

    #[test]
    fn emitted_sub_matches_hand_coded() {
        for seed in 0..5u64 {
            let a = rand_bytes(seed);
            let b = rand_bytes(seed.wrapping_add(303));

            let mut a_m = FpL25519::zero();
            let mut b_m = FpL25519::zero();
            scalar25519_from_bytes_mod_order_emit(&a, &mut a_m);
            scalar25519_from_bytes_mod_order_emit(&b, &mut b_m);

            let mut diff_m = FpL25519::zero();
            scalar25519_sub_emit(&a_m, &b_m, &mut diff_m);

            let mut ours = [0u8; 32];
            scalar25519_to_bytes_emit(&diff_m, &mut ours);

            let theirs = Scalar25519::from_bytes_mod_order(&a)
                .sub(&Scalar25519::from_bytes_mod_order(&b))
                .to_bytes();
            assert_eq!(ours, theirs, "sub_emit divergence at seed {seed}");
        }
    }

    #[test]
    fn emitted_negate_matches_hand_coded() {
        for seed in 0..5u64 {
            let a = rand_bytes(seed);

            let mut a_m = FpL25519::zero();
            scalar25519_from_bytes_mod_order_emit(&a, &mut a_m);

            let mut neg_m = FpL25519::zero();
            scalar25519_negate_emit(&a_m, &mut neg_m);

            let mut ours = [0u8; 32];
            scalar25519_to_bytes_emit(&neg_m, &mut ours);

            let theirs = Scalar25519::from_bytes_mod_order(&a).negate().to_bytes();
            assert_eq!(ours, theirs, "negate_emit divergence at seed {seed}");
        }
    }

    #[test]
    fn emitted_wide_reduction_matches_hand_coded() {
        for seed in 0..5u64 {
            let bytes = rand_bytes_64(seed);

            let mut ours_m = FpL25519::zero();
            from_bytes_mod_order_wide_emit(&bytes, &mut ours_m);

            let mut ours = [0u8; 32];
            scalar25519_to_bytes_emit(&ours_m, &mut ours);

            let theirs = Scalar25519::from_bytes_mod_order_wide(&bytes).to_bytes();
            assert_eq!(ours, theirs,
                "from_bytes_mod_order_wide_emit divergence at seed {seed}");
        }
    }
}
