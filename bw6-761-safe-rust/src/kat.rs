//! Cross-check that fiat-rust wrappers + the safe-Rust extension
//! tower obey field axioms + verified-bedrock2 invariants.
//!
//! The pairing-level KAT (gnark cross-check) is currently #[ignore]
//! pending the SageMath-computed Frobenius constants — see the
//! crate-level doc and BW6_761_FrobConsts.v.
use super::*;

fn zero() -> Fp { Fp([0u64; 12]) }

fn one_mont() -> Fp {
    // R mod p; obtained via to_montgomery(1).
    let raw = FpRaw({
        let mut a = [0u64; 12];
        a[0] = 1;
        a
    });
    let mut out = zero();
    fp_to_montgomery(&mut out, &raw);
    out
}

fn nontrivial_raw() -> FpRaw {
    let mut a = [0u64; 12];
    a[0] = 0x0123_4567_89ab_cdef;
    a[1] = 0xfedc_ba98_7654_3210;
    a[2] = 0x0011_2233_4455_6677;
    a[3] = 0x7766_5544_3322_1100;
    a[4] = 0xdead_beef_cafe_babe;
    a[5] = 0x1357_9bdf_2468_ace0;
    a[6] = 0x0246_8ace_1357_9bdf;
    a[7] = 0xface_b00c_d00d_feed;
    a[8] = 0xaaaa_bbbb_cccc_dddd;
    a[9] = 0x1111_2222_3333_4444;
    a[10] = 0x5555_6666_7777_8888;
    a[11] = 0x0099_aabb_ccdd_eeff;
    // Mask the most-significant limb conservatively: BW6-761 prime
    // begins with 0x122e..., so any 12-limb value whose top byte is
    // ≤ 0x11 is safely < p.  Cleared to 0x00xx... here.
    a[11] &= 0x00ff_ffff_ffff_ffff;
    FpRaw(a)
}

// =====================================================================
// fiat-rust Fp KATs (sanity check the leaf wrappers)
// =====================================================================

#[test]
fn add_zero_identity() {
    let a = one_mont();
    let mut out = zero();
    fp_add(&mut out, &a, &zero());
    assert_eq!(out.0, a.0);
}

#[test]
fn sub_self_is_zero() {
    let a = one_mont();
    let mut out = a;
    fp_sub(&mut out, &a, &a);
    assert_eq!(out.0, [0u64; 12]);
}

#[test]
fn mul_one_identity() {
    let a = one_mont();
    let mut out = zero();
    fp_mul(&mut out, &a, &a);  // 1 * 1 = 1
    assert_eq!(out.0, a.0);
}

#[test]
fn invert_roundtrip() {
    let mut a = zero();
    fp_to_montgomery(&mut a, &nontrivial_raw());
    let mut a_inv = zero();
    fp_inv(&mut a_inv, &a);
    let mut prod = zero();
    fp_mul(&mut prod, &a, &a_inv);
    assert_eq!(prod.0, one_mont().0, "a * a^-1 should equal 1 in Montgomery form");
}

// =====================================================================
// Extern-shim linkage KATs: prove that the Coq-verified tower bodies
// successfully resolve every `_bw6_761_*` symbol through the
// extern_shim re-routing into fiat-rust.
// =====================================================================

/// Helper: tower's Fp newtype with Montgomery-form 1.
fn tower_one_mont() -> tower::Fp {
    let canonical = one_mont();
    tower::Fp(canonical.0)
}

/// Helper: tower's Fp newtype with all-zero limbs.
fn tower_zero_fp() -> tower::Fp {
    tower::Fp([0u64; 12])
}

#[test]
fn tower_link_smoke_fp3_add() {
    // Exercises bw6_761_Fp3_add: three parallel Fp adds.  With c0=1,
    // c1=c2=0 plus the zero element, the result must equal (1,0,0).
    // A green test means: extern_shim's `_bw6_761_add` symbol
    // resolved + fiat-rust's add was invoked + the byte layout of
    // tower::Fp matches fiat-rust's Fp.
    use tower::{bw6_761_Fp3_add, Fp3 as TFp3};
    let a = TFp3 { c0: tower_one_mont(), c1: tower_zero_fp(), c2: tower_zero_fp() };
    let z = TFp3 { c0: tower_zero_fp(), c1: tower_zero_fp(), c2: tower_zero_fp() };
    let mut out = TFp3 { c0: tower_zero_fp(), c1: tower_zero_fp(), c2: tower_zero_fp() };
    bw6_761_Fp3_add(&mut out, &a, &z);
    assert_eq!(out.c0.0, tower_one_mont().0, "Fp3_add(a, 0) c0 should equal a.c0");
    assert_eq!(out.c1.0, [0u64; 12], "Fp3_add(a, 0) c1 should be zero");
    assert_eq!(out.c2.0, [0u64; 12], "Fp3_add(a, 0) c2 should be zero");
}

#[test]
fn tower_link_smoke_fp3_mul() {
    // Exercises bw6_761_Fp3_mul through the Karatsuba-cubic body.
    // With a = (1, 0, 0), a * a = (1, 0, 0).  Verifies that the
    // 12+ recursive calls into Fp leaf ops all link.
    use tower::{bw6_761_Fp3_mul, Fp3 as TFp3};
    let a = TFp3 { c0: tower_one_mont(), c1: tower_zero_fp(), c2: tower_zero_fp() };
    let mut out = TFp3 { c0: tower_zero_fp(), c1: tower_zero_fp(), c2: tower_zero_fp() };
    bw6_761_Fp3_mul(&mut out, &a, &a);
    assert_eq!(out.c0.0, tower_one_mont().0, "Fp3_mul(1, 1) c0 should equal 1");
    assert_eq!(out.c1.0, [0u64; 12], "Fp3_mul(1, 1) c1 should be zero");
    assert_eq!(out.c2.0, [0u64; 12], "Fp3_mul(1, 1) c2 should be zero");
}

#[test]
fn tower_link_smoke_fp6_mul() {
    // Exercises bw6_761_Fp6_mul through the quadratic-over-Fp3
    // Karatsuba body.  (a+0·w)*(a+0·w) = (a², 0) and with a = (1,0,0)
    // in Fp3, a² = (1,0,0).
    use tower::{bw6_761_Fp6_mul, Fp3 as TFp3, Fp6 as TFp6};
    let one_fp3 = TFp3 { c0: tower_one_mont(), c1: tower_zero_fp(), c2: tower_zero_fp() };
    let zero_fp3 = TFp3 { c0: tower_zero_fp(), c1: tower_zero_fp(), c2: tower_zero_fp() };
    let a = TFp6 { c0: one_fp3, c1: zero_fp3 };
    let mut out = TFp6 { c0: zero_fp3, c1: zero_fp3 };
    bw6_761_Fp6_mul(&mut out, &a, &a);
    assert_eq!(out.c0.c0.0, tower_one_mont().0, "Fp6_mul(1, 1) c0.c0 should equal 1");
    assert_eq!(out.c0.c1.0, [0u64; 12]);
    assert_eq!(out.c0.c2.0, [0u64; 12]);
    assert_eq!(out.c1.c0.0, [0u64; 12]);
    assert_eq!(out.c1.c1.0, [0u64; 12]);
    assert_eq!(out.c1.c2.0, [0u64; 12]);
}

#[test]
fn tower_fp3_inv_roundtrip() {
    // Exercises the verified bw6_761_Fp3_inv body (cubic-extension
    // inversion formula).  inv(1, 0, 0) = (1, 0, 0).
    use tower::{bw6_761_Fp3_inv, bw6_761_Fp3_mul, Fp3 as TFp3};
    let a = TFp3 { c0: tower_one_mont(), c1: tower_zero_fp(), c2: tower_zero_fp() };
    let mut a_inv = TFp3 { c0: tower_zero_fp(), c1: tower_zero_fp(), c2: tower_zero_fp() };
    bw6_761_Fp3_inv(&mut a_inv, &a);
    // 1 inverted in Montgomery form is still 1; multiplying back
    // must give 1.
    let mut prod = TFp3 { c0: tower_zero_fp(), c1: tower_zero_fp(), c2: tower_zero_fp() };
    bw6_761_Fp3_mul(&mut prod, &a, &a_inv);
    assert_eq!(prod.c0.0, tower_one_mont().0, "a * a^-1 should be (1, 0, 0)");
    assert_eq!(prod.c1.0, [0u64; 12]);
    assert_eq!(prod.c2.0, [0u64; 12]);
}

#[test]
fn tower_fp6_inv_roundtrip() {
    // Exercises the hand-coded `bw6_761_Fp6_inv` (norm-trick over
    // Fp3, defined in the OCaml driver's heredoc) called by the
    // verified bw6_final_exp_easy.  inv(1, 0) * (1, 0) = (1, 0).
    use tower::{bw6_761_Fp6_inv, bw6_761_Fp6_mul, Fp3 as TFp3, Fp6 as TFp6};
    let one_fp3 = TFp3 { c0: tower_one_mont(), c1: tower_zero_fp(), c2: tower_zero_fp() };
    let zero_fp3 = TFp3 { c0: tower_zero_fp(), c1: tower_zero_fp(), c2: tower_zero_fp() };
    let a = TFp6 { c0: one_fp3, c1: zero_fp3 };
    let mut a_inv = TFp6 { c0: zero_fp3, c1: zero_fp3 };
    bw6_761_Fp6_inv(&mut a_inv, &a);
    let mut prod = TFp6 { c0: zero_fp3, c1: zero_fp3 };
    bw6_761_Fp6_mul(&mut prod, &a, &a_inv);
    assert_eq!(prod.c0.c0.0, tower_one_mont().0, "a * a^-1 should be Fp6 one");
    assert_eq!(prod.c0.c1.0, [0u64; 12]);
    assert_eq!(prod.c0.c2.0, [0u64; 12]);
    assert_eq!(prod.c1.c0.0, [0u64; 12]);
    assert_eq!(prod.c1.c1.0, [0u64; 12]);
    assert_eq!(prod.c1.c2.0, [0u64; 12]);
}

// =====================================================================
// Pairing-level KATs.
//
// IMPORTANT: BW6_761_FrobConsts.v ships placeholder Frobenius
// constants; without the real SageMath-computed values for the
// BW6-761 prime, `bw6_final_exp` cannot produce the canonical
// pairing value matching gnark-crypto's `e(g1, g2)`.  The gnark
// cross-check below is therefore `#[ignore]`'d until those
// constants land.
// =====================================================================

/// Smoke test: the pairing function runs end-to-end without
/// panicking on (1, 1), (1, 1)-style inputs.  Doesn't assert the
/// algebraic value (placeholder Frob consts) but confirms the
/// `miller_loop -> final_exp` wiring links and the inner sequence
/// of ~9 final-exp helpers (conjugate / pow_u / frob / frob_p2 /
/// frob_p3 / mul / inv chain) all resolve.
#[test]
fn pairing_runs_without_panic() {
    use tower::{Fp3 as TFp3, Fp6 as TFp6};
    let one_fp3 = TFp3 { c0: tower_one_mont(), c1: tower_zero_fp(), c2: tower_zero_fp() };
    let zero_fp3 = TFp3 { c0: tower_zero_fp(), c1: tower_zero_fp(), c2: tower_zero_fp() };

    // Placeholder generator-like points.  The G2 affine point's
    // membership on the twist isn't enforced here — we just want
    // every Coq-extracted bedrock2 body to execute.
    let p = G1 { x: tower_one_mont(), y: tower_one_mont() };
    let q = G2 { x: one_fp3, y: one_fp3 };

    // Placeholder Frobenius constants (= one_fp3).  In a real
    // deployment these come from BW6_761_FrobConsts.v's SageMath-
    // computed values.
    let gamma_fp3 = one_fp3;
    let gamma_fp6 = one_fp3;
    let gamma_fp3_p2 = one_fp3;
    let gamma_fp6_p2 = one_fp3;
    let gamma_fp6_p3 = one_fp3;

    let mut out = TFp6 { c0: zero_fp3, c1: zero_fp3 };
    pairing(&mut out, &p, &q,
            &gamma_fp3, &gamma_fp6,
            &gamma_fp3_p2, &gamma_fp6_p2, &gamma_fp6_p3);
    // No assertion: this test passes iff pairing returns at all.
    // (A divide-by-zero in Fp3_inv during the easy part would
    // surface as a panic via fiat-rust's invariants.)
}

/// gnark-crypto cross-check.  IGNORED pending real Frobenius
/// constants.
///
/// When `BW6_761_FrobConsts.v` is updated with SageMath-computed
/// values for the BW6-761 prime (gamma_fp3 = zeta^{(p-1)/3} etc.),
/// remove the `#[ignore]` and assert against gnark-crypto's
/// canonical `e(g1Gen, g2Gen)` value.  As of 2026-05-21,
/// gnark-crypto's `ecc/bw6-761/pairing_test.go` ships no hardcoded
/// vector — the canonical reference value would need to be
/// extracted by running gnark's `Pair(g1Gen, g2Gen)` and dumping
/// the 6×Fp Montgomery-form limbs.
#[test]
#[ignore = "requires SageMath-computed Frobenius constants (BW6_761_FrobConsts.v ships placeholders)"]
fn pairing_kat_gnark_generator() {
    // TODO(post-Frob-consts):
    //   1. Replace BW6_761_FrobConsts.v with real values
    //   2. Regenerate bw6_761_safe_tower.rs
    //   3. Hard-code gnark's `e(g1Gen, g2Gen)` Fp6 limbs as
    //      EXPECTED_E_G_G.
    //   4. Assert pairing(g1Gen, g2Gen, ...) == EXPECTED_E_G_G.
    unimplemented!("waiting on Frobenius constants");
}
