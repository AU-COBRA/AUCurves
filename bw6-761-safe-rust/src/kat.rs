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

// ====== Real Frobenius constants for BW6-761 (Phase 1, computed
//        via /tmp/bw6_frob_compute.py — matches gnark-crypto/ecc/
//        bw6-761/internal/fptower/frobenius.go) ======
//
//   alpha           = (-4)^((p-1)/3) mod p      (cube root of 1)
//   sqrt(alpha)     = (Tonelli-Shanks branch — happens to equal alpha^2)
//   gamma_fp3 pi    = [_,  alpha,    alpha^2]
//   gamma_fp6 pi    = [sa, sa·alpha, sa·alpha^2]
//   gamma_fp3 pi^2  = squared componentwise
//   gamma_fp6 pi^2  = squared componentwise
//   gamma_fp6 pi^3  = [-1; _; _]  (c0 slot used by per-Fp mul)

fn alpha_raw() -> FpRaw {
    FpRaw([
        0x5e7bc00000000060, 0x214983de30000053, 0x5fe3f89c11811c1e, 0xa5b093ed79b1c57b,
        0xab8579e02ed3cddc, 0xf87fa59308c07a8f, 0x5870636cb60d217f, 0x823132b971cdefc6,
        0x256ab7ae14297a1a, 0x4d06e68545f7e64c, 0x27035cdf02acb274, 0x00cfca638f1500e3,
    ])
}
fn alpha_sq_raw() -> FpRaw {
    FpRaw([
        0x962140000000002a, 0xc547ba8a4000002f, 0xb6290012d96f8819, 0xf2f082d4dcb5e37c,
        0xc65759fc45183151, 0x8e0a235a0a398300, 0xab5e57926fa70184, 0xee4a737f73b6f952,
        0x2d17be416c5e4426, 0x6c1f31e53bd9603c, 0xaa846c61024e4cca, 0x00531dc16c6ecd27,
    ])
}
fn minus_one_raw() -> FpRaw {
    FpRaw([
        0xf49d00000000008a, 0xe6913e6870000082, 0x160cf8aeeaf0a437, 0x98a116c25667a8f8,
        0x71dcd3dc73ebff2e, 0x8689c8ed12f9fd90, 0x03cebaff25b42304, 0x707ba638e584e919,
        0x528275ef8087be41, 0xb926186a81d14688, 0xd187c94004faff3e, 0x0122e824fb83ce0a,
    ])
}

fn fp_from_raw(r: &FpRaw) -> tower::Fp {
    let mut out = zero();
    fp_to_montgomery(&mut out, r);
    tower::Fp(out.0)
}

/// Build the 5 BW6-761 Frobenius gamma constants in Montgomery form,
/// laid out as Fp3 blobs (since the bedrock2 spec passes them as
/// Fp3 pointers):
///   gamma_fp3      = (_,  alpha,    alpha^2)   — c0 ignored
///   gamma_fp6      = (sa, sa·alpha, sa·alpha^2)
///   gamma_fp3_p2   = squared
///   gamma_fp6_p2   = squared
///   gamma_fp6_p3   = (-1, _, _)                — c1, c2 ignored
fn real_frob_consts() -> (tower::Fp3, tower::Fp3, tower::Fp3, tower::Fp3, tower::Fp3) {
    use tower::Fp3;
    let alpha = fp_from_raw(&alpha_raw());
    let alpha_sq = fp_from_raw(&alpha_sq_raw());
    let one_mont = tower_one_mont();
    let minus_one = fp_from_raw(&minus_one_raw());
    // For this prime sqrt(alpha) = alpha^2 (Tonelli-Shanks branch),
    // so b0 = alpha^2, b1 = alpha^2 * alpha = alpha^3 = 1,
    // b2 = alpha^2 * alpha^2 = alpha^4 = alpha.
    let gamma_fp3    = Fp3 { c0: tower_zero_fp(), c1: alpha,    c2: alpha_sq };
    let gamma_fp6    = Fp3 { c0: alpha_sq,        c1: one_mont, c2: alpha    };
    // Squared: a1^2 = alpha^2, a2^2 = alpha^4 = alpha;
    //          b0^2 = alpha,   b1^2 = 1,        b2^2 = alpha^2.
    let gamma_fp3_p2 = Fp3 { c0: tower_zero_fp(), c1: alpha_sq, c2: alpha    };
    let gamma_fp6_p2 = Fp3 { c0: alpha,           c1: one_mont, c2: alpha_sq };
    let gamma_fp6_p3 = Fp3 { c0: minus_one,       c1: tower_zero_fp(), c2: tower_zero_fp() };
    (gamma_fp3, gamma_fp6, gamma_fp3_p2, gamma_fp6_p2, gamma_fp6_p3)
}

/// Smoke test: the pairing function runs end-to-end without
/// panicking on (1, 1), (1, 1)-style inputs with REAL Frobenius
/// constants.  Doesn't assert the algebraic value (no gnark
/// reference vector available) but confirms the per-Fp-component
/// Frobenius bodies execute against real alpha = (-4)^((p-1)/3).
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

    let (gamma_fp3, gamma_fp6, gamma_fp3_p2, gamma_fp6_p2, gamma_fp6_p3) =
        real_frob_consts();

    let mut out = TFp6 { c0: zero_fp3, c1: zero_fp3 };
    pairing(&mut out, &p, &q,
            &gamma_fp3, &gamma_fp6,
            &gamma_fp3_p2, &gamma_fp6_p2, &gamma_fp6_p3);
    // No assertion: this test passes iff pairing returns at all.
    // (A divide-by-zero in Fp3_inv during the easy part would
    // surface as a panic via fiat-rust's invariants.)
}

/// Algebraic sanity: bw6_fp6_frob_p3 on a pure-c1 input should
/// negate every Fp slot (since gamma_fp6_p3.c0 = -1 and pi^3 acts
/// trivially on c0).  Cross-checks the new per-Fp-component body
/// against an explicit Gallina-level expectation.
#[test]
fn fp6_frob_p3_negates_c1() {
    use tower::{bw6_fp6_frob_p3, bw6_761_sub, Fp3 as TFp3, Fp6 as TFp6};
    let (_g3, _g6, _g3p2, _g6p2, gamma_fp6_p3) = real_frob_consts();
    // Input: c0 = (1,0,0), c1 = (1,1,1) — three 1's so the per-slot
    // negation is observable.
    let zero_fp3 = TFp3 { c0: tower_zero_fp(), c1: tower_zero_fp(), c2: tower_zero_fp() };
    let one_fp3  = TFp3 { c0: tower_one_mont(), c1: tower_zero_fp(), c2: tower_zero_fp() };
    let ones_fp3 = TFp3 { c0: tower_one_mont(), c1: tower_one_mont(), c2: tower_one_mont() };
    let x = TFp6 { c0: one_fp3, c1: ones_fp3 };
    let mut out = TFp6 { c0: zero_fp3, c1: zero_fp3 };
    bw6_fp6_frob_p3(&mut out, &x, &gamma_fp6_p3);
    // out.c0 must equal x.c0 (copy)
    assert_eq!(out.c0.c0.0, tower_one_mont().0, "frob_p3.c0.c0 = x.c0.c0");
    assert_eq!(out.c0.c1.0, tower_zero_fp().0);
    assert_eq!(out.c0.c2.0, tower_zero_fp().0);
    // out.c1 must equal -x.c1 (all three slots).  Compute reference
    // by subtracting x.c1 from 0.
    let mut neg = tower_zero_fp();
    bw6_761_sub(&mut neg, &tower_zero_fp(), &tower_one_mont());
    assert_eq!(out.c1.c0.0, neg.0, "frob_p3.c1.c0 = -x.c1.c0");
    assert_eq!(out.c1.c1.0, neg.0, "frob_p3.c1.c1 = -x.c1.c1");
    assert_eq!(out.c1.c2.0, neg.0, "frob_p3.c1.c2 = -x.c1.c2");
}

/// gnark-crypto cross-check.  IGNORED pending an extracted
/// reference vector.
///
/// Status update (Phase 1 of the Frobenius math-fix, 2026-05-21):
/// the real Frobenius constants ARE now in place
/// (`BW6_761_FrobConsts.v` ships `alpha = (-4)^((p-1)/3)` and the
/// 11 derived scalars), the bedrock2 body has been switched to a
/// per-Fp-component implementation matching gnark's
/// `internal/fptower/frobenius.go`, and the algebraic
/// sanity check `fp6_frob_p3_negates_c1` above passes.
///
/// What remains for this KAT: gnark-crypto's
/// `ecc/bw6-761/pairing_test.go` ships no hardcoded `e(g1Gen,
/// g2Gen)` vector, so the canonical reference value would need to
/// be extracted by running gnark's `Pair(g1Gen, g2Gen)` once and
/// dumping the 6×Fp Montgomery-form limbs.  That extraction is
/// out of scope for the bedrock2/Coq work here.
#[test]
#[ignore = "needs an extracted gnark reference vector for e(g1Gen, g2Gen)"]
fn pairing_kat_gnark_generator() {
    // TODO(post-gnark-extraction):
    //   1. Run gnark's `Pair(g1Gen, g2Gen)` and dump the 6×12 u64
    //      Montgomery-form limbs into `EXPECTED_E_G_G`.
    //   2. Assert pairing(g1Gen, g2Gen, gammas...) == EXPECTED_E_G_G
    //      using the `real_frob_consts()` helper above.
    // (The bedrock2 Frobenius bodies + spec are now math-correct;
    //  this is purely a fixture-data task.)
    unimplemented!("needs gnark reference vector");
}
