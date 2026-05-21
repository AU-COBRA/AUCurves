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

// ====== gnark-crypto reference vector (extracted 2026-05-21 via
//        Docker golang:1.25 + gnark-crypto v0.20.1).
//
// G1 generator (affine, Montgomery-form Fp limbs little-endian u64):
const G1_GEN_X: [u64; 12] = [
    0xd6e42d7614c2d770, 0x4bb886eddbc3fc21, 0x64648b044098b4d2, 0x1a585c895a422985,
    0xf1a9ac17cf8685c9, 0x352785830727aea5, 0xddf8cb12306266fe, 0x6913b4bfbc9e949a,
    0x3a4b78d67ba5f6ab, 0x0f481c06a8d02a04, 0x91d4e7365c43edac, 0x00f4d17cd48beca5,
];
const G1_GEN_Y: [u64; 12] = [
    0x97e805c4bd16411f, 0x870d844e1ee6dd08, 0x1eba7a37cb9eab4d, 0xd544c4df10b9889a,
    0x8fe37f21a33897be, 0xe9bf99a43a0885d2, 0xd7ee0c9e273de139, 0xaa6a9ec7a38dd791,
    0x8f95d3fcf765da8e, 0x42326e7db7357c99, 0xe217e407e218695f, 0x009d1eb23b7cf684,
];
// G2 generator: gnark stores g2Gen.X and .Y as plain `fp.Element` (Fp,
// NOT Fp3) — BW6-761 places G2 over the base field Fp.  Our bedrock
// Miller-loop body takes G2 coords as `Fp3`, so we embed the Fp
// coordinate into the c0 slot of a degenerate Fp3 with c1 = c2 = 0.
const G2_GEN_X: [u64; 12] = [
    0x3d902a84cd9f4f78, 0x864e451b8a9c05dd, 0xc2b3c0d6646c5673, 0x17a7682def1ecb9d,
    0xbe31a1e0fb768fe3, 0x4df125e09b92d1a6, 0x0943fce635b02ee9, 0xffc8e7ad0605e780,
    0x8165c00a39341e95, 0x8ccc2ae90a0f094f, 0x73a8b8cc0ad09e0c, 0x011027e203edd9f4,
];
const G2_GEN_Y: [u64; 12] = [
    0x9a159be4e773f67c, 0x6b957244aa8f4e6b, 0xa27b70c9c945a38c, 0xacb6a09fda11d0ab,
    0x3abbdaa9bb6b1291, 0xdbdf642af5694c36, 0xb6360bb9560b369f, 0xac0bd1e822b8d6da,
    0xfa355d17afe6945f, 0x8d6a0fc1fbcad35e, 0x72a63c7874409840, 0x0114976e5b0db280,
];

// e(g1Gen, g2Gen) — Fp6 = Fp3[w]/(w^2 − v) over Fp3 = Fp[u]/(u^3 − nr).
// Layout: [B0.A0, B0.A1, B0.A2, B1.A0, B1.A1, B1.A2], each Fp in
// Montgomery little-endian u64 limbs.  Cross-checked against
// gnark-crypto's R = 2^768 mod p (Mont(1) limbs identical to
// fiat-rust's fiat_bw6_761_set_one).
const EXPECTED_E_G_G: [[u64; 12]; 6] = [
    // B0.A0
    [0xda51326b6fa8e240, 0xdd7db828ed3de6e6, 0x94ea9aec011ebbcc, 0xf67647a828e9badb,
     0xe75d2138fe0d93b0, 0xb9eaf32a785c376d, 0x7b06980c79024b43, 0x05d6dc3e38c57d11,
     0xfc6b96fed138a2fb, 0x5115d0534afe2b16, 0x5c65118ec3473b96, 0x011b3a30623f9a42],
    // B0.A1
    [0x4c0692e5020858ff, 0x8b6c29755a5640bb, 0x3cb595c5d085734f, 0x88ee6eb4cbaefc1d,
     0x260f17fa99e0a117, 0xab72ee4400287fc3, 0x1c83f7e1f1975c17, 0xc4282ac34174807c,
     0x09a9a715c595397a, 0x9314c8719434fee8, 0x027ac209570f6bb9, 0x00ec4f37fb4d2659],
    // B0.A2
    [0xa7ae5aab6fe33c25, 0xfe7ab0e37b26649b, 0x4c1292960de81e5a, 0xba88a980549b1565,
     0xfda13b7c9fc4bf85, 0xef24725be0be887b, 0xad5d72e68c8f5219, 0xfb0e2241f26fd755,
     0x291fed7a530a1aed, 0x051e6df82d43afd1, 0xdcf4c7deee6afc10, 0x00428a4150b9b367],
    // B1.A0
    [0x8be5ef98b1592033, 0xd0be811aa2adca7c, 0xbff996396a818832, 0xa8327bdcfdf6613a,
     0x2396125fcfc55400, 0x97c87b57ece24176, 0xf041251b50c1e480, 0xe029f1a50a6783af,
     0x514cacf665706a77, 0xf3a689a5e2014904, 0x606842d11a886c7e, 0x00147b66f40bd446],
    // B1.A1
    [0xee8368caaf4231de, 0xd9082150fe5d99c4, 0x773d13e02a992aa5, 0xb7a1f406948d5bf6,
     0xbbc8d519aaaa889e, 0xbf0ab277a54844fa, 0x6811c936a76d06f5, 0xe5d2f875746f940a,
     0x9f00454249049970, 0xf232b1e330965b1e, 0xf09015c606488b93, 0x00e4c4d2bd430393],
    // B1.A2
    [0xdc38bfe1f0553469, 0xc4bdf705ee7c7041, 0x35e41da6adbc20e6, 0x86d8017a12f6a876,
     0x71d4701e3b4504ba, 0xd92add80f3a8f2dd, 0xe3bb42ef14e544e3, 0x7a6fe26d963c2cd7,
     0xa92079b23e782482, 0xb3c00e82e789516d, 0x11d64586abdfc4df, 0x0094e2eadc90c9ff],
];

/// gnark-crypto cross-check on `e(g1Gen, g2Gen)` for BW6-761.
///
/// The G1/G2 generators and reference Fp6 value above come from
/// running `bw6761.Pair([]G1Affine{g1Gen}, []G2Affine{g2Gen})`
/// against gnark-crypto v0.20.1 (extracted 2026-05-21 via Docker
/// golang:1.25).  Both gnark and our fiat-rust backend use
/// Montgomery form with R = 2^768 mod p and little-endian u64 limbs,
/// so the limbs can be compared bit-for-bit with no re-encoding.
/// (Cross-checked: gnark's `Mont(1)` matches `fiat_bw6_761_set_one`
/// exactly.)
///
/// Currently `#[ignore]`'d: while the fixture data is now in place
/// and the test runs end-to-end without panicking, the value
/// produced by our `pairing(...)` does NOT match the gnark reference.
/// Per `PENDING.md` items 2+4: BW6-761 is a Brezing-Weng curve over
/// BLS12-377 whose canonical optimal-ate pairing needs *two* Miller
/// loops over two different seeds plus a per-curve final adjustment
/// (not expressible by the current `CurveParams` record's
/// `optimal_ate_extras := []`).  The currently-extracted bedrock2
/// `bw6_761_miller_loop` runs a single 64-bit loop over the
/// BLS12-377 seed `0x8508c00000000001`, which is the *wrong* loop
/// structure for BW6-761.  Unblocking this KAT requires the new
/// `BW6_761_MillerLoop.v` / `BW6_761_FinalExp.v` (~1500 LoC of new
/// Rocq proof work) called out in `PENDING.md`.
///
/// Once those land, removing `#[ignore]` below should be the only
/// change needed in this file — the gnark fixture is already
/// frozen in `EXPECTED_E_G_G`.
#[test]
#[ignore = "gnark fixture in place, but bedrock2 Miller body uses single BLS12-377-seed loop; needs proper two-loop BW6 optimal-ate (PENDING.md items 2+4). Run with --ignored to see exact mismatch."]
fn pairing_kat_gnark_generator() {
    use tower::{Fp3 as TFp3, Fp6 as TFp6};

    let g1 = G1 {
        x: tower::Fp(G1_GEN_X),
        y: tower::Fp(G1_GEN_Y),
    };
    // BW6-761 G2 lives over Fp (not Fp3); embed gnark's Fp coords in
    // the c0 slot of a degenerate Fp3 with c1 = c2 = 0.
    let g2 = G2 {
        x: TFp3 { c0: tower::Fp(G2_GEN_X), c1: tower_zero_fp(), c2: tower_zero_fp() },
        y: TFp3 { c0: tower::Fp(G2_GEN_Y), c1: tower_zero_fp(), c2: tower_zero_fp() },
    };

    let (gamma_fp3, gamma_fp6, gamma_fp3_p2, gamma_fp6_p2, gamma_fp6_p3) =
        real_frob_consts();

    let zero_fp3 = TFp3 { c0: tower_zero_fp(), c1: tower_zero_fp(), c2: tower_zero_fp() };
    let mut out = TFp6 { c0: zero_fp3, c1: zero_fp3 };
    pairing(&mut out, &g1, &g2,
            &gamma_fp3, &gamma_fp6,
            &gamma_fp3_p2, &gamma_fp6_p2, &gamma_fp6_p3);

    assert_eq!(out.c0.c0.0, EXPECTED_E_G_G[0], "e(g1,g2).B0.A0 mismatch");
    assert_eq!(out.c0.c1.0, EXPECTED_E_G_G[1], "e(g1,g2).B0.A1 mismatch");
    assert_eq!(out.c0.c2.0, EXPECTED_E_G_G[2], "e(g1,g2).B0.A2 mismatch");
    assert_eq!(out.c1.c0.0, EXPECTED_E_G_G[3], "e(g1,g2).B1.A0 mismatch");
    assert_eq!(out.c1.c1.0, EXPECTED_E_G_G[4], "e(g1,g2).B1.A1 mismatch");
    assert_eq!(out.c1.c2.0, EXPECTED_E_G_G[5], "e(g1,g2).B1.A2 mismatch");
}

// =====================================================================
// G1/G2 group ops smoke tests (reference Rust over verified tower)
// =====================================================================

#[test]
fn g1_neg_of_inf_is_inf() {
    use crate::group::*;
    let inf = G1Aff::inf();
    assert_eq!(g1_neg(&inf), G1Aff::Inf);
}

#[test]
fn g1_double_of_inf_is_inf() {
    use crate::group::*;
    let inf = G1Aff::inf();
    assert_eq!(g1_double(&inf), G1Aff::Inf);
}

#[test]
fn g1_add_inf_is_identity() {
    use crate::group::*;
    let inf = G1Aff::inf();
    let one_pt = G1Aff::pt(tower_one_mont(), tower_one_mont());
    assert_eq!(g1_add(&inf, &one_pt), one_pt);
    assert_eq!(g1_add(&one_pt, &inf), one_pt);
}

#[test]
fn g1_scalar_mul_zero_gives_inf() {
    use crate::group::*;
    let p = G1Aff::pt(tower_one_mont(), tower_one_mont());
    assert_eq!(g1_scalar_mul(&[0u8; 4], &p), G1Aff::Inf);
}

#[test]
fn g1_scalar_mul_one_returns_point() {
    use crate::group::*;
    let p = G1Aff::pt(tower_one_mont(), tower_one_mont());
    // scalar = 1 (last bit set) → result = p
    assert_eq!(g1_scalar_mul(&[1u8], &p), p);
}

#[test]
fn g2_neg_of_inf_is_inf() {
    use crate::group::*;
    let inf = G2Aff::inf();
    assert_eq!(g2_neg(&inf), G2Aff::Inf);
}

#[test]
fn g2_double_of_inf_is_inf() {
    use crate::group::*;
    let inf = G2Aff::inf();
    assert_eq!(g2_double(&inf), G2Aff::Inf);
}

#[test]
fn g2_add_inf_is_identity() {
    use crate::group::*;
    use tower::Fp3;
    let inf = G2Aff::inf();
    let one_fp3 = Fp3 { c0: tower_one_mont(), c1: tower_zero_fp(), c2: tower_zero_fp() };
    let p = G2Aff::pt(one_fp3, one_fp3);
    assert_eq!(g2_add(&inf, &p), p);
    assert_eq!(g2_add(&p, &inf), p);
}

#[test]
fn g2_scalar_mul_zero_gives_inf() {
    use crate::group::*;
    use tower::Fp3;
    let one_fp3 = Fp3 { c0: tower_one_mont(), c1: tower_zero_fp(), c2: tower_zero_fp() };
    let p = G2Aff::pt(one_fp3, one_fp3);
    assert_eq!(g2_scalar_mul(&[0u8; 4], &p), G2Aff::Inf);
}

#[test]
fn g2_scalar_mul_one_returns_point() {
    use crate::group::*;
    use tower::Fp3;
    let one_fp3 = Fp3 { c0: tower_one_mont(), c1: tower_zero_fp(), c2: tower_zero_fp() };
    let p = G2Aff::pt(one_fp3, one_fp3);
    assert_eq!(g2_scalar_mul(&[1u8], &p), p);
}

#[test]
fn hash_to_g1_stub_returns_none() {
    use crate::group::*;
    assert!(hash_to_g1(b"hello", b"BW6-761-DST").is_none());
}

#[test]
fn hash_to_g2_stub_returns_none() {
    use crate::group::*;
    assert!(hash_to_g2(b"hello", b"BW6-761-DST").is_none());
}
