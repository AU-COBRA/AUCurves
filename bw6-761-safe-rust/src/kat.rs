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

// gnark-crypto's `thirdRootOneG1` in Montgomery form (LE u64).  Cube
// root of unity over Fp used to build the G2 endomorphism image
// q1.X = thirdRootOneG1 · q0.X in the optimal-ate Miller loop.
// (Cross-checked 2026-05-22 against gnark-crypto v0.20.1's
// `bw6-761.go::thirdRootOneG1.SetString(...)`.)
const THIRD_ROOT_ONE_G1_MONT: [u64; 12] = [
    0x67a04ae427bfb5f8, 0x9d32d491eb6a5cff, 0x43d03c1cb68051d4, 0x0b75ca96f69859a5,
    0x0763497f5325ec60, 0x48076b5c278dd94d, 0x8ca3965ff91efd06, 0x1e6077657ea02f5d,
    0xcdd6c153a8c37724, 0x28b5b634e5c22ea4, 0x9e01e3efd42e902c, 0x00e3d6815769a804,
];

// half_fp = (p+1)/2 mod p in Montgomery form (LE u64).  Multiplied
// by Fp elements inside `bw6_761_g2_double_step` to perform the halve
// step (avoids needing a runtime Fp inversion per iteration).
const HALF_FP_MONT: [u64; 12] = [
    0xfb4fffffffffc330, 0x2074b24effffc6b4, 0x5a53337936b8278b, 0x39860afa32a61376,
    0x2f634f8d48c05b9d, 0x23b81847b2a110ce, 0x558e305f8130ae05, 0xc9e7471b95da050e,
    0xe6ec6737c49cc35e, 0xff5551673471245b, 0x5497f3fdd230548e, 0x00ba6fd1f655db44,
];

fn fp_from_raw(r: &FpRaw) -> tower::Fp {
    let mut out = zero();
    fp_to_montgomery(&mut out, r);
    tower::Fp(out.0)
}

// sqrt(alpha) = (-4)^((p-1)/6) mod p, computed via Tonelli-Shanks
// (the branch picked by gnark-crypto's `Frobenius`); cross-checked
// 2026-05-22 against gnark v0.20.1 via `Frob(v).B1.A0`.  In Mont
// limbs (LE u64).
fn sa_raw() -> FpRaw {
    // canonical (non-Mont) value: (-4)^((p-1)/6) mod p
    // = alpha + 1 (since alpha's last byte is 0x60 and sa's is 0x61).
    let mut a = alpha_raw().0;
    a[0] = a[0].wrapping_add(1);
    FpRaw(a)
}

/// Build the 5 BW6-761 Frobenius gamma constants in Montgomery form,
/// laid out as Fp3 blobs (cross-checked 2026-05-22 against gnark's
/// `Frobenius` on basis vectors u, u², v, v·u, v·u² in `internal/
/// fptower`):
///
///   gamma_fp3 (pi)   = (_, α, α²)
///   gamma_fp6 (pi)   = (sa, sa·α, sa·α²) = (sa, −1, −α)
///   gamma_fp3_p2     = (_, α², α)
///   gamma_fp6_p2     = (α, α², 1)
///   gamma_fp6_p3     = (−1, −α, −α²)
///
/// where α = (−4)^((p−1)/3), sa = (−4)^((p−1)/6), and the Fp identities
/// `sa² = α`, `α³ = 1`, `sa³ = −1`, `sa·α = −1`, `sa·α² = −α` hold.
fn real_frob_consts() -> (tower::Fp3, tower::Fp3, tower::Fp3, tower::Fp3, tower::Fp3) {
    use tower::Fp3;
    let alpha = fp_from_raw(&alpha_raw());
    let alpha_sq = fp_from_raw(&alpha_sq_raw());
    let sa = fp_from_raw(&sa_raw());
    let one_mont = tower_one_mont();
    let minus_one = fp_from_raw(&minus_one_raw());
    // Compute −α, −α² in Mont.
    let mut neg_alpha = tower::Fp::zero();
    let mut neg_alpha_sq = tower::Fp::zero();
    let zero_fp = tower_zero_fp();
    tower::bw6_761_sub(&mut neg_alpha, &zero_fp, &alpha);
    tower::bw6_761_sub(&mut neg_alpha_sq, &zero_fp, &alpha_sq);

    let gamma_fp3    = Fp3 { c0: zero_fp, c1: alpha,        c2: alpha_sq    };
    let gamma_fp6    = Fp3 { c0: sa,      c1: minus_one,    c2: neg_alpha   };
    let gamma_fp3_p2 = Fp3 { c0: zero_fp, c1: alpha_sq,     c2: alpha       };
    let gamma_fp6_p2 = Fp3 { c0: alpha,   c1: alpha_sq,     c2: one_mont    };
    let gamma_fp6_p3 = Fp3 { c0: minus_one, c1: neg_alpha,  c2: neg_alpha_sq };
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
    let trog1 = tower::Fp(THIRD_ROOT_ONE_G1_MONT);
    let halff = tower::Fp(HALF_FP_MONT);
    pairing(&mut out, &p, &q,
            &gamma_fp3, &gamma_fp6,
            &gamma_fp3_p2, &gamma_fp6_p2, &gamma_fp6_p3,
            &trog1, &halff);
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
// gnark MillerLoop (no final exp) on (g1Gen, g2Gen).  Used to
// validate the Miller loop wiring independently of the final
// exponentiation.  Extracted 2026-05-22 from gnark-crypto v0.20.1.
const EXPECTED_MILLER_NO_FINEXP: [[u64; 12]; 6] = [
    [0x1fbfed9d99f36d94, 0xcae699fb8e03a388, 0x2a9685e28b2ebfcd, 0x7749dd7d3146f60d,
     0x99a85250cb88ec63, 0x9bb285813a6bcf26, 0x89230deab7f930a5, 0x7732a7b3eaa86eef,
     0xaf3d98c1c9af6bca, 0xfb1342b6f164a729, 0x1683da66d213f591, 0x00619d8e2a563d8c],
    [0xd46699f6d5483424, 0x8ae8909c8818ab8c, 0x15b9197ec42a3f2f, 0x1774cdbb6bc1bade,
     0xf7ca9deb0bcf0559, 0x0b4fc78712b59ebb, 0x80cd331637f47416, 0x86dc3ad12cf4d982,
     0x718dcebdfeb1f607, 0x5e2a0bd67cbb6357, 0xab34e56a24c9e8c4, 0x00d1b86fffc53d17],
    [0xe62c6b34e40c99fe, 0x4558b170cc57f005, 0xee28d41b57df87ea, 0x1e01ef638ed9692a,
     0x93ee057ad0e0b2ec, 0xb6c9afdae1a00299, 0x75a92fb8d1ec21d6, 0x9a7754481709b92c,
     0x05d1286982923de0, 0xbf06fafd5f257729, 0xac938fdd41a822e5, 0x003e9864d35feba6],
    [0x7f6a5350754f8026, 0x318602dc3b413207, 0x653382163e6f5d1d, 0x234108fb2aef6d6a,
     0x6c8a96f3d2233ea6, 0x87dc776fcade057c, 0x4d9563ce7f31cb8f, 0x8842da432dd2b31f,
     0x5c7c2aaa9fd0d71e, 0x5c525bf3b071af88, 0xf2e4daa18a0376b4, 0x004894f0fe845fb9],
    [0xaff9847ba19eba31, 0xd89ba6390a620db1, 0xd50a95ddabe4fda2, 0x6bde5f1e2be3669b,
     0x813bb79d46c2ebae, 0x2d06b7884cbfdf3c, 0xa7c4a815ed9632f1, 0xefe9099aa0b731d0,
     0x80c605b5edcecdc6, 0xb7a1ae27f41a599b, 0x1bd2414fe996a297, 0x011d97e1aace77d8],
    [0x707e10739b6eeef8, 0x82f0cfde2593193d, 0xef660b2ec9baaf9c, 0x1b37adc2f23b408e,
     0x437bcb9596e84c03, 0xe22ef4e9b7c94fec, 0xff5b96e01661dad5, 0xc993578d379857c7,
     0x55ff245cd7f8e42b, 0xf4fa100fa6d6f345, 0xf78918fa2c238b4d, 0x004368cdd4a0c110],
];

// gnark's "after easy" Fp6 value: r = f^((p^3-1)(p+1)) where
// f = MillerLoop(g1Gen, g2Gen).  Used to validate the easy part of
// our final-exp in isolation from the hard-part chain.
const EXPECTED_AFTER_EASY_B0_A0: [u64; 12] = [
    0x57b2c24e0bb1bbc5, 0xa6cbdb2c6911617d, 0xa6def870b7f25063, 0x265d4851e7ecf0d5,
    0x4be47834eb848906, 0xb9ca660b74e840a8, 0x30217705c11abb49, 0xdc7d6040240b111b,
    0xa33c2d889b4a098f, 0xd36e3a50cb350524, 0x76a2acf53544b439, 0x01169f63ca3fa64e,
];

/// Diagnostic: extract our final-exp easy-part output and compare
/// against gnark's reference value on (g1Gen, g2Gen).
#[test]
fn final_exp_easy_kat() {
    use tower::{Fp3 as TFp3, Fp6 as TFp6,
                bw6_761_miller_loop_optimal, bw6_final_exp_easy,
                bw6_761_Fp3_mul_fp, bw6_761_Fp3_opp,
                bw6_761_Fp3_felem_copy};
    // Reuse the miller-only setup.
    let qx = TFp3 { c0: tower::Fp(G2_GEN_X), c1: tower_zero_fp(), c2: tower_zero_fp() };
    let qy = TFp3 { c0: tower::Fp(G2_GEN_Y), c1: tower_zero_fp(), c2: tower_zero_fp() };
    let trog1 = tower::Fp(THIRD_ROOT_ONE_G1_MONT);
    let halff = tower::Fp(HALF_FP_MONT);
    let mut q1x = TFp3 { c0: tower_zero_fp(), c1: tower_zero_fp(), c2: tower_zero_fp() };
    let mut q1y = TFp3 { c0: tower_zero_fp(), c1: tower_zero_fp(), c2: tower_zero_fp() };
    let mut q0ny = TFp3 { c0: tower_zero_fp(), c1: tower_zero_fp(), c2: tower_zero_fp() };
    let mut q1ny = TFp3 { c0: tower_zero_fp(), c1: tower_zero_fp(), c2: tower_zero_fp() };
    bw6_761_Fp3_mul_fp(&mut q1x, &qx, &trog1);
    bw6_761_Fp3_opp(&mut q1y, &qy);
    bw6_761_Fp3_opp(&mut q0ny, &qy);
    bw6_761_Fp3_felem_copy(&mut q1ny, &qy);
    let p_x = tower::Fp(G1_GEN_X);
    let p_y = tower::Fp(G1_GEN_Y);
    let zero_fp3 = TFp3 { c0: tower_zero_fp(), c1: tower_zero_fp(), c2: tower_zero_fp() };
    let mut f = TFp6 { c0: zero_fp3, c1: zero_fp3 };
    bw6_761_miller_loop_optimal(
        &mut f, &p_x, &p_y, &qx, &qy, &q1x, &q1y, &q0ny, &q1ny, &halff,
    );
    let (gamma_fp3, gamma_fp6, _g3p2, _g6p2, _g6p3) = real_frob_consts();
    let mut r = TFp6 { c0: zero_fp3, c1: zero_fp3 };
    bw6_final_exp_easy(&mut r, &f, &gamma_fp3, &gamma_fp6);
    eprintln!("our after-easy B0.A0 = {:016x?}", r.c0.c0.0);
    eprintln!("gnark after-easy B0.A0 = {:016x?}", EXPECTED_AFTER_EASY_B0_A0);
    assert_eq!(r.c0.c0.0, EXPECTED_AFTER_EASY_B0_A0,
               "final-exp easy part B0.A0 mismatch");
}

/// Independent check that just our Miller-loop body (without final
/// exponentiation) matches gnark's reference.  Validates the
/// q1 = (thirdRootOneG1·q0.X, −q0.Y) wiring + half_fp constant
/// independently from the final-exp / Frobenius issues.
#[test]
fn miller_loop_only_kat() {
    use tower::{Fp3 as TFp3, Fp6 as TFp6,
                bw6_761_miller_loop_optimal,
                bw6_761_Fp3_mul_fp, bw6_761_Fp3_opp,
                bw6_761_Fp3_felem_copy};

    let qx = TFp3 { c0: tower::Fp(G2_GEN_X), c1: tower_zero_fp(), c2: tower_zero_fp() };
    let qy = TFp3 { c0: tower::Fp(G2_GEN_Y), c1: tower_zero_fp(), c2: tower_zero_fp() };

    let trog1 = tower::Fp(THIRD_ROOT_ONE_G1_MONT);
    let halff = tower::Fp(HALF_FP_MONT);

    let mut q1x = TFp3 { c0: tower_zero_fp(), c1: tower_zero_fp(), c2: tower_zero_fp() };
    let mut q1y = TFp3 { c0: tower_zero_fp(), c1: tower_zero_fp(), c2: tower_zero_fp() };
    let mut q0ny = TFp3 { c0: tower_zero_fp(), c1: tower_zero_fp(), c2: tower_zero_fp() };
    let mut q1ny = TFp3 { c0: tower_zero_fp(), c1: tower_zero_fp(), c2: tower_zero_fp() };
    bw6_761_Fp3_mul_fp(&mut q1x, &qx, &trog1);
    bw6_761_Fp3_opp(&mut q1y, &qy);
    bw6_761_Fp3_opp(&mut q0ny, &qy);
    bw6_761_Fp3_felem_copy(&mut q1ny, &qy);

    let p_x = tower::Fp(G1_GEN_X);
    let p_y = tower::Fp(G1_GEN_Y);

    let zero_fp3 = TFp3 { c0: tower_zero_fp(), c1: tower_zero_fp(), c2: tower_zero_fp() };
    let mut f = TFp6 { c0: zero_fp3, c1: zero_fp3 };
    bw6_761_miller_loop_optimal(
        &mut f,
        &p_x, &p_y,
        &qx, &qy,
        &q1x, &q1y,
        &q0ny, &q1ny,
        &halff,
    );

    let label = ["B0.A0", "B0.A1", "B0.A2", "B1.A0", "B1.A1", "B1.A2"];
    let got = [f.c0.c0.0, f.c0.c1.0, f.c0.c2.0, f.c1.c0.0, f.c1.c1.0, f.c1.c2.0];
    for k in 0..6 {
        if got[k] != EXPECTED_MILLER_NO_FINEXP[k] {
            eprintln!("Miller mismatch at {}", label[k]);
            eprintln!("got    : {:016x?}", got[k]);
            eprintln!("expect : {:016x?}", EXPECTED_MILLER_NO_FINEXP[k]);
        }
        assert_eq!(got[k], EXPECTED_MILLER_NO_FINEXP[k],
                   "miller loop {} mismatch", label[k]);
    }
}

#[test]
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
    let trog1 = tower::Fp(THIRD_ROOT_ONE_G1_MONT);
    let halff = tower::Fp(HALF_FP_MONT);

    let zero_fp3 = TFp3 { c0: tower_zero_fp(), c1: tower_zero_fp(), c2: tower_zero_fp() };
    let mut out = TFp6 { c0: zero_fp3, c1: zero_fp3 };
    pairing(&mut out, &g1, &g2,
            &gamma_fp3, &gamma_fp6,
            &gamma_fp3_p2, &gamma_fp6_p2, &gamma_fp6_p3,
            &trog1, &halff);

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

// =====================================================================
// Projective (RCB a = 0) G1 vs the affine reference
//
// The affine chain (`g1_double`, `g1_add`, `g1_scalar_mul_affine`)
// spends one `fp_inv` per group operation; the projective chain
// (`g1_proj_double_extracted` = RCB Algorithm 9, `g1_proj_add` = RCB
// Algorithm 7) spends none, and `g1_scalar_mul` inverts once at the
// end.  These tests pin the two chains to the same function.
// =====================================================================

fn g1_gen() -> crate::group::G1Aff {
    crate::group::G1Aff::pt(tower::Fp(G1_GEN_X), tower::Fp(G1_GEN_Y))
}

/// The curve constant used by [`g1_three_b`] is only correct if
/// BW6-761 G1 really is `y² = x³ − 1`.  Check it on the generator.
#[test]
fn g1_curve_b_is_minus_one() {
    use tower::{Fp, bw6_761_mul, bw6_761_sub, bw6_761_from_word,
                bw6_761_opp};
    let x = Fp(G1_GEN_X);
    let y = Fp(G1_GEN_Y);
    let mut y2 = Fp::zero(); bw6_761_mul(&mut y2, &y, &y);
    let mut x2 = Fp::zero(); bw6_761_mul(&mut x2, &x, &x);
    let mut x3 = Fp::zero(); bw6_761_mul(&mut x3, &x2, &x);
    let mut b = Fp::zero(); bw6_761_sub(&mut b, &y2, &x3);
    let mut one = Fp::zero(); bw6_761_from_word(&mut one, 1u64);
    let mut minus_one = Fp::zero(); bw6_761_opp(&mut minus_one, &one);
    assert_eq!(b, minus_one, "BW6-761 G1 is not y^2 = x^3 - 1");
    // ... and therefore 3b = -3, which is what g1_three_b returns.
    let mut three = Fp::zero(); bw6_761_from_word(&mut three, 3u64);
    let mut minus_three = Fp::zero(); bw6_761_opp(&mut minus_three, &three);
    assert_eq!(crate::group::g1_three_b(), minus_three);
}

/// The hand transcription of `rcb_double_a0_gallina` that this crate
/// used to SHIP as `group::g1_proj_double`, retained here as the test
/// oracle for the Rocq-emitted body that replaced it (see
/// [`g1_alg9_extracted_matches_handwritten`]).  Independent code —
/// struct-typed `Fp` throughout, no byte buffers, the paper's in-place
/// buffer reuse rather than SSA slots — so agreement between the two
/// is evidence about both.
///
/// Steps 1 and 6 are squarings written as `mul`, following
/// `CurveDoubleA3.v`'s PORT-CHECK (S); BW6-761's `fp_square` leaf is
/// in fact 13% SLOWER than `fp_mul` (230 ns against 203 ns; see
/// `examples/bench_g1.rs`), so nothing is given up by that.
fn g1_proj_double_handwritten(P: &crate::group::G1Proj, b3: &tower::Fp)
    -> crate::group::G1Proj
{
    use crate::group::G1Proj;
    use tower::{bw6_761_add as fp_add_t, bw6_761_mul as fp_mul_t,
                bw6_761_sub as fp_sub_t, Fp as TFp};
    let (x, y, z) = (P.x, P.y, P.z);
    let mut u = TFp::zero();
    let mut t0 = TFp::zero(); fp_mul_t(&mut t0, &y, &y);     // 1
    let mut z3 = TFp::zero(); fp_add_t(&mut z3, &t0, &t0);   // 2
    fp_add_t(&mut u, &z3, &z3); z3 = u;                      // 3
    fp_add_t(&mut u, &z3, &z3); z3 = u;                      // 4
    let mut t1 = TFp::zero(); fp_mul_t(&mut t1, &y, &z);     // 5
    let mut t2 = TFp::zero(); fp_mul_t(&mut t2, &z, &z);     // 6
    fp_mul_t(&mut u, b3, &t2); t2 = u;                       // 7
    let mut x3 = TFp::zero(); fp_mul_t(&mut x3, &t2, &z3);   // 8
    let mut y3 = TFp::zero(); fp_add_t(&mut y3, &t0, &t2);   // 9
    fp_mul_t(&mut u, &t1, &z3); z3 = u;                      // 10
    fp_add_t(&mut u, &t2, &t2); t1 = u;                      // 11
    fp_add_t(&mut u, &t1, &t2); t2 = u;                      // 12
    fp_sub_t(&mut u, &t0, &t2); t0 = u;                      // 13
    fp_mul_t(&mut u, &t0, &y3); y3 = u;                      // 14
    fp_add_t(&mut u, &x3, &y3); y3 = u;                      // 15
    fp_mul_t(&mut u, &x, &y); t1 = u;                        // 16
    fp_mul_t(&mut u, &t0, &t1); x3 = u;                      // 17
    fp_add_t(&mut u, &x3, &x3); x3 = u;                      // 18
    G1Proj { x: x3, y: y3, z: z3 }
}

/// Algorithm 9 against the affine doubling, on 2^k·G for k = 0..15.
#[test]
fn g1_proj_double_matches_affine() {
    use crate::g1_double_a0_extracted::g1_proj_double_extracted;
    use crate::group::*;
    let mut aff = g1_gen();
    let mut proj = g1_to_proj(&aff);
    for k in 0..16 {
        aff = g1_double(&aff);
        proj = g1_proj_double_extracted(&proj);
        assert_eq!(g1_from_proj(&proj), aff, "doubling mismatch at k={k}");
    }
}

/// Algorithm 9 against Algorithm 7 applied to a repeated argument —
/// the Rust image of `rcb_double_a0_eq_ladderstep`.  On-curve inputs,
/// so the two agree coordinate for coordinate, rather than only up to
/// the projective equivalence.
#[test]
fn g1_alg9_equals_alg7_self_add_on_the_nose() {
    use crate::g1_double_a0_extracted::g1_proj_double_extracted;
    use crate::group::*;
    let b3 = g1_three_b();
    let mut p = g1_to_proj(&g1_gen());
    for k in 0..16 {
        let by_double = g1_proj_double_extracted(&p);
        let by_self_add = g1_proj_add(&p, &p, &b3);
        assert_eq!(by_double, by_self_add,
                   "Alg 9 != Alg 7(P,P) at k={k}");
        p = by_double;
    }
    // Also at the identity, where Z = 0.
    let inf = g1_proj_inf();
    assert_eq!(g1_proj_double_extracted(&inf), g1_proj_add(&inf, &inf, &b3));
}

/// Algorithm 7 against the affine addition.
#[test]
fn g1_proj_add_matches_affine() {
    use crate::group::*;
    let b3 = g1_three_b();
    let g = g1_gen();
    let mut acc_aff = g;
    let mut acc_proj = g1_to_proj(&g);
    for k in 0..16 {
        acc_aff = g1_add(&acc_aff, &g);
        acc_proj = g1_proj_add(&acc_proj, &g1_to_proj(&g), &b3);
        assert_eq!(g1_from_proj(&acc_proj), acc_aff,
                   "addition mismatch at k={k}");
    }
}

/// Completeness: the projective formulas need no special case for the
/// identity or for `P + (−P)`, where the affine chain branches.
#[test]
fn g1_proj_add_is_complete() {
    use crate::group::*;
    let b3 = g1_three_b();
    let g = g1_gen();
    let gp = g1_to_proj(&g);
    let inf = g1_proj_inf();
    assert_eq!(g1_from_proj(&g1_proj_add(&inf, &gp, &b3)), g);
    assert_eq!(g1_from_proj(&g1_proj_add(&gp, &inf, &b3)), g);
    assert_eq!(
        g1_from_proj(&crate::g1_double_a0_extracted::g1_proj_double_extracted(&inf)),
        G1Aff::Inf);
    let neg_gp = g1_to_proj(&g1_neg(&g));
    assert_eq!(g1_from_proj(&g1_proj_add(&gp, &neg_gp, &b3)), G1Aff::Inf);
}

/// The headline differential test: projective and affine scalar
/// multiplication agree on a spread of scalars.
#[test]
fn g1_scalar_mul_projective_matches_affine() {
    use crate::group::*;
    let g = g1_gen();
    let scalars: [&[u8]; 8] = [
        &[0u8],
        &[1u8],
        &[2u8],
        &[0xff],
        &[0x01, 0x00],
        &[0xde, 0xad, 0xbe, 0xef],
        &[0x00, 0x00, 0x12, 0x34, 0x56, 0x78],
        &[0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
          0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef],
    ];
    for s in scalars {
        assert_eq!(g1_scalar_mul(s, &g), g1_scalar_mul_affine(s, &g),
                   "scalar mul mismatch on {s:02x?}");
    }
}

/// `(m + n)·G = m·G + n·G` through the projective path.
#[test]
fn g1_scalar_mul_projective_is_additive() {
    use crate::group::*;
    let g = g1_gen();
    let m = g1_scalar_mul(&[0x00, 0x2a], &g);   // 42
    let n = g1_scalar_mul(&[0x00, 0x64], &g);   // 100
    let sum = g1_scalar_mul(&[0x00, 0x8e], &g); // 142
    assert_eq!(g1_add(&m, &n), sum);
}

#[test]
fn g1_scalar_mul_projective_zero_and_one() {
    use crate::group::*;
    let g = g1_gen();
    assert_eq!(g1_scalar_mul(&[0u8; 4], &g), G1Aff::Inf);
    assert_eq!(g1_scalar_mul(&[1u8], &g), g);
    assert_eq!(g1_scalar_mul(&[2u8], &g), g1_double(&g));
}

// =====================================================================
// Rocq-EMITTED Algorithm 9 (`g1_double_a0_extracted.rs`) against the
// hand-written `group::g1_proj_double`
//
// Both are transcriptions of `PointDoubleA0.rcb_double_a0_gallina`;
// the emitted one mechanically, through `rs_body_extract`, the other
// by hand.  Disagreement on any input means one of the two is wrong,
// so these compare the full projective TRIPLE, not the affine image.
// =====================================================================

/// Deterministic Fp element: `x^k` for a fixed generator-coordinate
/// `x`, which stays inside the Montgomery domain by construction.
fn fp_pow_small(base: &tower::Fp, k: u32) -> tower::Fp {
    use tower::{bw6_761_mul, Fp};
    let mut acc = Fp::zero();
    crate::tower::bw6_761_one(&mut acc);
    for _ in 0..k {
        let mut t = Fp::zero();
        bw6_761_mul(&mut t, &acc, base);
        acc = t;
    }
    acc
}

/// Scale a projective representative by `lambda`, giving a DIFFERENT
/// triple for the same projective point (in particular `Z != 1`).
fn scale_proj(p: &crate::group::G1Proj, lambda: &tower::Fp) -> crate::group::G1Proj {
    use crate::group::G1Proj;
    use tower::{bw6_761_mul, Fp};
    let mut x = Fp::zero();
    let mut y = Fp::zero();
    let mut z = Fp::zero();
    bw6_761_mul(&mut x, &p.x, lambda);
    bw6_761_mul(&mut y, &p.y, lambda);
    bw6_761_mul(&mut z, &p.z, lambda);
    G1Proj { x, y, z }
}

/// The differential test: emitted body vs hand-written body, as
/// projective triples, on the identity, the generator, 2G, a spread
/// of on-curve points, and non-normalised (`Z != 1`) representatives.
#[test]
fn g1_alg9_extracted_matches_handwritten() {
    use crate::g1_double_a0_extracted::g1_proj_double_extracted;
    use crate::group::*;
    let b3 = g1_three_b();
    let g = g1_gen();
    let gp = g1_to_proj(&g);

    // (1) the identity (0 : 1 : 0)
    let inf = g1_proj_inf();
    assert_eq!(g1_proj_double_extracted(&inf), g1_proj_double_handwritten(&inf, &b3),
               "extracted != hand-written at the identity");

    // (2) the generator, Z = 1
    assert_eq!(g1_proj_double_extracted(&gp), g1_proj_double_handwritten(&gp, &b3),
               "extracted != hand-written at G");

    // (3) 2G, and (4) a run of further on-curve points 2^k·G, whose
    //     Z is not 1 from k = 1 on.
    let mut p = gp;
    for k in 0..24 {
        let want = g1_proj_double_handwritten(&p, &b3);
        let got = g1_proj_double_extracted(&p);
        assert_eq!(got, want, "extracted != hand-written at 2^{k}·G");
        p = want;
    }

    // (5) a spread of on-curve points k·G for pseudo-random k.
    let scalars: [&[u8]; 6] = [
        &[0xde, 0xad, 0xbe, 0xef],
        &[0x00, 0x00, 0x12, 0x34, 0x56, 0x78],
        &[0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff],
        &[0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef,
          0xfe, 0xdc, 0xba, 0x98, 0x76, 0x54, 0x32, 0x10],
        &[0xa5, 0x5a, 0x3c, 0xc3, 0x0f, 0xf0, 0x69, 0x96,
          0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88,
          0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff, 0x01],
        &[0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6,
          0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c],
    ];
    for s in scalars {
        let q = g1_to_proj(&g1_scalar_mul(s, &g));
        assert_eq!(g1_proj_double_extracted(&q), g1_proj_double_handwritten(&q, &b3),
                   "extracted != hand-written at {s:02x?}·G");
        // (6) the same point, non-normalised: (λX : λY : λZ), Z != 1.
        for e in [2u32, 3, 7, 11] {
            let lambda = fp_pow_small(&tower::Fp(G1_GEN_X), e);
            let qs = scale_proj(&q, &lambda);
            assert_eq!(g1_proj_double_extracted(&qs),
                       g1_proj_double_handwritten(&qs, &b3),
                       "extracted != hand-written at λ^{e}·({s:02x?}·G)");
        }
    }
}

/// The emitted body also has to agree with Algorithm 7 applied to a
/// repeated argument — the Rust image of `rcb_double_a0_eq_ladderstep`
/// — on on-curve inputs, coordinate for coordinate.
#[test]
fn g1_alg9_extracted_equals_alg7_self_add() {
    use crate::g1_double_a0_extracted::g1_proj_double_extracted;
    use crate::group::*;
    let b3 = g1_three_b();
    let mut p = g1_to_proj(&g1_gen());
    for k in 0..16 {
        let by_double = g1_proj_double_extracted(&p);
        assert_eq!(by_double, g1_proj_add(&p, &p, &b3),
                   "extracted Alg 9 != Alg 7(P,P) at k={k}");
        p = by_double;
    }
}

/// And it has to agree with the affine reference through
/// `g1_from_proj`, which is an independent check of the value (the
/// two tests above only pin it to other RCB code).
#[test]
fn g1_alg9_extracted_matches_affine() {
    use crate::g1_double_a0_extracted::g1_proj_double_extracted;
    use crate::group::*;
    let mut aff = g1_gen();
    let mut proj = g1_to_proj(&aff);
    for k in 0..16 {
        aff = g1_double(&aff);
        proj = g1_proj_double_extracted(&proj);
        assert_eq!(g1_from_proj(&proj), aff,
                   "extracted doubling mismatch at k={k}");
    }
}
