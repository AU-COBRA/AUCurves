//! zkgroup primitives demo — trait-shaped wrapper around the
//! hax-extractable `zkgroup-hax` crate (in
//! `SSProve-lean/zkgroup-hax/`).
//!
//! This file used to be a direct `curve25519-dalek::ristretto::*`
//! consumer (a PoC for Pedersen + Schnorr over Ristretto255).  We
//! have since migrated to a trait surface so that:
//!
//! - The production tree carries **no `curve25519_dalek` imports**
//!   on the zkgroup path.  This keeps the dalek dep test-only on the
//!   zkgroup track, mirroring what the `wnaf_comb_leaves` /
//!   `tfp25519_limbs` features did for the Ed25519 track.
//! - Trait-instance wiring lives in `tests/zkgroup_with_aucurves.rs`,
//!   which is the canonical pattern for every other Signal protocol
//!   in this crate (`double_ratchet_with_aucurves.rs`,
//!   `pqxdh_with_aucurves.rs`, `sender_keys_with_aucurves.rs`,
//!   `x3dh_with_aucurves.rs`, `spqr_with_aucurves.rs`).
//! - Cross-library KATs against the hax-extractable reference
//!   formalisation (`SSProve-lean/zkgroup-hax`) live in the same
//!   integration-test file.  The reference formalisation itself can
//!   be cross-checked against `libsignal-zkgroup` upstream via its
//!   `--features upstream-signal` gate, which we do not enable here.
//!
//! ## What this module provides
//!
//! 1. A `ZkgroupCrypto` trait with the eight ristretto-255 primitive
//!    operations the demo's Pedersen-commit-and-prove flow needs.
//!    The shape mirrors `zkgroup_hax::RistrettoGroup` (same byte
//!    typing, same operation set), so an `impl ZkgroupCrypto` and an
//!    `impl RistrettoGroup` on the same backing struct can share
//!    bodies line-for-line.
//!
//! 2. Generic free functions `commit`, `prove_knowledge`,
//!    `verify_proof` parameterised by a `ZkgroupCrypto` instance.
//!    These keep the original PoC's public surface (Pedersen commit
//!    over `(value·G + blinding·H)`, Schnorr proof of knowledge, and
//!    SHA-256-Fiat-Shamir verification) but route every group
//!    operation through the trait.  The cryptographic content is
//!    unchanged.
//!
//! ## Trust footprint
//!
//! At the source level, this module touches no concrete arithmetic —
//! it is parametric in `ZkgroupCrypto`.  The trust transfer is
//! therefore wherever the instance comes from:
//!
//! - In `tests/zkgroup_with_aucurves.rs`, the instance delegates to
//!   `zkgroup-hax`'s free functions (which themselves require a
//!   `RistrettoGroup` impl).  For now both are backed by
//!   curve25519-dalek; the dalek dep lives in `[dev-dependencies]`
//!   only.
//! - The medium-term plan (`AUCurves/docs/signal-stack-status-2026-05-13.md`
//!   §6.2 sessions 3-8) routes the trait through the verified
//!   `Ristretto255` extraction (`SSProve-lean/CatCrypt/Crypto/
//!   Ristretto255/Extraction/Ristretto255_haxpipe.lean`) plus the
//!   Rocq `pedersen_commit_strong_correct` Qed
//!   (`AUCurves/src/Bedrock/End2End/Pedersen/Strong_Correctness.v`).
//!
//! The byte-level layout (`Scalar = [u8; 32]`, `RistrettoPoint =
//! [u8; 32]` for the compressed encoding) matches both
//! `zkgroup-hax::types` and the libsignal-zkgroup wire format, so a
//! later swap of the backing instance is a no-op at the trait
//! boundary.

use crate::symmetric::sha256;

/// A 32-byte little-endian scalar in `ℤ_ℓ` (the Ristretto-255
/// subgroup order).
pub type Scalar = [u8; 32];

/// A 32-byte compressed Ristretto-255 group element.
pub type RistrettoPoint = [u8; 32];

/// A Pedersen commitment is a single ristretto point.
///
/// `Commitment(C) = value·G + blinding·H` where `G` is the canonical
/// basepoint and `H` a second generator with unknown relative
/// discrete log.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Commitment(pub RistrettoPoint);

/// A Schnorr proof of knowledge of `(value, blinding)` for a
/// Pedersen commitment `Commitment(value·G + blinding·H)`.
///
/// Sigma-protocol form: `(R, s_v, s_r)` where `R = r_v·G + r_b·H`,
/// `s_v = r_v + c·value`, `s_r = r_b + c·blinding`, with challenge
/// `c = H(C ‖ R)`.  Stored as 32-byte byte strings to match the
/// `ZkgroupCrypto` byte typing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SchnorrProof {
    pub r: RistrettoPoint,
    pub s_v: Scalar,
    pub s_r: Scalar,
}

/// Group-and-scalar operations sufficient for the demo's Pedersen +
/// Schnorr flow.
///
/// Shape mirrors `zkgroup_hax::RistrettoGroup` from the
/// SSProve-lean/zkgroup-hax crate.  An instance that wires this
/// trait through `zkgroup-hax`'s free functions can be implemented
/// line-for-line on the same backing struct; see the
/// `AucurvesZkgroup` impl in `tests/zkgroup_with_aucurves.rs` for
/// the canonical wiring.
///
/// All inputs are 32-byte byte strings (little-endian scalars,
/// compressed-ristretto points), so the trait is hax-extractable
/// shape-wise.  Reductions modulo `ℓ` and modulo the ristretto
/// subgroup are the responsibility of the implementor.
///
/// Reduction modulo the scalar field follows
/// `Scalar::from_bytes_mod_order` semantics (truncate, then reduce);
/// implementations targeting wide-uniform sampling should mod-reduce
/// the wide bytes externally before calling into the trait.
pub trait ZkgroupCrypto: Copy {
    /// The canonical Ristretto-255 basepoint `G`.
    fn basepoint() -> RistrettoPoint;

    /// A second generator `H` with unknown relative discrete log
    /// w.r.t. `G`.  Required for Pedersen hiding.
    fn basepoint_h() -> RistrettoPoint;

    /// Scalar multiplication: `k·P`, point compressed on output.
    fn point_mul(k: &Scalar, p: &RistrettoPoint) -> RistrettoPoint;

    /// Point addition: `P + Q`, both compressed on input and output.
    fn point_add(p: &RistrettoPoint, q: &RistrettoPoint) -> RistrettoPoint;

    /// Scalar addition modulo `ℓ`.
    fn scalar_add(a: &Scalar, b: &Scalar) -> Scalar;

    /// Scalar multiplication modulo `ℓ`.
    fn scalar_mul(a: &Scalar, b: &Scalar) -> Scalar;

    /// Reduce 64 wide bytes to a canonical 32-byte scalar mod `ℓ`.
    ///
    /// Used by the Fiat-Shamir step to turn a SHA-256 output plus
    /// 32 zero bytes into a uniformly-distributed challenge.  Wider
    /// hash chains (SHA-512) feed directly.
    fn scalar_from_wide(wide: &[u8; 64]) -> Scalar;

    /// Byte-equality of two compressed ristretto points.  Because
    /// ristretto encodings are canonical, this is group equality.
    fn point_eq(p: &RistrettoPoint, q: &RistrettoPoint) -> bool;
}

/// Pedersen commit: `C = value·G + blinding·H`.
///
/// Parametric in `Z: ZkgroupCrypto`.  The instance supplies the
/// concrete ristretto arithmetic; this function is pure dispatch.
pub fn commit<Z: ZkgroupCrypto>(value: &Scalar, blinding: &Scalar) -> Commitment {
    let g = Z::basepoint();
    let h = Z::basepoint_h();
    let vg = Z::point_mul(value, &g);
    let bh = Z::point_mul(blinding, &h);
    Commitment(Z::point_add(&vg, &bh))
}

/// Build a Fiat-Shamir challenge `c = H(C ‖ R) mod ℓ`.
///
/// Internal helper, shared by prover and verifier.
fn challenge<Z: ZkgroupCrypto>(c: &RistrettoPoint, r: &RistrettoPoint) -> Scalar {
    let mut buf = [0u8; 64];
    buf[..32].copy_from_slice(&sha256(&{
        let mut chal_in = [0u8; 64];
        chal_in[..32].copy_from_slice(c);
        chal_in[32..].copy_from_slice(r);
        chal_in
    }));
    // Top 32 bytes left at zero — `scalar_from_wide` does the
    // reduction.  The 32-byte SHA-256 image gives 256-bit Fiat-Shamir
    // entropy, which is sufficient for the σ-protocol soundness
    // bound (the residual `ℓ - 2^252` slack is statistical-distance
    // bounded by < 2^-127).
    Z::scalar_from_wide(&buf)
}

/// Derive deterministic Schnorr nonces `(r_v, r_b)` from a 32-byte
/// seed, using two domain-separated SHA-256 calls (mirroring the
/// original PoC).
///
/// Splitting domains via the constants `b"rv-domain"` /
/// `b"rb-domain"` matches the original demo so KATs are stable
/// across the trait migration.
fn derive_nonces<Z: ZkgroupCrypto>(rng_seed: &[u8; 32]) -> (Scalar, Scalar) {
    let mut wide_v = [0u8; 64];
    wide_v[..32].copy_from_slice(rng_seed);
    wide_v[32..].copy_from_slice(&sha256(b"rv-domain"));
    let r_v = Z::scalar_from_wide(&wide_v);

    let mut wide_r = [0u8; 64];
    wide_r[..32].copy_from_slice(rng_seed);
    wide_r[32..].copy_from_slice(&sha256(b"rb-domain"));
    let r_b = Z::scalar_from_wide(&wide_r);
    (r_v, r_b)
}

/// Prove knowledge of `(value, blinding)` inside `commitment`.
///
/// `rng_seed` is used for the σ-protocol nonces; for KAT determinism
/// we derive from a seed rather than calling system RNG.  In a
/// production deployment, callers pass a freshly-sampled 32-byte
/// scalar.
pub fn prove_knowledge<Z: ZkgroupCrypto>(
    value: &Scalar,
    blinding: &Scalar,
    commitment: &Commitment,
    rng_seed: &[u8; 32],
) -> SchnorrProof {
    let g = Z::basepoint();
    let h = Z::basepoint_h();
    let (r_v, r_b) = derive_nonces::<Z>(rng_seed);
    let rv_g = Z::point_mul(&r_v, &g);
    let rb_h = Z::point_mul(&r_b, &h);
    let r_point = Z::point_add(&rv_g, &rb_h);

    let c = challenge::<Z>(&commitment.0, &r_point);
    let cv = Z::scalar_mul(&c, value);
    let cb = Z::scalar_mul(&c, blinding);
    let s_v = Z::scalar_add(&r_v, &cv);
    let s_r = Z::scalar_add(&r_b, &cb);
    SchnorrProof { r: r_point, s_v, s_r }
}

/// Verify a Schnorr proof against a Pedersen commitment.
///
/// Checks `s_v·G + s_r·H == R + c·C`, with `c = H(C ‖ R)`.
pub fn verify_proof<Z: ZkgroupCrypto>(commitment: &Commitment, proof: &SchnorrProof) -> bool {
    let g = Z::basepoint();
    let h = Z::basepoint_h();
    let c = challenge::<Z>(&commitment.0, &proof.r);

    let svg = Z::point_mul(&proof.s_v, &g);
    let srh = Z::point_mul(&proof.s_r, &h);
    let lhs = Z::point_add(&svg, &srh);

    let cc = Z::point_mul(&c, &commitment.0);
    let rhs = Z::point_add(&proof.r, &cc);

    Z::point_eq(&lhs, &rhs)
}

// =========================================================================
// Equality across two commitments: prove `c1` and `c2` share a value.
// =========================================================================
//
// In the zkgroup credential-disclosure primitive, a user has to
// show that two Pedersen commitments hide the same attribute value
// (the user's profile-key field shared between issuer- and
// verifier-facing commitments) without revealing the value.  This
// reduces to a Schnorr proof of knowledge of `(value, b1, b2)` with
// the constraint `c1 = value·G + b1·H` and `c2 = value·G + b2·H`.
//
// Algebraically: `c1 - c2 = (b1 - b2)·H`, so the user proves
// knowledge of `b1 - b2` for the discrete-log of `(c1 - c2)` w.r.t.
// `H`.  We expose this as `prove_equality` / `verify_equality`
// alongside the value-and-blinding variant above.

/// A Schnorr proof that two Pedersen commitments hide the same
/// value: `(R, s_db)` where `R = r·H`, `s_db = r + c·(b1 - b2)`,
/// `c = H((c1 - c2) ‖ R)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EqualityProof {
    pub r: RistrettoPoint,
    pub s_db: Scalar,
}

/// Negate a scalar by computing `0 - a` via `scalar_add(L_minus_a)`.
///
/// Implementations of `ZkgroupCrypto` that surface a `scalar_neg`
/// can override this with a single call; the default uses the
/// algebraic identity `-a = (ℓ - 1)·a + (-a)` viewed mod ℓ via
/// `0 - a`.  Concretely we exploit `scalar_add(a, neg) = 0` to get
/// `neg = scalar_mul(a, scalar_mul_minus_one)`... but the simplest
/// portable way that needs no extra trait method is to compute
/// `(ℓ - 1) - (a - 1) = ℓ - a` by the standard mod arithmetic, but
/// without `scalar_sub` in the trait we instead use
/// `scalar_mul(a, MINUS_ONE_LE)` where `MINUS_ONE_LE` is the
/// 32-byte LE encoding of `ℓ - 1`.
///
/// Note: this constant is the ristretto-255 subgroup order minus 1,
/// canonical LE encoding.  Computed once at build time.
const MINUS_ONE_LE: Scalar = [
    0xec, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58,
    0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
];

/// Scalar negation via multiplication by `ℓ - 1`.
fn scalar_neg<Z: ZkgroupCrypto>(a: &Scalar) -> Scalar {
    Z::scalar_mul(a, &MINUS_ONE_LE)
}

/// Point negation via `(-1)·P`.
fn point_neg<Z: ZkgroupCrypto>(p: &RistrettoPoint) -> RistrettoPoint {
    Z::point_mul(&MINUS_ONE_LE, p)
}

/// Prove that two commitments hide the same value: returns a
/// witness for `dlog_H(c1 - c2) = b1 - b2`.
///
/// `rng_seed` is per call.  Distinct seeds give distinct proofs.
pub fn prove_equality<Z: ZkgroupCrypto>(
    blinding1: &Scalar,
    blinding2: &Scalar,
    c1: &Commitment,
    c2: &Commitment,
    rng_seed: &[u8; 32],
) -> EqualityProof {
    let h = Z::basepoint_h();
    let mut wide = [0u8; 64];
    wide[..32].copy_from_slice(rng_seed);
    wide[32..].copy_from_slice(&sha256(b"eq-rh-domain"));
    let r = Z::scalar_from_wide(&wide);
    let r_point = Z::point_mul(&r, &h);

    // delta = c1 - c2.
    let neg_c2 = point_neg::<Z>(&c2.0);
    let delta = Z::point_add(&c1.0, &neg_c2);

    let c = challenge::<Z>(&delta, &r_point);
    // db = b1 - b2.
    let neg_b2 = scalar_neg::<Z>(blinding2);
    let db = Z::scalar_add(blinding1, &neg_b2);
    let c_db = Z::scalar_mul(&c, &db);
    let s_db = Z::scalar_add(&r, &c_db);
    EqualityProof { r: r_point, s_db }
}

/// Verify a same-value proof for `(c1, c2)`.
pub fn verify_equality<Z: ZkgroupCrypto>(
    c1: &Commitment,
    c2: &Commitment,
    proof: &EqualityProof,
) -> bool {
    let h = Z::basepoint_h();
    let neg_c2 = point_neg::<Z>(&c2.0);
    let delta = Z::point_add(&c1.0, &neg_c2);

    let c = challenge::<Z>(&delta, &proof.r);
    let lhs = Z::point_mul(&proof.s_db, &h);
    let c_delta = Z::point_mul(&c, &delta);
    let rhs = Z::point_add(&proof.r, &c_delta);
    Z::point_eq(&lhs, &rhs)
}
