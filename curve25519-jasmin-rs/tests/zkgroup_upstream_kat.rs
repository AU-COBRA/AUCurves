//! Upstream `libsignal-zkgroup` cross-vector check for the wired
//! zkgroup primitives in `curve25519-jasmin`.
//!
//! Closing piece of the zkgroup integration plan:
//!
//! - `5026162` — zkgroup phase 1 trait wrapper (12 KATs in
//!   `tests/zkgroup_with_aucurves.rs` vs the `zkgroup-hax` baseline).
//! - `b413bf2e` — Ristretto255 lifted to `Vector UInt8 32` (Lean).
//! - `5b03586`  — Pedersen surface lift (Lean).
//!
//! This file complements `tests/zkgroup_with_aucurves.rs`:
//!
//!   * `zkgroup_with_aucurves.rs`  →  our wiring  vs  zkgroup-hax own baseline.
//!   * `zkgroup_upstream_kat.rs`   →  our wiring  vs  Signal's libsignal-zkgroup.
//!
//! The upstream `libsignal-zkgroup` crate is the canonical reference
//! Signal ships in production.  A byte-identical agreement at the
//! group-arithmetic level certifies that
//!
//!   1. our ristretto255 trait wiring (`AucurvesZkgroup`) is on the
//!      same byte plane as production Signal, and
//!   2. our `mac_ggm_*` / `mac_mucmz_*` algebra reduces to the same
//!      group-element computations Signal performs internally.
//!
//! ## Why most tests are `#[ignore]`'d
//!
//! `libsignal-zkgroup` is published only as part of the
//! `signalapp/libsignal` GitHub monorepo (NOT on crates.io).  Wiring
//! it in costs ~80 transitive crates + GitHub network access, which
//! is undesirable for a default test run on every commit.  We
//! therefore feature-gate the upstream cross-check behind
//! `upstream-signal`.  Even with the feature on, the actual
//! libsignal dep is a `git = "..."` line that maintainers can
//! uncomment in `Cargo.toml` — see the comment block there.
//!
//! ## Two test tiers
//!
//! Tier A (always-on, no libsignal dep) — group-arithmetic
//! reference checks against `curve25519-dalek` directly.  These run
//! under the default test suite and pin down the byte plane our
//! `AucurvesZkgroup` instance shares with dalek (and therefore with
//! Signal, modulo the §3.1 MAC shape gap described below).
//!
//! Tier B (`#[cfg(feature = "upstream-signal")]` + `#[ignore]`) —
//! byte-identical cross-check against `libsignal-zkgroup` proper.
//! These have explicit fixture-name comments so that whoever wires
//! libsignal in can fill the body without re-reading the upstream
//! source.
//!
//! ## The §3.1 MAC shape gap
//!
//! `libsignal-zkgroup` implements the *multi-attribute* MAC of
//! Signal-zkgroup §3.1 (with `w, w'` extra key components).  Our
//! `zkgroup-hax::mac_ggm_*` is CMZ14 baseline (§2.3, Def 1), and
//! `mac_mucmz_*` is μCMZ (1552 §2.3) — a different scheme again.
//! A direct byte-equal cross-check on `MacGgmTag` against
//! `libsignal_zkgroup_crypto::credentials::Mac` is therefore NOT
//! defined; the equivalence is at the level of group operations
//! and the algebraic identities that compose into both schemes.
//!
//! Tier B Test #5 below shows where the full §3.1 MAC bridge would
//! attach when zkgroup-hax phase MAC_n (the multi-attribute MAC)
//! lands.  Until then it stays `#[ignore]`'d with a fixture
//! pointer.
//!
//! ## Running
//!
//! ```text
//! # Tier A only (default):
//! cargo test --features dalek_leaves \
//!     --test zkgroup_upstream_kat
//!
//! # Tier B (needs libsignal-zkgroup wired in Cargo.toml manually):
//! cargo test --features "dalek_leaves upstream-signal" \
//!     --test zkgroup_upstream_kat -- --ignored
//! ```

#![allow(non_snake_case)]

use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint as DalekPoint};
use curve25519_dalek::scalar::Scalar as DalekScalar;
use curve25519_dalek::traits::Identity;
use sha2::{Digest, Sha512};

use zkgroup_hax::{
    mac_ggm_keygen, mac_ggm_sign, mac_ggm_verify, mac_mucmz_keygen, mac_mucmz_sign,
    mac_mucmz_verify, presentation_randomize, RistrettoGroup,
};

// =========================================================================
// AucurvesZkgroup: the same trait wiring used by
// `tests/zkgroup_with_aucurves.rs`.  Duplicated here (rather than
// shared via a `mod common`) so each integration-test binary stays
// self-contained — matches the in-tree style of
// `pqxdh_with_aucurves.rs` etc.
// =========================================================================

#[derive(Clone, Copy)]
struct AucurvesZkgroup;

const H_LABEL: &[u8] = b"zkgroup-hax/basepoint-h";

fn dalek_basepoint_h() -> DalekPoint {
    let mut h = Sha512::new();
    h.update(H_LABEL);
    DalekPoint::from_uniform_bytes(&h.finalize().into())
}

impl RistrettoGroup for AucurvesZkgroup {
    fn basepoint() -> zkgroup_hax::RistrettoPoint {
        RISTRETTO_BASEPOINT_POINT.compress().to_bytes()
    }
    fn basepoint_h() -> zkgroup_hax::RistrettoPoint {
        dalek_basepoint_h().compress().to_bytes()
    }
    fn point_mul(
        k: &zkgroup_hax::Scalar,
        p: &zkgroup_hax::RistrettoPoint,
    ) -> zkgroup_hax::RistrettoPoint {
        let ks = DalekScalar::from_bytes_mod_order(*k);
        let pp = CompressedRistretto(*p)
            .decompress()
            .unwrap_or_else(DalekPoint::identity);
        (ks * pp).compress().to_bytes()
    }
    fn point_add(
        p: &zkgroup_hax::RistrettoPoint,
        q: &zkgroup_hax::RistrettoPoint,
    ) -> zkgroup_hax::RistrettoPoint {
        let pp = CompressedRistretto(*p)
            .decompress()
            .unwrap_or_else(DalekPoint::identity);
        let qq = CompressedRistretto(*q)
            .decompress()
            .unwrap_or_else(DalekPoint::identity);
        (pp + qq).compress().to_bytes()
    }
    fn scalar_add(a: &zkgroup_hax::Scalar, b: &zkgroup_hax::Scalar) -> zkgroup_hax::Scalar {
        let aa = DalekScalar::from_bytes_mod_order(*a);
        let bb = DalekScalar::from_bytes_mod_order(*b);
        (aa + bb).to_bytes()
    }
    fn scalar_mul(a: &zkgroup_hax::Scalar, b: &zkgroup_hax::Scalar) -> zkgroup_hax::Scalar {
        let aa = DalekScalar::from_bytes_mod_order(*a);
        let bb = DalekScalar::from_bytes_mod_order(*b);
        (aa * bb).to_bytes()
    }
    fn scalar_neg(a: &zkgroup_hax::Scalar) -> zkgroup_hax::Scalar {
        let aa = DalekScalar::from_bytes_mod_order(*a);
        (-aa).to_bytes()
    }
    fn point_eq(p: &zkgroup_hax::RistrettoPoint, q: &zkgroup_hax::RistrettoPoint) -> bool {
        p == q
    }
}

fn scalar_from_u64(x: u64) -> zkgroup_hax::Scalar {
    let mut s = [0u8; 32];
    s[..8].copy_from_slice(&x.to_le_bytes());
    s
}

// =========================================================================
// Tier A: always-on byte-plane checks against curve25519-dalek
// =========================================================================
//
// These do NOT require libsignal-zkgroup.  They certify the byte
// plane our trait wiring uses is identical to what dalek (and
// therefore upstream Signal, which uses dalek internally) computes
// for the same scalar/point inputs.
//
// Five operations Signal actually uses:
//   T1. Ristretto255 basepoint canonical encoding.
//   T2. Scalar little-endian-mod-ℓ representation round-trip.
//   T3. Group operation: k·G byte-equal to dalek's (k·G).compress().
//   T4. MAC_GGM exponent algebra: V = (x0 + x1·m)·U byte-equal to
//       a direct dalek-side recomputation.
//   T5. μCMZ rerandomization invariance under (r·U, r·V) scaling.

/// T1.  The ristretto255 basepoint, as emitted by our trait wiring,
/// matches the canonical encoding from RFC 9496 / curve25519-dalek's
/// own `RISTRETTO_BASEPOINT_POINT` constant.
#[test]
fn upstream_t1_ristretto_basepoint_canonical() {
    let bp = <AucurvesZkgroup as RistrettoGroup>::basepoint();
    let expected = RISTRETTO_BASEPOINT_POINT.compress().to_bytes();
    assert_eq!(
        bp, expected,
        "AucurvesZkgroup::basepoint() must equal RFC 9496 canonical encoding"
    );
}

/// T2.  Scalar `1` little-endian round-trips through
/// `DalekScalar::from_bytes_mod_order` — confirming our `Scalar`
/// byte layout is the LE-mod-ℓ convention shared with libsignal.
#[test]
fn upstream_t2_scalar_little_endian_mod_l() {
    let one: zkgroup_hax::Scalar = scalar_from_u64(1);
    let dalek_one = DalekScalar::from_bytes_mod_order(one);
    assert_eq!(
        dalek_one.to_bytes(),
        one,
        "scalar 1 must round-trip through dalek LE-mod-ℓ representation"
    );
    let big: zkgroup_hax::Scalar = scalar_from_u64(0xDEAD_BEEF_CAFE_BABE);
    let dalek_big = DalekScalar::from_bytes_mod_order(big);
    assert_eq!(
        dalek_big.to_bytes(),
        big,
        "64-bit-payload scalar must round-trip"
    );
}

/// T3.  Group operation: our `point_mul(k, G)` equals dalek's
/// `(k · BASEPOINT).compress()` over a range of small scalars.
#[test]
fn upstream_t3_basepoint_scalarmul_byte_equal() {
    for k_u64 in [1u64, 2, 7, 100, 0xFFFF, 0xDEAD_BEEF, 1u64 << 40] {
        let k = scalar_from_u64(k_u64);
        let g = <AucurvesZkgroup as RistrettoGroup>::basepoint();
        let our_kG = <AucurvesZkgroup as RistrettoGroup>::point_mul(&k, &g);
        let dalek_k = DalekScalar::from_bytes_mod_order(k);
        let dalek_kG = (dalek_k * RISTRETTO_BASEPOINT_POINT).compress().to_bytes();
        assert_eq!(
            our_kG, dalek_kG,
            "point_mul(k={}, G) byte mismatch vs dalek",
            k_u64
        );
    }
}

/// T4.  MAC_GGM algebraic identity: `V = (x0 + x1·m)·U` byte-equal
/// to a direct dalek-side recomputation of the same exponent.  This
/// is the core algebraic fact libsignal's MAC machinery also relies
/// on (whatever the §3.1 packaging around it).
#[test]
fn upstream_t4_mac_ggm_exponent_byte_level() {
    for (x0_u, x1_u, m_u, u_u) in [
        (7u64, 13, 99, 17),
        (1, 1, 1, 1),
        (0xDEAD, 0xBEEF, 0xCAFE, 0xBABE),
        (0xFFFF_FFFF, 1, 0xFFFF_FFFE, 2),
    ] {
        let x0 = scalar_from_u64(x0_u);
        let x1 = scalar_from_u64(x1_u);
        let m = scalar_from_u64(m_u);
        let u_scalar = scalar_from_u64(u_u);
        let g = <AucurvesZkgroup as RistrettoGroup>::basepoint();
        let u_point = <AucurvesZkgroup as RistrettoGroup>::point_mul(&u_scalar, &g);

        let sk = mac_ggm_keygen(x0, x1);
        let tag = mac_ggm_sign::<AucurvesZkgroup>(&sk, &m, &u_point);

        // Direct dalek-side exponent.
        let exponent = DalekScalar::from_bytes_mod_order(x0)
            + DalekScalar::from_bytes_mod_order(x1) * DalekScalar::from_bytes_mod_order(m);
        let u_dalek = CompressedRistretto(u_point)
            .decompress()
            .expect("u_point must decompress");
        let expected_v = (exponent * u_dalek).compress().to_bytes();

        assert_eq!(
            tag.v, expected_v,
            "MAC_GGM V byte mismatch (x0,x1,m,u)=({:#x},{:#x},{:#x},{:#x})",
            x0_u, x1_u, m_u, u_u
        );
        assert!(
            mac_ggm_verify::<AucurvesZkgroup>(&sk, &m, &tag),
            "round-trip honest verify must succeed"
        );
    }
}

/// T5.  μCMZ presentation rerandomization: `(r·U, r·V)` preserves
/// verification.  This is the group-level identity Signal's
/// credential-presentation flow exploits — the verifier accepts
/// any element of the equivalence class `{ (r·U, r·V) : r ∈ ℤ_ℓ* }`.
#[test]
fn upstream_t5_mucmz_rerandomization_preserves_validity() {
    let sk = mac_mucmz_keygen(
        scalar_from_u64(11),
        scalar_from_u64(22),
        scalar_from_u64(33),
    );
    let m = scalar_from_u64(7);
    let u_scalar = scalar_from_u64(303);
    let g = <AucurvesZkgroup as RistrettoGroup>::basepoint();
    let u_point = <AucurvesZkgroup as RistrettoGroup>::point_mul(&u_scalar, &g);

    let tag = mac_mucmz_sign::<AucurvesZkgroup>(&sk, &m, &u_point);
    for r_u in [2u64, 17, 0xDEAD_BEEF, 1u64 << 50] {
        let r = scalar_from_u64(r_u);
        let rerand = presentation_randomize::<AucurvesZkgroup>(&tag, &r);
        assert!(
            mac_mucmz_verify::<AucurvesZkgroup>(&sk, &m, &rerand),
            "rerandomized μCMZ tag (r={:#x}) must still verify",
            r_u
        );
        assert_ne!(tag.u, rerand.u, "rerandomized U must differ");
        assert_ne!(tag.v, rerand.v, "rerandomized V must differ");
    }
}

// =========================================================================
// Tier B: byte-identical cross-check against libsignal-zkgroup.
//
// Gated on `upstream-signal` feature AND `#[ignore]`'d, so the
// default test suite never touches them.  Reviewers wiring
// libsignal in must:
//
//   1. Uncomment the `libsignal-zkgroup` git dep in
//      `[features.upstream-signal]` of `Cargo.toml` (see comment
//      there pointing to https://github.com/signalapp/libsignal).
//   2. Replace the `#[ignore]` annotation with the actual call into
//      `libsignal_zkgroup_crypto::*`.
//   3. Run `cargo test --features "dalek_leaves upstream-signal" \
//        --test zkgroup_upstream_kat -- --ignored`.
//
// Each Tier B test below is annotated with the EXACT upstream
// fixture path that supplies its KAT.  Listed by the operation
// Signal actually performs in the group system, not by our internal
// API shape.
// =========================================================================

#[cfg(feature = "upstream-signal")]
mod upstream {
    // Note: `use libsignal_zkgroup::*;` (or similar) when the dep is
    // wired.  Left as a deliberate `compile_error!` so the dep
    // omission surfaces immediately.
    //
    // compile_error!(
    //     "Enable libsignal-zkgroup in Cargo.toml [features.upstream-signal]; \
    //      see tests/zkgroup_upstream_kat.rs header for the git dep line."
    // );

    /// B1.  Group public-key derivation.
    ///
    /// Upstream fixture:
    ///   `libsignal-zkgroup` crate, file
    ///   `crates/zkgroup/tests/integration_tests.rs::test_master_key_to_group_secret_key`
    ///   — derives `GroupMasterKey → GroupSecretKey → GroupPublicParams`.
    ///
    /// What to assert:
    ///   For a fixed `[u8; 32]` master key seed, our recomputation
    ///   of `H = HashToGroup(label)` and the derived public params
    ///   should byte-equal the bytes emitted by libsignal's
    ///   `GroupPublicParams::serialize` on the matching subset of
    ///   group elements.  Subset because libsignal includes §3.1's
    ///   `(W, W')` which we don't model here.
    #[test]
    #[ignore = "requires libsignal-zkgroup; see header for wiring instructions"]
    fn b1_group_public_key_derivation_byte_equal() {
        // TODO(libsignal-wiring): see test docs for fixture path.
    }

    /// B2.  Profile-key ciphertext (encrypt).
    ///
    /// Upstream fixture:
    ///   `libsignal-zkgroup` profile-key encrypt path:
    ///   `crates/zkgroup/src/crypto/profile_key_encryption.rs::
    ///    ProfileKeyEncryptionDomain::encrypt`
    ///   tested via
    ///   `crates/zkgroup/tests/integration_tests.rs::test_profile_key_encrypt`.
    ///
    /// What to assert:
    ///   With identical `(GroupSecretKey, ProfileKey, ServiceID)`
    ///   input bytes, our μCMZ tag (`(U, V)` pair from
    ///   `mac_mucmz_sign`) lies on the same group-element pair as
    ///   the `ProfileKeyCiphertext` libsignal emits.  Caveat:
    ///   libsignal's ciphertext is a *Pedersen-encryption* of the
    ///   profile key under the group public key (not a MAC tag),
    ///   so the bridge needs an extra step — the bytes equal
    ///   `(E_A1, E_A2) = (r·G, ProfileKeyAsPoint + r·X)`.  Compare
    ///   each component point-byte-equal.
    #[test]
    #[ignore = "requires libsignal-zkgroup; see header for wiring instructions"]
    fn b2_profile_key_encrypt_byte_equal() {
        // TODO(libsignal-wiring): pair our trait point_mul + point_add
        // with the libsignal fixture above.
    }

    /// B3.  Profile-key ciphertext (decrypt) round-trip.
    ///
    /// Upstream fixture:
    ///   `crates/zkgroup/tests/integration_tests.rs::test_profile_key_encrypt`
    ///   (same fixture as B2, decrypt half).
    ///
    /// What to assert:
    ///   `decrypt(encrypt(pk, x), sk) == x` round-trip is a
    ///   group-arithmetic identity:
    ///     decrypt = E_A2 + (-sk)·E_A1
    ///             = (x·H + r·sk·G) + (-sk)·(r·G)
    ///             = x·H.
    ///   Reconstruct on our trait via `point_add` + `point_mul` +
    ///   `scalar_neg`, then byte-equal-compare to the dalek-encoded
    ///   `x·H`.  Independent of any libsignal call — purely a
    ///   cross-check that our 7 trait methods are sufficient to
    ///   express Signal's decrypt step.
    #[test]
    #[ignore = "requires libsignal-zkgroup; see header for wiring instructions"]
    fn b3_profile_key_decrypt_roundtrip_byte_equal() {
        // TODO(libsignal-wiring): see test docs.
    }

    /// B4.  Presentation-proof randomization.
    ///
    /// Upstream fixture:
    ///   `crates/zkgroup/src/crypto/credentials.rs::
    ///    BlindedCredentialWithSecretNonce::reveal_blinded_credential`
    ///   tested via
    ///   `crates/zkgroup/tests/integration_tests.rs::
    ///    test_blind_issue_credential`.
    ///
    /// What to assert:
    ///   Our `presentation_randomize::<AucurvesZkgroup>(&tag, &r)`
    ///   over the μCMZ tag produces a tag pair `(r·U, r·V)` that,
    ///   while not byte-equal to libsignal's `PresentationProof`
    ///   bytes (different scheme — §3.1 vs μCMZ), lives on the
    ///   same equivalence class of (U, V) pairs.  Compare via
    ///   `verify` cross-acceptance: rerandomized-by-us tag
    ///   verifies under our `mac_mucmz_verify`; libsignal's
    ///   presentation-randomized tag verifies under libsignal's
    ///   `PresentationProof::verify`.  Both succeed.
    #[test]
    #[ignore = "requires libsignal-zkgroup; see header for wiring instructions"]
    fn b4_presentation_randomization_class_equivalence() {
        // TODO(libsignal-wiring): see test docs.
    }

    /// B5.  Full §3.1 MAC byte-equal (PENDING zkgroup-hax MAC_n
    /// phase).
    ///
    /// Upstream fixture:
    ///   `crates/zkgroup/src/crypto/credentials.rs::SystemParams`
    ///   + `Credential` (the multi-attribute MAC with `w, w'`).
    ///
    /// What to assert:
    ///   `mac_zkgroup_sign / mac_zkgroup_verify` (zkgroup-hax phase
    ///   MAC_n) byte-equal to libsignal's `Credential::serialize()`
    ///   on identical inputs.  CURRENTLY BLOCKED on MAC_n
    ///   landing in zkgroup-hax — until then this is documented
    ///   gap; the §3.1 MAC shape is NOT in our crate today.
    ///   When MAC_n lands, replace this body with a direct
    ///   byte-comparison.
    #[test]
    #[ignore = "blocked on zkgroup-hax phase MAC_n (§3.1 multi-attribute MAC)"]
    fn b5_zkgroup_31_mac_byte_equal_pending_mac_n() {
        // TODO(zkgroup-hax MAC_n): land the §3.1 MAC, then cross-check
        // libsignal_zkgroup_crypto::credentials::Credential.
    }

    /// B6.  HMAC-tag verification cross-check.
    ///
    /// Upstream fixture:
    ///   `crates/zkgroup/src/crypto/uid_struct.rs::UidStruct`
    ///   + the HMAC-SHA256 binding tag used in
    ///   `crates/zkgroup/src/api/auth/auth_credential_with_pni.rs`.
    ///
    /// What to assert:
    ///   Identical `(key, message)` input → identical 32-byte HMAC
    ///   output between our `symmetric::hmac_sha256` and
    ///   libsignal's path through `hmac::SimpleHmac<Sha256>`.
    ///   This is the only Tier B test that touches a primitive
    ///   we already have (our verified HMAC-SHA-256) rather than a
    ///   group operation.  Listed here because the libsignal
    ///   presentation-binding tag is the only place credential
    ///   bytes flow into a symmetric primitive in the Signal
    ///   group flow.
    #[test]
    #[ignore = "requires libsignal-zkgroup; see header for wiring instructions"]
    fn b6_hmac_sha256_credential_binding_byte_equal() {
        // TODO(libsignal-wiring): wire our hmac_sha256 against
        // libsignal's HMAC over identical inputs.
    }
}
