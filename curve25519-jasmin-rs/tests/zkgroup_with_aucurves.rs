//! Closes the zkgroup loop: hax-extracted `zkgroup-hax` MAC + μCMZ
//! primitives composed with our trait-shaped Pedersen + Schnorr
//! demo, all routed through the same `ZkgroupCrypto` /
//! `RistrettoGroup` instance.
//!
//! Implements both:
//! - `ZkgroupCrypto` (from `curve25519_jasmin::zkgroup_demo`) — the
//!   Pedersen-and-Schnorr trait surface used by the in-tree demo.
//! - `RistrettoGroup` (from `zkgroup_hax::group`) — the hax-extracted
//!   group-operation trait used by the upstream `zkgroup-hax` crate.
//!
//! Both traits share an identical operation set (Ristretto-255 group
//! and scalar arithmetic on byte-typed inputs) so a single backing
//! struct implements them line-for-line.  This file mirrors the
//! pattern used by `double_ratchet_with_aucurves.rs`,
//! `sender_keys_with_aucurves.rs`, `x3dh_with_aucurves.rs`, and
//! `pqxdh_with_aucurves.rs`.
//!
//! ## Trust set
//!
//! Today's wiring backs both traits with `curve25519-dalek`
//! arithmetic, with the dalek dep living in `[dev-dependencies]`
//! only (not the production tree).  Routing through the verified
//! `Ristretto255` path is queued for the later sessions of
//! `AUCurves/docs/signal-stack-status-2026-05-13.md` §6.2 (sessions
//! 3-8: lift `Ristretto255_haxpipe.lean`'s types, wire
//! `Pedersen_haxpipe` into a concrete `PedersenParams` instance,
//! and replace zkgroup-hax's internal MAC scheme wiring with the
//! verified Pedersen + Chaum-Pedersen σ chain).
//!
//! As of this writing, NO verified Lean / Rocq module is reached at
//! runtime — the test exercises the trait wiring and the byte-level
//! agreement between our `zkgroup_demo` Pedersen / Schnorr surface
//! and the `zkgroup-hax` MAC / μCMZ surface, against the same dalek
//! reference.  The Lean / Rocq theorems already exist
//! (`pedersen_uc_secure` Qed, `pedersen_commit_strong_correct` Qed)
//! but their composition into this trait instance is a later
//! session's work.

#![allow(non_snake_case)]

use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint as DalekPoint};
use curve25519_dalek::scalar::Scalar as DalekScalar;
use curve25519_dalek::traits::Identity;
use sha2::{Digest, Sha512};

use curve25519_jasmin::zkgroup_demo::{
    commit, prove_equality, prove_knowledge, verify_equality, verify_proof, Commitment,
    RistrettoPoint, Scalar, ZkgroupCrypto,
};
use zkgroup_hax::{
    issuance_signer_blind, issuance_user_commit, issuance_user_unblind, mac_ggm_keygen,
    mac_ggm_sign, mac_ggm_verify, mac_mucmz_keygen, mac_mucmz_public_params, mac_mucmz_sign,
    mac_mucmz_verify, presentation_randomize, RistrettoGroup,
};

// =========================================================================
// AucurvesZkgroup: shared backing instance for both traits.
// =========================================================================

#[derive(Clone, Copy)]
struct AucurvesZkgroup;

// Domain-separation labels.  `basepoint_h` is shared between the two
// trait impls (the Pedersen `h` for the demo) so that
// `zkgroup_demo::commit::<AucurvesZkgroup>` and
// `mac_mucmz_public_params::<AucurvesZkgroup>` see the same `H`.
const H_LABEL: &[u8] = b"zkgroup-hax/basepoint-h";

fn dalek_basepoint_h() -> DalekPoint {
    let mut h = Sha512::new();
    h.update(H_LABEL);
    DalekPoint::from_uniform_bytes(&h.finalize().into())
}

impl ZkgroupCrypto for AucurvesZkgroup {
    fn basepoint() -> RistrettoPoint {
        RISTRETTO_BASEPOINT_POINT.compress().to_bytes()
    }
    fn basepoint_h() -> RistrettoPoint {
        dalek_basepoint_h().compress().to_bytes()
    }
    fn point_mul(k: &Scalar, p: &RistrettoPoint) -> RistrettoPoint {
        let ks = DalekScalar::from_bytes_mod_order(*k);
        let pp = CompressedRistretto(*p)
            .decompress()
            .unwrap_or_else(DalekPoint::identity);
        (ks * pp).compress().to_bytes()
    }
    fn point_add(p: &RistrettoPoint, q: &RistrettoPoint) -> RistrettoPoint {
        let pp = CompressedRistretto(*p)
            .decompress()
            .unwrap_or_else(DalekPoint::identity);
        let qq = CompressedRistretto(*q)
            .decompress()
            .unwrap_or_else(DalekPoint::identity);
        (pp + qq).compress().to_bytes()
    }
    fn scalar_add(a: &Scalar, b: &Scalar) -> Scalar {
        let aa = DalekScalar::from_bytes_mod_order(*a);
        let bb = DalekScalar::from_bytes_mod_order(*b);
        (aa + bb).to_bytes()
    }
    fn scalar_mul(a: &Scalar, b: &Scalar) -> Scalar {
        let aa = DalekScalar::from_bytes_mod_order(*a);
        let bb = DalekScalar::from_bytes_mod_order(*b);
        (aa * bb).to_bytes()
    }
    fn scalar_from_wide(wide: &[u8; 64]) -> Scalar {
        DalekScalar::from_bytes_mod_order_wide(wide).to_bytes()
    }
    fn point_eq(p: &RistrettoPoint, q: &RistrettoPoint) -> bool {
        p == q
    }
}

// `zkgroup-hax` uses its own type aliases (also `[u8; 32]`), but
// because they live in a foreign crate Rust treats them as distinct
// from `zkgroup_demo`'s.  The impl bodies are identical to the
// `ZkgroupCrypto` impl above — we duplicate purely for type
// matching.
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

// =========================================================================
// Helper: deterministic scalar from a seed (no rand_core dependency in
// the test logic).
// =========================================================================

fn scalar_from_u64(x: u64) -> Scalar {
    let mut s = [0u8; 32];
    s[..8].copy_from_slice(&x.to_le_bytes());
    s
}

// =========================================================================
// KAT 1: Pedersen commit + Schnorr roundtrip — honest proof verifies
// =========================================================================

#[test]
fn zkgroup_pedersen_commit_proof_roundtrip() {
    let value = scalar_from_u64(12345);
    let blinding = scalar_from_u64(67890);
    let c = commit::<AucurvesZkgroup>(&value, &blinding);
    let proof = prove_knowledge::<AucurvesZkgroup>(&value, &blinding, &c, &[0x42u8; 32]);
    assert!(
        verify_proof::<AucurvesZkgroup>(&c, &proof),
        "honest σ-proof must verify"
    );
}

// =========================================================================
// KAT 2: wrong value rejected (σ-protocol soundness)
// =========================================================================

#[test]
fn zkgroup_rejects_wrong_value() {
    let value = scalar_from_u64(12345);
    let blinding = scalar_from_u64(67890);
    let c = commit::<AucurvesZkgroup>(&value, &blinding);
    let wrong = scalar_from_u64(99);
    let proof = prove_knowledge::<AucurvesZkgroup>(&wrong, &blinding, &c, &[0x42u8; 32]);
    assert!(
        !verify_proof::<AucurvesZkgroup>(&c, &proof),
        "proof of wrong value must not verify"
    );
}

// =========================================================================
// KAT 3: wrong blinding rejected
// =========================================================================

#[test]
fn zkgroup_rejects_wrong_blinding() {
    let value = scalar_from_u64(12345);
    let blinding = scalar_from_u64(67890);
    let c = commit::<AucurvesZkgroup>(&value, &blinding);
    let wrong_b = scalar_from_u64(11111);
    let proof = prove_knowledge::<AucurvesZkgroup>(&value, &wrong_b, &c, &[0x42u8; 32]);
    assert!(
        !verify_proof::<AucurvesZkgroup>(&c, &proof),
        "proof of wrong blinding must not verify"
    );
}

// =========================================================================
// KAT 4: distinct commitments for distinct values (Pedersen binding)
// =========================================================================

#[test]
fn zkgroup_different_values_different_commitments() {
    let v1 = scalar_from_u64(1);
    let v2 = scalar_from_u64(2);
    let b = scalar_from_u64(100);
    let c1 = commit::<AucurvesZkgroup>(&v1, &b);
    let c2 = commit::<AucurvesZkgroup>(&v2, &b);
    assert_ne!(
        c1, c2,
        "Pedersen binding: distinct values give distinct commitments"
    );
}

// =========================================================================
// KAT 5: tampered proof rejected (challenge-binding)
// =========================================================================

#[test]
fn zkgroup_tampered_proof_rejected() {
    let value = scalar_from_u64(7);
    let blinding = scalar_from_u64(11);
    let c = commit::<AucurvesZkgroup>(&value, &blinding);
    let mut proof = prove_knowledge::<AucurvesZkgroup>(&value, &blinding, &c, &[0x55u8; 32]);
    // Flip one byte of `s_v`.
    proof.s_v[0] ^= 0x01;
    assert!(
        !verify_proof::<AucurvesZkgroup>(&c, &proof),
        "tampered s_v must not verify"
    );
}

// =========================================================================
// KAT 6: equality-of-commitments proof (same value, different blindings)
// =========================================================================

#[test]
fn zkgroup_equality_proof_accepts_same_value() {
    let value = scalar_from_u64(42);
    let b1 = scalar_from_u64(1001);
    let b2 = scalar_from_u64(2002);
    let c1 = commit::<AucurvesZkgroup>(&value, &b1);
    let c2 = commit::<AucurvesZkgroup>(&value, &b2);
    assert_ne!(
        c1, c2,
        "distinct blindings under same value → distinct commitments"
    );
    let proof = prove_equality::<AucurvesZkgroup>(&b1, &b2, &c1, &c2, &[0xAAu8; 32]);
    assert!(
        verify_equality::<AucurvesZkgroup>(&c1, &c2, &proof),
        "equality proof for shared value must verify"
    );
}

// =========================================================================
// KAT 7: equality-of-commitments proof rejects different values
// =========================================================================
//
// If the prover lies about `(b1, b2)` for commitments hiding *different*
// values, the Schnorr witness it constructs is for a wrong discrete
// log.  Verification must reject.
#[test]
fn zkgroup_equality_proof_rejects_different_values() {
    let v1 = scalar_from_u64(42);
    let v2 = scalar_from_u64(43); // ≠ v1
    let b1 = scalar_from_u64(1001);
    let b2 = scalar_from_u64(2002);
    let c1 = commit::<AucurvesZkgroup>(&v1, &b1);
    let c2 = commit::<AucurvesZkgroup>(&v2, &b2);
    let proof = prove_equality::<AucurvesZkgroup>(&b1, &b2, &c1, &c2, &[0xBBu8; 32]);
    assert!(
        !verify_equality::<AucurvesZkgroup>(&c1, &c2, &proof),
        "equality proof must reject distinct-value commitments"
    );
}

// =========================================================================
// KAT 8: zkgroup-hax MAC_GGM honest verification (cross-trait check)
// =========================================================================

#[test]
fn zkgroup_hax_mac_ggm_verify_accepts_honest_tag() {
    // Deterministic key + message + tag basepoint via the SAME trait
    // instance that drives our Pedersen demo.
    let sk = mac_ggm_keygen(scalar_from_u64(7), scalar_from_u64(13));
    let m = scalar_from_u64(99);
    let u = <AucurvesZkgroup as RistrettoGroup>::point_mul(
        &scalar_from_u64(17),
        &<AucurvesZkgroup as RistrettoGroup>::basepoint(),
    );
    let tag = mac_ggm_sign::<AucurvesZkgroup>(&sk, &m, &u);
    assert!(
        mac_ggm_verify::<AucurvesZkgroup>(&sk, &m, &tag),
        "honest MAC_GGM tag must verify"
    );
}

// =========================================================================
// KAT 9: zkgroup-hax MAC_GGM rejects perturbed tag
// =========================================================================

#[test]
fn zkgroup_hax_mac_ggm_rejects_perturbed_tag() {
    let sk = mac_ggm_keygen(scalar_from_u64(7), scalar_from_u64(13));
    let m = scalar_from_u64(99);
    let u = <AucurvesZkgroup as RistrettoGroup>::point_mul(
        &scalar_from_u64(17),
        &<AucurvesZkgroup as RistrettoGroup>::basepoint(),
    );
    let mut tag = mac_ggm_sign::<AucurvesZkgroup>(&sk, &m, &u);
    tag.v[0] ^= 0x01;
    assert!(
        !mac_ggm_verify::<AucurvesZkgroup>(&sk, &m, &tag),
        "perturbed MAC_GGM tag must not verify"
    );
}

// =========================================================================
// KAT 10: zkgroup-hax μCMZ issuance → unblind → verify roundtrip
// =========================================================================
//
// Exercises the full anonymous-credential issuance flow from
// `zkgroup_hax::issuance_mucmz` under the verified-bridge trait
// instance:
//   (1) user commits to `m` with blinding `s`,
//   (2) signer blinds with fresh `u'`,
//   (3) user unblinds → MAC tag,
//   (4) verifier recomputes V' and accepts.

#[test]
fn zkgroup_hax_mucmz_issuance_roundtrip() {
    let sk = mac_mucmz_keygen(
        scalar_from_u64(11),
        scalar_from_u64(22),
        scalar_from_u64(33),
    );
    let pp = mac_mucmz_public_params::<AucurvesZkgroup>(&sk);
    let m = scalar_from_u64(7);
    let s = scalar_from_u64(101); // user blinding factor
    let u_prime_scalar = scalar_from_u64(202); // signer's fresh exponent

    let user_msg = issuance_user_commit::<AucurvesZkgroup>(&pp, &m, &s);
    let signer_msg =
        issuance_signer_blind::<AucurvesZkgroup>(&sk, &user_msg, &u_prime_scalar);
    let tag = issuance_user_unblind::<AucurvesZkgroup>(&signer_msg, &s);

    assert!(
        mac_mucmz_verify::<AucurvesZkgroup>(&sk, &m, &tag),
        "μCMZ unblinded tag must verify under issuance key"
    );

    // Tamper resilience: a bit-flip in V must not verify.
    let mut tampered = tag;
    tampered.v[0] ^= 0x01;
    assert!(
        !mac_mucmz_verify::<AucurvesZkgroup>(&sk, &m, &tampered),
        "tampered μCMZ tag must not verify"
    );
}

// =========================================================================
// KAT 11: μCMZ presentation randomization preserves validity
// =========================================================================

#[test]
fn zkgroup_hax_mucmz_presentation_randomize_preserves_validity() {
    let sk = mac_mucmz_keygen(
        scalar_from_u64(11),
        scalar_from_u64(22),
        scalar_from_u64(33),
    );
    let m = scalar_from_u64(7);
    let u = <AucurvesZkgroup as RistrettoGroup>::point_mul(
        &scalar_from_u64(303),
        &<AucurvesZkgroup as RistrettoGroup>::basepoint(),
    );
    let tag = mac_mucmz_sign::<AucurvesZkgroup>(&sk, &m, &u);
    let r = scalar_from_u64(404);
    let rerand = presentation_randomize::<AucurvesZkgroup>(&tag, &r);
    assert!(
        mac_mucmz_verify::<AucurvesZkgroup>(&sk, &m, &rerand),
        "rerandomized μCMZ tag must still verify on the same message"
    );
    // Non-trivial: r ≠ 1 produces a fresh byte view.
    assert_ne!(tag.u, rerand.u, "rerandomized U must differ from U");
    assert_ne!(tag.v, rerand.v, "rerandomized V must differ from V");
}

// =========================================================================
// KAT 12: edge case — commit with zero value (identity-aligned)
// =========================================================================

#[test]
fn zkgroup_commit_zero_value_yields_blinding_only() {
    let zero = [0u8; 32];
    let b = scalar_from_u64(77);
    let c = commit::<AucurvesZkgroup>(&zero, &b);
    // Verify the structure: c == b·H since value=0 drops the first term.
    let h = <AucurvesZkgroup as ZkgroupCrypto>::basepoint_h();
    let expected = <AucurvesZkgroup as ZkgroupCrypto>::point_mul(&b, &h);
    assert_eq!(
        c, Commitment(expected),
        "commit(0, b) must equal b·H"
    );
    // σ-proof of (0, b) still verifies.
    let proof = prove_knowledge::<AucurvesZkgroup>(&zero, &b, &c, &[0x10u8; 32]);
    assert!(
        verify_proof::<AucurvesZkgroup>(&c, &proof),
        "σ-proof for (value=0, blinding=b) must verify"
    );
}
