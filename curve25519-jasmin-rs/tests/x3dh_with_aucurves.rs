//! Closes the X3DH loop: hax-extracted Signal X3DH running on our
//! Rocq-verified primitive backend.
//!
//! Implements `X3dhCrypto` (from `x3dh-hax`) using our verified-extraction
//! primitives, mirroring the `signal-spqr-hax` integration pattern in
//! `tests/spqr_with_aucurves.rs`.
//!
//! Trust set per primitive:
//!   - **DH** (`dh`, `dh_pub`): libjade-Jasmin X25519 (`x25519_jasmin*`).
//!     EasyCrypt-verified jasminc compiler.
//!   - **KDF** (`kdf`): HKDF-SHA-256 (RFC 5869) composition over libjade
//!     Jasmin SHA-256 compression.
//!   - **Sign/Verify**: standard Ed25519 via the `rust_cmd_ed`-extracted
//!     verified bodies (Window4 scalarmult + verified xyzt ops + verified
//!     Scalar25519 mod L).  Matches the libsignal_compat TODO note: same
//!     `[u8;32]` key as both X25519 and Ed25519 secret (deterministic
//!     Ed25519, not XEdDSA randomness).
//!
//! Functional correctness of the DH leaf: x25519 in libjade per
//! formosa-25519's EasyCrypt proofs.  Functional correctness of HKDF:
//! SHA-256 compression Jasmin-verified; HKDF composition is a thin wrapper.
//!
//! **Sign/verify**: full XEdDSA wired.  The trait passes the SAME
//! `[u8; 32]` for both DH and signature operations on the IK; XEdDSA
//! handles this by deriving the Ed25519 verify-key from the X25519 pub
//! via `mont_to_edwards`.  Sign uses `xeddsa_sign_deterministic` (no
//! randomness needed — RFC 8032-style deterministic nonce); verify
//! uses `xeddsa_verify` directly.  Tampering negative test below
//! exercises this path.

#![allow(non_snake_case)]

use curve25519_jasmin::{x25519_jasmin, x25519_jasmin_base};
use curve25519_jasmin::symmetric::{hkdf_sha256_extract, hkdf_sha256_expand};
use curve25519_jasmin::xeddsa::{xeddsa_sign_deterministic, xeddsa_verify};
use x3dh_hax::protocol::{X3dhCrypto, create_bundle, initiate, respond};
use x3dh_hax::types::*;

/// X3dhCrypto implementation backed by our verified curve25519-jasmin
/// primitives.
#[derive(Clone, Copy)]
struct AucurvesX3dh;

impl X3dhCrypto for AucurvesX3dh {
    fn dh(secret: &X3dhKey, peer_pub: &X3dhKey) -> X3dhKey {
        x25519_jasmin(secret, peer_pub)
    }

    fn dh_pub(secret: &X3dhKey) -> X3dhKey {
        x25519_jasmin_base(secret)
    }

    fn kdf(dh1: &X3dhKey, dh2: &X3dhKey, dh3: &X3dhKey, dh4: &X3dhKey) -> X3dhSessionKey {
        // Signal X3DH KDF: F || DH1 || DH2 || DH3 || DH4 with F = 0xff × 32.
        // Per libsignal_compat shape: HKDF-SHA256(salt=[0;32], ikm=F||DH1..4,
        // info=b"WhisperText") → 32 bytes.
        let mut ikm = [0u8; 32 + 4 * 32];
        ikm[..32].fill(0xff);
        ikm[32..64].copy_from_slice(dh1);
        ikm[64..96].copy_from_slice(dh2);
        ikm[96..128].copy_from_slice(dh3);
        ikm[128..160].copy_from_slice(dh4);
        let prk = hkdf_sha256_extract(Some(&[0u8; 32]), &ikm);
        let mut sk = [0u8; 32];
        hkdf_sha256_expand(&prk, b"WhisperText", &mut sk);
        sk
    }

    fn sign(ik_secret: &X3dhKey, msg: &X3dhKey) -> X3dhSignature {
        // Deterministic XEdDSA — no randomness needed (the trait
        // doesn't provide any).  Signs against the Edwards verify-key
        // derived by xeddsa_verify from the X25519 pub `dh_pub(ik_secret)`,
        // so verify() below succeeds for honest inputs.
        xeddsa_sign_deterministic(ik_secret, msg)
    }

    fn verify(ik_pub: &X3dhKey, msg: &X3dhKey, sig: &X3dhSignature) -> bool {
        // Full XEdDSA verify: Mont→Edwards derives the verify-key from
        // the X25519 pub, then runs the verified Ed25519 verify body.
        xeddsa_verify(ik_pub, msg, sig)
    }
}

/// Smoke test: full X3DH session establishment using our verified primitives.
/// Alice initiates, Bob responds; both must derive the same session key.
#[test]
fn x3dh_alice_bob_session_match() {
    // Deterministic seeds for reproducibility.
    let ik_a = [0xA1u8; 32];
    let ek_a = [0xA2u8; 32];
    let ik_b = [0xB1u8; 32];
    let spk_b = [0xB2u8; 32];
    let opk_b = [0xB3u8; 32];

    // Bob publishes a pre-key bundle (signs SPK with IK).
    let bundle_b = create_bundle::<AucurvesX3dh>(&ik_b, &spk_b, &opk_b);

    // Alice runs initiate.
    let (session_a, init_msg, sig_valid_a) = initiate::<AucurvesX3dh>(
        &ik_a, &ek_a, &bundle_b, true,
    );
    assert!(sig_valid_a, "alice's SPK signature check must succeed");

    // Bob responds.
    let session_b = respond::<AucurvesX3dh>(
        &ik_b, &spk_b, &opk_b, &init_msg, true,
    );

    assert_eq!(session_a, session_b,
        "X3DH session-key divergence between Alice and Bob");
}

/// Negative test: tamper with the SPK signature → sig_valid = false.
#[test]
fn x3dh_alice_rejects_tampered_spk_sig() {
    let ik_a = [0xA1u8; 32];
    let ek_a = [0xA2u8; 32];
    let ik_b = [0xB1u8; 32];
    let spk_b = [0xB2u8; 32];
    let opk_b = [0xB3u8; 32];

    let mut bundle_b = create_bundle::<AucurvesX3dh>(&ik_b, &spk_b, &opk_b);
    bundle_b.sig[0] ^= 0x01;

    let (_sk, _msg, sig_valid) = initiate::<AucurvesX3dh>(&ik_a, &ek_a, &bundle_b, true);
    assert!(!sig_valid,
        "tampered SPK signature must report sig_valid = false");
}

/// Smoke test: dh_pub is consistent — verifying the trait method
/// matches our standalone wrapper.
#[test]
fn x3dh_dh_pub_consistent() {
    let secret = [0x42u8; 32];
    let via_trait = <AucurvesX3dh as X3dhCrypto>::dh_pub(&secret);
    let direct = x25519_jasmin_base(&secret);
    assert_eq!(via_trait, direct);
}
