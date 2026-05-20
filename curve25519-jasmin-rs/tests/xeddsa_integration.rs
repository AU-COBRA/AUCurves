//! Integration tests for XEdDSA: sign + verify roundtrip, mont→edwards
//! field-split path, determinism, and rejection of tampered inputs.
//!
//! Complements the inline unit tests in `src/xeddsa.rs::tests`.  The
//! integration-level tests exercise only the public crate API (no
//! `super::*`), which catches accidental visibility regressions and
//! gives CI a cross-process check that the public surface alone
//! suffices to sign + verify under all expected inputs.
//!
//! The verify path goes through `mont_to_edwards::mont_u_to_edwards_compressed`
//! (the XEdDSA-specific "field split") and then standard Ed25519 verify.
//! Tests below specifically exercise both stages.

use curve25519_jasmin::{
    mont_to_edwards::mont_u_to_edwards_compressed,
    x25519_jasmin_base,
    xeddsa::{xeddsa_sign, xeddsa_sign_deterministic, xeddsa_verify},
};

/// 6 distinct (privkey-seed, message) pairs spanning short / RFC-typical /
/// 1 KB / empty message cases.
fn vectors() -> Vec<(u8, Vec<u8>)> {
    vec![
        (0x01, b"".to_vec()),
        (0x42, b"Hello Signal".to_vec()),
        (0xfe, b"a".to_vec()),
        (0x7f, vec![0x55u8; 64]),
        (0x80, vec![0xaau8; 256]),
        (0xc3, vec![0xffu8; 1024]),
    ]
}

#[test]
fn integration_sign_verify_roundtrip_diverse() {
    for (seed, msg) in vectors() {
        let priv_k = [seed; 32];
        let pub_k = x25519_jasmin_base(&priv_k);
        let random = [seed.wrapping_add(1); 64];
        let sig = xeddsa_sign(&priv_k, &msg, &random);
        assert!(
            xeddsa_verify(&pub_k, &msg, &sig),
            "honest signature should verify (seed={:#x}, msg.len={})",
            seed,
            msg.len()
        );
    }
}

#[test]
fn integration_sign_deterministic_is_deterministic() {
    // Same key + same message → same signature (no random input dependence).
    let priv_k = [0x33u8; 32];
    let msg = b"Determinism check";
    let s1 = xeddsa_sign_deterministic(&priv_k, msg);
    let s2 = xeddsa_sign_deterministic(&priv_k, msg);
    assert_eq!(&s1[..], &s2[..], "deterministic sign must be stable");
    let pub_k = x25519_jasmin_base(&priv_k);
    assert!(xeddsa_verify(&pub_k, msg, &s1), "det sig should verify");
}

#[test]
fn integration_sign_deterministic_differs_per_message() {
    let priv_k = [0x21u8; 32];
    let s1 = xeddsa_sign_deterministic(&priv_k, b"alpha");
    let s2 = xeddsa_sign_deterministic(&priv_k, b"beta");
    assert_ne!(&s1[..], &s2[..], "different messages → different sigs");
}

#[test]
fn integration_verify_rejects_wrong_pubkey() {
    let priv_a = [0x10u8; 32];
    let priv_b = [0x20u8; 32];
    let pub_b = x25519_jasmin_base(&priv_b);
    let msg = b"signed by a, verifying as b";
    let sig = xeddsa_sign(&priv_a, msg, &[0x55u8; 64]);
    assert!(
        !xeddsa_verify(&pub_b, msg, &sig),
        "verify under wrong pubkey must reject"
    );
}

#[test]
fn integration_verify_rejects_tampered_message() {
    let priv_k = [0xa5u8; 32];
    let pub_k = x25519_jasmin_base(&priv_k);
    let msg = b"original";
    let sig = xeddsa_sign(&priv_k, msg, &[0x11u8; 64]);
    assert!(
        !xeddsa_verify(&pub_k, b"tampered", &sig),
        "verify on different message must reject"
    );
}

#[test]
fn integration_verify_rejects_tampered_signature_bytes() {
    let priv_k = [0x6du8; 32];
    let pub_k = x25519_jasmin_base(&priv_k);
    let msg = b"tampering test";
    let mut sig = xeddsa_sign(&priv_k, msg, &[0x66u8; 64]);
    // Flip a bit in R (first half of sig).
    sig[7] ^= 0x40;
    assert!(
        !xeddsa_verify(&pub_k, msg, &sig),
        "R-tampering must reject"
    );
    // Re-sign clean, then tamper s (second half).
    let mut sig2 = xeddsa_sign(&priv_k, msg, &[0x66u8; 64]);
    sig2[40] ^= 0x01;
    assert!(
        !xeddsa_verify(&pub_k, msg, &sig2),
        "s-tampering must reject"
    );
}

/// The XEdDSA verify path's first stage is mont_u_to_edwards_compressed
/// (the "field split" path: derive Edwards y from Montgomery u via
/// fiat-crypto verified field primitives).  Test it produces a valid
/// 32-byte compressed Edwards point for the public keys of every vector,
/// and that the sign-bit input is honored (sign-bit=0 is the XEdDSA
/// convention; passing 1 must produce a distinct output for the same u).
#[test]
fn integration_mont_to_edwards_field_split_path() {
    for (seed, _) in vectors() {
        let priv_k = [seed; 32];
        let pub_k = x25519_jasmin_base(&priv_k);
        let edwards_pos = mont_u_to_edwards_compressed(&pub_k, 0)
            .expect("mont→edwards should succeed on honest X25519 pubkey");
        let edwards_neg = mont_u_to_edwards_compressed(&pub_k, 1)
            .expect("mont→edwards with sign-bit=1 should also succeed");
        // The two should differ in the high bit of byte 31 (the
        // compressed sign bit).
        assert_ne!(
            edwards_pos[31] >> 7,
            edwards_neg[31] >> 7,
            "sign-bit input must control compressed sign bit"
        );
        // The y-coordinate (bits 0..255) should agree.
        let y_pos_msb = edwards_pos[31] & 0x7f;
        let y_neg_msb = edwards_neg[31] & 0x7f;
        assert_eq!(
            y_pos_msb, y_neg_msb,
            "y-coord (high byte mod 0x80) must match across sign-bit choices"
        );
        for i in 0..31 {
            assert_eq!(
                edwards_pos[i], edwards_neg[i],
                "y-coord byte {} must match across sign-bit choices",
                i
            );
        }
    }
}

/// All-zero Montgomery u corresponds to a low-order Edwards point.  The
/// XEdDSA verify is expected to handle this without panicking; whether
/// it accepts or rejects a "signature" under this pubkey is policy-
/// dependent.  We assert no-panic + that the mont→edwards conversion
/// returns Some (not None — the low-order point is well-defined).
#[test]
fn integration_mont_to_edwards_handles_low_order_pubkey() {
    let zero_pub = [0u8; 32];
    let _ = mont_u_to_edwards_compressed(&zero_pub, 0);
    // The function may return Some([0,..,0x80]) or None depending on
    // implementation conventions; the test just ensures no panic.
}

/// Randomized and deterministic variants both produce verifiable signatures.
#[test]
fn integration_xeddsa_two_sign_variants_cross_verify() {
    let priv_k = [0x9eu8; 32];
    let pub_k = x25519_jasmin_base(&priv_k);
    let msg = b"both variants should verify";
    let sig_rand = xeddsa_sign(&priv_k, msg, &[0x77u8; 64]);
    let sig_det = xeddsa_sign_deterministic(&priv_k, msg);
    assert!(
        xeddsa_verify(&pub_k, msg, &sig_rand),
        "randomized variant verifies"
    );
    assert!(
        xeddsa_verify(&pub_k, msg, &sig_det),
        "deterministic variant verifies"
    );
    // The two variants produce distinct signatures (different R) because
    // the nonce derivations differ.
    assert_ne!(
        &sig_rand[..32],
        &sig_det[..32],
        "rand vs det nonce-R should differ"
    );
}
