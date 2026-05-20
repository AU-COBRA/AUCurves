//! Closes the loop: hax-extracted Signal SPQR (Sparse Post-Quantum
//! Ratchet) running on our Rocq-verified primitive backend.
//!
//! Implements `SpqrCrypto` (from `signal-spqr-hax`) using our
//! verified-extraction primitives:
//!   - KDF (HKDF-SHA256 + HMAC-SHA256): libjade SHA-256 verified
//!     compression function + RFC 5869/2104 composition.
//!   - KEM: simplified 32-byte mock (signal-spqr-hax types are all
//!     [u8; 32] for Kani tractability); real ML-KEM-768 lives in
//!     `tests/cross_lib.rs` in signal-spqr-hax itself.
//!   - AEAD: XOR for the trait-shape demo (signal-spqr-hax's
//!     Ciphertext = [u8; 32]; real AES-GCM lives in our
//!     `symmetric::aes256_gcm_encrypt` for production paths).
//!
//! This test demonstrates that the hax-extracted SPQR ratchet
//! protocol runs end-to-end with our verified primitives at the
//! KDF/HMAC layer.  The KEM stub is a placeholder for the
//! signal-spqr-hax-internal trait shape; production deployment
//! would use ml-kem-768 (already wired in `pqxdh.rs`).

#![allow(non_snake_case)]

use curve25519_jasmin::symmetric::{hmac_sha256, hkdf_sha256};
use signal_spqr_hax::ratchet::{SpqrCrypto, init_alice, init_bob,
                               ratchet_encrypt, ratchet_decrypt,
                               ratchet_step_send, ratchet_step_recv};
use signal_spqr_hax::types::*;

/// SpqrCrypto implementation backed by curve25519-jasmin's verified
/// HMAC/HKDF over libjade SHA-256.
#[derive(Clone, Copy)]
struct AucurvesSpqr;

impl SpqrCrypto for AucurvesSpqr {
    fn kdf_rk(root_key: &SymKey, shared_secret: &KemSs) -> (SymKey, SymKey) {
        // HKDF-SHA256(salt=root_key, ikm=shared_secret, info=...) → 64 bytes
        // split into (new_root, new_chain).
        let mut okm = [0u8; 64];
        hkdf_sha256(Some(root_key), shared_secret, b"SPQR-RK-AUCURVES", &mut okm);
        let mut new_rk = [0u8; 32]; new_rk.copy_from_slice(&okm[..32]);
        let mut new_ck = [0u8; 32]; new_ck.copy_from_slice(&okm[32..]);
        (new_rk, new_ck)
    }

    fn kdf_ck(chain_key: &SymKey) -> (SymKey, SymKey) {
        // HMAC-SHA256 with domain-separated labels.
        let new_ck = hmac_sha256(chain_key, b"SPQR-CK-next");
        let msg_key = hmac_sha256(chain_key, b"SPQR-CK-msg");
        (new_ck, msg_key)
    }

    fn kem_keygen(seed: &SymKey) -> (KemPk, KemSk) {
        // Textbook trait-shape KEM: sk == pk == seed (32 bytes).
        // ct = pk XOR r, ss = SHA(r).  Insecure as KEM but self-
        // consistent: decaps(sk, encaps(pk, r).0).ss == encaps(pk, r).ss.
        // Real ML-KEM-768 wired separately in src/pqxdh.rs.
        (*seed, *seed)
    }

    fn kem_encaps(pk: &KemPk, randomness: &SymKey) -> (KemCt, KemSs) {
        // ct = pk XOR r
        let mut ct = [0u8; 32];
        for i in 0..32 { ct[i] = pk[i] ^ randomness[i]; }
        // ss = SHA-256(r)
        let ss = curve25519_jasmin::symmetric::sha256(randomness);
        (ct, ss)
    }

    fn kem_decaps(sk: &KemSk, ct: &KemCt) -> KemSs {
        // r = ct XOR sk (since sk == pk in this stub)
        let mut r = [0u8; 32];
        for i in 0..32 { r[i] = ct[i] ^ sk[i]; }
        curve25519_jasmin::symmetric::sha256(&r)
    }

    fn encrypt(key: &SymKey, plaintext: &Plaintext) -> Ciphertext {
        // 32-byte trait shape: XOR with key.  Real AES-GCM lives in
        // production paths (`symmetric::aes256_gcm_encrypt`).
        let mut ct = [0u8; 32];
        for i in 0..32 { ct[i] = plaintext[i] ^ key[i]; }
        ct
    }

    fn decrypt(key: &SymKey, ciphertext: &Ciphertext) -> Plaintext {
        let mut pt = [0u8; 32];
        for i in 0..32 { pt[i] = ciphertext[i] ^ key[i]; }
        pt
    }
}

// ============================================================
// End-to-end SPQR ratchet test with our verified-primitive backend
// ============================================================

#[test]
fn spqr_ratchet_with_aucurves_primitives() {
    let initial_root = [0x42u8; 32];
    let alice_seed = [0xA0u8; 32];
    let bob_seed = [0xB0u8; 32];

    // Bob initializes first (his keypair becomes the inbound target).
    let mut bob = init_bob::<AucurvesSpqr>(&initial_root, &bob_seed);
    let bob_pk = bob.kem_pk;

    // Alice initializes with Bob's KEM pubkey.
    let mut alice = init_alice::<AucurvesSpqr>(&initial_root, &alice_seed, &bob_pk);

    // Alice does a send step: KEM encaps against Bob's pk + advance.
    let randomness = [0xC1u8; 32];
    let new_kem_seed = [0xC2u8; 32];
    let ct = ratchet_step_send::<AucurvesSpqr>(&mut alice, &randomness, &new_kem_seed);

    // Bob receives: needs the new public key from Alice as a "header".
    let header = MessageHeader {
        kem_pk: alice.kem_pk,
        epoch: 1,
        msg_index: 0,
    };
    ratchet_step_recv::<AucurvesSpqr>(&mut bob, &header, &ct);

    // Alice encrypts a message.
    let plaintext: Plaintext = [0xCCu8; 32];
    let (msg_header, ciphertext) =
        ratchet_encrypt::<AucurvesSpqr>(&mut alice, &plaintext);

    // Bob decrypts.
    let recovered =
        ratchet_decrypt::<AucurvesSpqr>(&mut bob, &msg_header, &ciphertext);

    assert_eq!(plaintext, recovered,
               "SPQR ratchet roundtrip via verified primitives");
}

#[test]
fn spqr_kdf_rk_is_deterministic_via_aucurves() {
    let rk = [0x01u8; 32];
    let ss = [0x02u8; 32];
    let (rk1, ck1) = AucurvesSpqr::kdf_rk(&rk, &ss);
    let (rk2, ck2) = AucurvesSpqr::kdf_rk(&rk, &ss);
    assert_eq!(rk1, rk2);
    assert_eq!(ck1, ck2);
    assert_ne!(rk1, ck1, "domain separation: rk and ck must differ");
}

#[test]
fn spqr_kdf_ck_advances() {
    let ck = [0x77u8; 32];
    let (next_ck, mk) = AucurvesSpqr::kdf_ck(&ck);
    assert_ne!(ck, next_ck, "kdf_ck advances the chain");
    assert_ne!(ck, mk, "kdf_ck produces a distinct message key");
    assert_ne!(next_ck, mk, "domain separation: ck vs mk");
}
