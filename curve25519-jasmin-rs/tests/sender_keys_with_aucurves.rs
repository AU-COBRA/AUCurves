//! Closes the Sender Keys loop: hax-extracted Signal SenderKeys running
//! on our Rocq-verified primitive backend.
//!
//! Mirrors `tests/x3dh_with_aucurves.rs` + AEAD + HMAC-based KDF chain.
//!
//! Trust set per primitive:
//!   - kdf_msg, kdf_chain: HMAC-SHA-256 over libjade-Jasmin SHA-256.
//!   - aead_encrypt, aead_decrypt: AES-256-CBC + HMAC-SHA-256 (Signal-spec).
//!     Wire = IV(16) || ciphertext_PKCS7 || HMAC-SHA-256(32).
//!     AES block: libcrux-lean-specs pure-Rust FIPS-197 (no AES-NI;
//!     byte-identical to libcrux HACL via FIPS-197 spec).
//!     CBC + PKCS7 + HMAC: safe Rust over libjade SHA-256.
//!   - sign: XEdDSA deterministic via verified Window4 scalarmult + Scalar25519.
//!   - verify: XEdDSA verify via mont_to_edwards + verified Ed25519 verify.
//!   - verifying_key_from: derives X25519 pub (the "verify-key" is then
//!     the same X25519 pub which xeddsa_verify converts on each call).

#![allow(non_snake_case)]

use curve25519_jasmin::x25519_jasmin_base;
use curve25519_jasmin::symmetric::{
    hmac_sha256,
    aes256_cbc_hmac_encrypt_nonce, aes256_cbc_hmac_decrypt_nonce,
};
use curve25519_jasmin::xeddsa::{xeddsa_sign_deterministic, xeddsa_verify};
use sender_keys_hax::protocol::{SenderKeysCrypto, init_sender, init_receiver, send, receive};
use sender_keys_hax::types::*;

#[derive(Clone, Copy)]
struct AucurvesSenderKeys;

impl SenderKeysCrypto for AucurvesSenderKeys {
    fn kdf_msg(chain: &ChainKey) -> MessageKey {
        hmac_sha256(chain, &[0x01u8])
    }

    fn kdf_chain(chain: &ChainKey) -> ChainKey {
        hmac_sha256(chain, &[0x02u8])
    }

    fn aead_encrypt(key: &MessageKey, nonce: &Nonce, aad: &[u8], pt: &[u8]) -> Vec<u8> {
        aes256_cbc_hmac_encrypt_nonce(key, nonce, aad, pt)
            .expect("aes256_cbc_hmac_encrypt_nonce is infallible for valid key/nonce")
    }

    fn aead_decrypt(key: &MessageKey, nonce: &Nonce, aad: &[u8], ct: &[u8]) -> Option<Vec<u8>> {
        aes256_cbc_hmac_decrypt_nonce(key, nonce, aad, ct).ok()
    }

    fn sign(sk: &SigningKey, msg: &[u8]) -> Signature {
        xeddsa_sign_deterministic(sk, msg)
    }

    fn verify(vk: &VerifyingKey, msg: &[u8], sig: &Signature) -> bool {
        xeddsa_verify(vk, msg, sig)
    }

    fn verifying_key_from(sk: &SigningKey) -> VerifyingKey {
        x25519_jasmin_base(sk)
    }
}

#[test]
fn sender_keys_alice_bob_roundtrip() {
    let sender_id = [0x12u8; 32];
    let initial_ck = [0xC0u8; 32];
    let signing_key = [0x5Au8; 32];

    let mut alice = init_sender::<AucurvesSenderKeys>(sender_id, initial_ck, signing_key);
    let vk = <AucurvesSenderKeys as SenderKeysCrypto>::verifying_key_from(&signing_key);
    let mut bob = init_receiver(sender_id, initial_ck, vk);

    let plaintext = b"hello group";
    let aad = b"group-id-42";

    let msg = send::<AucurvesSenderKeys>(&mut alice, plaintext, aad);
    let received = receive::<AucurvesSenderKeys>(&mut bob, &msg)
        .expect("receive must succeed on honest message");
    assert_eq!(received, plaintext);
}

#[test]
fn sender_keys_chain_advances() {
    let sender_id = [0x12u8; 32];
    let initial_ck = [0xC0u8; 32];
    let signing_key = [0x5Au8; 32];

    let mut alice = init_sender::<AucurvesSenderKeys>(sender_id, initial_ck, signing_key);
    let vk = <AucurvesSenderKeys as SenderKeysCrypto>::verifying_key_from(&signing_key);
    let mut bob = init_receiver(sender_id, initial_ck, vk);

    let aad = b"group";
    for i in 0..5u8 {
        let pt = [0x10 + i; 64];
        let msg = send::<AucurvesSenderKeys>(&mut alice, &pt, aad);
        let got = receive::<AucurvesSenderKeys>(&mut bob, &msg)
            .expect("receive must succeed");
        assert_eq!(got, pt, "iteration {i}");
        assert_eq!(msg.msg_num, i as u32);
    }
}

#[test]
fn sender_keys_rejects_tampered_signature() {
    let sender_id = [0x12u8; 32];
    let initial_ck = [0xC0u8; 32];
    let signing_key = [0x5Au8; 32];

    let mut alice = init_sender::<AucurvesSenderKeys>(sender_id, initial_ck, signing_key);
    let vk = <AucurvesSenderKeys as SenderKeysCrypto>::verifying_key_from(&signing_key);
    let mut bob = init_receiver(sender_id, initial_ck, vk);

    let mut msg = send::<AucurvesSenderKeys>(&mut alice, b"hi", b"aad");
    msg.signature[0] ^= 0x01;

    assert!(
        receive::<AucurvesSenderKeys>(&mut bob, &msg).is_none(),
        "tampered signature must cause receive to fail"
    );
}
