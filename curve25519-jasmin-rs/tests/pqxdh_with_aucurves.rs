//! Closes the PQXDH loop: hax-extracted Signal PQXDH running on our
//! Rocq-verified primitive backend.
//!
//! Mirrors `tests/x3dh_with_aucurves.rs` + ML-KEM-768 via formosa-mlkem.
//!
//! Trust set per primitive:
//!   - DH (`dh`, `dh_pub`): libjade-Jasmin X25519.
//!   - KDF: HKDF-SHA-256 over libjade-Jasmin SHA-256.
//!   - Sign/Verify: XEdDSA (`xeddsa_sign_deterministic` + `xeddsa_verify`).
//!   - KEM (keygen, enc, dec): formosa-mlkem-768 (EasyCrypt-verified jasminc).
//!
//! PQXDH adds one ML-KEM-768 encapsulation on top of the X3DH 4-DH chain,
//! producing an additional `pq_ss` that's mixed into the final HKDF.

#![allow(non_snake_case)]

use curve25519_jasmin::{x25519_jasmin, x25519_jasmin_base};
use curve25519_jasmin::symmetric::{
    hkdf_sha256_extract, hkdf_sha256_expand, sha256,
    mlkem768_keygen, mlkem768_enc, mlkem768_dec,
    MLKEM768_PUBLIC_KEY_BYTES, MLKEM768_SECRET_KEY_BYTES, MLKEM768_CIPHERTEXT_BYTES,
};
use curve25519_jasmin::xeddsa::{xeddsa_sign_deterministic, xeddsa_verify};
use pqxdh_hax::protocol::{PqxdhCrypto, create_bundle, initiate, respond};
use pqxdh_hax::types::*;

/// PqxdhCrypto<1184, 2400, 1088> implementation backed by our verified
/// primitives.  Width parameters match ML-KEM-768.
#[derive(Clone, Copy)]
struct AucurvesPqxdh;

impl PqxdhCrypto<MLKEM768_PUBLIC_KEY_BYTES, MLKEM768_SECRET_KEY_BYTES,
                 MLKEM768_CIPHERTEXT_BYTES> for AucurvesPqxdh {
    fn dh(secret: &PqxdhDhKey, peer_pub: &PqxdhDhKey) -> PqxdhDhKey {
        x25519_jasmin(secret, peer_pub)
    }

    fn dh_pub(secret: &PqxdhDhKey) -> PqxdhDhKey {
        x25519_jasmin_base(secret)
    }

    fn kem_keygen(seed: &PqxdhKemSs) -> ([u8; MLKEM768_PUBLIC_KEY_BYTES],
                                          [u8; MLKEM768_SECRET_KEY_BYTES]) {
        // formosa-mlkem keygen takes 64-byte coins; expand the 32-byte seed
        // via SHA-256 round-trip into a 64-byte coin material.
        let half1 = sha256(seed);
        let mut concat = [0u8; 64];
        concat[..32].copy_from_slice(seed);
        let half2 = sha256(&concat);
        let mut coins = [0u8; 64];
        coins[..32].copy_from_slice(&half1);
        coins[32..].copy_from_slice(&half2);

        let (pk_vec, sk_vec) = mlkem768_keygen(&coins);
        let mut pk_arr = [0u8; MLKEM768_PUBLIC_KEY_BYTES];
        let mut sk_arr = [0u8; MLKEM768_SECRET_KEY_BYTES];
        pk_arr.copy_from_slice(&pk_vec);
        sk_arr.copy_from_slice(&sk_vec);
        (pk_arr, sk_arr)
    }

    fn kem_encaps(pk: &[u8; MLKEM768_PUBLIC_KEY_BYTES], randomness: &PqxdhKemSs)
        -> ([u8; MLKEM768_CIPHERTEXT_BYTES], PqxdhKemSs) {
        let (ct_vec, ss) = mlkem768_enc(pk, randomness);
        let mut ct_arr = [0u8; MLKEM768_CIPHERTEXT_BYTES];
        ct_arr.copy_from_slice(&ct_vec);
        (ct_arr, ss)
    }

    fn kem_decaps(sk: &[u8; MLKEM768_SECRET_KEY_BYTES],
                  ct: &[u8; MLKEM768_CIPHERTEXT_BYTES]) -> PqxdhKemSs {
        mlkem768_dec(sk, ct)
    }

    fn kem_pk_encode(pk: &[u8; MLKEM768_PUBLIC_KEY_BYTES]) -> [u8; 32] {
        // ML-KEM-768 pk is 1184 bytes → hash to 32-byte digest for signing.
        sha256(pk)
    }

    fn kdf(dh1: &PqxdhDhKey, dh2: &PqxdhDhKey, dh3: &PqxdhDhKey, dh4: &PqxdhDhKey,
           kem_ss: &PqxdhKemSs) -> PqxdhSessionKey {
        // PQXDH KDF: HKDF-SHA256(salt=0, ikm = F || DH1..DH4 || pq_ss,
        //                        info="WhisperText").
        let mut ikm = [0u8; 32 + 4 * 32 + 32];
        ikm[..32].fill(0xff);
        ikm[32..64].copy_from_slice(dh1);
        ikm[64..96].copy_from_slice(dh2);
        ikm[96..128].copy_from_slice(dh3);
        ikm[128..160].copy_from_slice(dh4);
        ikm[160..192].copy_from_slice(kem_ss);
        let prk = hkdf_sha256_extract(Some(&[0u8; 32]), &ikm);
        let mut sk = [0u8; 32];
        hkdf_sha256_expand(&prk, b"WhisperText", &mut sk);
        sk
    }

    fn sign(ik_secret: &PqxdhDhKey, msg: &[u8; 32]) -> PqxdhSignature {
        xeddsa_sign_deterministic(ik_secret, msg)
    }

    fn verify(ik_pub: &PqxdhDhKey, msg: &[u8; 32], sig: &PqxdhSignature) -> bool {
        xeddsa_verify(ik_pub, msg, sig)
    }
}

#[test]
fn pqxdh_alice_bob_session_match() {
    let ik_a = [0xA1u8; 32];
    let ek_a = [0xA2u8; 32];
    let ik_b = [0xB1u8; 32];
    let spk_b = [0xB2u8; 32];
    let opk_b = [0xB3u8; 32];
    let pqpk_seed = [0xB4u8; 32];
    let enc_random = [0xC1u8; 32];

    let (bundle_b, pqsk_b) = create_bundle::<AucurvesPqxdh, _, _, _>(
        &ik_b, &spk_b, &opk_b, &pqpk_seed,
    );

    let (session_a, init_msg, spk_valid, pqpk_valid) =
        initiate::<AucurvesPqxdh, _, _, _>(&ik_a, &ek_a, &bundle_b, &enc_random, true);
    assert!(spk_valid, "SPK signature must verify");
    assert!(pqpk_valid, "PQPK signature must verify");

    let session_b = respond::<AucurvesPqxdh, _, _, _>(
        &ik_b, &spk_b, &opk_b, &pqsk_b, &init_msg, true,
    );

    assert_eq!(session_a, session_b,
        "PQXDH session-key divergence between Alice and Bob");
}

#[test]
fn pqxdh_alice_rejects_tampered_spk_sig() {
    let ik_a = [0xA1u8; 32];
    let ek_a = [0xA2u8; 32];
    let ik_b = [0xB1u8; 32];
    let spk_b = [0xB2u8; 32];
    let opk_b = [0xB3u8; 32];
    let pqpk_seed = [0xB4u8; 32];
    let enc_random = [0xC1u8; 32];

    let (mut bundle_b, _pqsk_b) = create_bundle::<AucurvesPqxdh, _, _, _>(
        &ik_b, &spk_b, &opk_b, &pqpk_seed,
    );
    bundle_b.spk_sig[0] ^= 0x01;

    let (_sk, _msg, spk_valid, _pqpk_valid) =
        initiate::<AucurvesPqxdh, _, _, _>(&ik_a, &ek_a, &bundle_b, &enc_random, true);
    assert!(!spk_valid, "tampered SPK signature must report invalid");
}
