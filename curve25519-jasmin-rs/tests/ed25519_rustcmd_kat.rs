//! Known Answer Tests for the Ed25519 sign/verify body extracted
//! from `rust_cmd_ed` (see `src/ed25519_rustcmd/sign.rs`,
//! `verify.rs`).  Vectors are RFC 8032 §7.1.
//!
//! Only built under `--features ed25519_rustcmd`.

#![cfg(feature = "ed25519_rustcmd")]

use curve25519_jasmin::ed25519_rustcmd::{public_key_from_seed, sign, verify};

fn h(s: &str) -> Vec<u8> {
    let s: String = s.chars().filter(|c| !c.is_whitespace()).collect();
    hex::decode(&s).expect("invalid hex")
}

fn h32(s: &str) -> [u8; 32] {
    let v = h(s);
    assert_eq!(v.len(), 32, "hex string must be 32 bytes, got {}", v.len());
    let mut a = [0u8; 32];
    a.copy_from_slice(&v);
    a
}

fn h64(s: &str) -> [u8; 64] {
    let v = h(s);
    assert_eq!(v.len(), 64, "hex string must be 64 bytes, got {}", v.len());
    let mut a = [0u8; 64];
    a.copy_from_slice(&v);
    a
}

// ----------------------------------------------------------------
// RFC 8032 §7.1 — TEST 1 (empty message)
// ----------------------------------------------------------------

const TEST1_SEED: &str =
    "9d61b19deffd5a60ba844af492ec2cc4\
     4449c5697b326919703bac031cae7f60";
const TEST1_PK: &str =
    "d75a980182b10ab7d54bfed3c964073a\
     0ee172f3daa62325af021a68f707511a";
const TEST1_SIG: &str =
    "e5564300c360ac729086e2cc806e828a\
     84877f1eb8e5d974d873e06522490155\
     5fb8821590a33bacc61e39701cf9b46b\
     d25bf5f0595bbe24655141438e7a100b";

// ----------------------------------------------------------------
// RFC 8032 §7.1 — TEST 2 (1-byte 0x72)
// ----------------------------------------------------------------

const TEST2_SEED: &str =
    "4ccd089b28ff96da9db6c346ec114e0f\
     5b8a319f35aba624da8cf6ed4fb8a6fb";
const TEST2_PK: &str =
    "3d4017c3e843895a92b70aa74d1b7ebc\
     9c982ccf2ec4968cc0cd55f12af4660c";
const TEST2_MSG: &str = "72";
const TEST2_SIG: &str =
    "92a009a9f0d4cab8720e820b5f642540\
     a2b27b5416503f8fb3762223ebdb69da\
     085ac1e43e15996e458f3613d0f11d8c\
     387b2eaeb4302aeeb00d291612bb0c00";

// ----------------------------------------------------------------
// RFC 8032 §7.1 — TEST 3 (2-byte 0xaf 0x82)
// ----------------------------------------------------------------

const TEST3_SEED: &str =
    "c5aa8df43f9f837bedb7442f31dcb7b1\
     66d38535076f094b85ce3a2e0b4458f7";
const TEST3_PK: &str =
    "fc51cd8e6218a1a38da47ed00230f058\
     0816ed13ba3303ac5deb911548908025";
const TEST3_MSG: &str = "af82";
const TEST3_SIG: &str =
    "6291d657deec24024827e69c3abe01a3\
     0ce548a284743a445e3680d7db5ac3ac\
     18ff9b538d16f290ae67f760984dc659\
     4a7c15e9716ed28dc027beceea1ec40a";

#[test]
fn rfc8032_test1_pk() {
    let seed = h32(TEST1_SEED);
    let pk = public_key_from_seed(&seed);
    assert_eq!(pk, h32(TEST1_PK), "TEST 1: derived public key mismatch");
}

// The extracted `sign.rs` now threads `msg_len` into both `sha512_64`
// calls (nonce_hash_len = 32 + msg_len, chal_hash_len = 64 + msg_len),
// so signatures match RFC 8032 exactly for any msg_len ≤ 4096.  This
// closes the "len arg dropped" emitter gap (Bug A) referenced in
// older comments here.

#[test]
fn rfc8032_test1_sign_empty() {
    let seed = h32(TEST1_SEED);
    let mut sig = [0u8; 64];
    sign(&mut sig, &seed, &[]);
    assert_eq!(sig, h64(TEST1_SIG), "TEST 1: signature mismatch");
}

#[test]
fn rfc8032_test1_sign_runs() {
    // Smoke test: the extracted body runs end-to-end without panicking
    // and produces a well-formed signature (R-half is a canonical point).
    let seed = h32(TEST1_SEED);
    let mut sig = [0u8; 64];
    sign(&mut sig, &seed, &[]);
    let r_bytes: [u8; 32] = sig[0..32].try_into().unwrap();
    assert!(
        curve25519_dalek::edwards::CompressedEdwardsY(r_bytes)
            .decompress()
            .is_some(),
        "extracted sign produced non-canonical R"
    );
}

#[test]
fn rfc8032_test1_verify_empty() {
    let pk = h32(TEST1_PK);
    let sig = h64(TEST1_SIG);
    assert!(verify(&sig, &pk, &[]), "TEST 1: verification rejected valid sig");
}

#[test]
fn rfc8032_test2_pk() {
    let seed = h32(TEST2_SEED);
    let pk = public_key_from_seed(&seed);
    assert_eq!(pk, h32(TEST2_PK), "TEST 2: derived public key mismatch");
}

#[test]
fn rfc8032_test2_sign() {
    let seed = h32(TEST2_SEED);
    let msg = h(TEST2_MSG);
    let mut sig = [0u8; 64];
    sign(&mut sig, &seed, &msg);
    assert_eq!(sig, h64(TEST2_SIG), "TEST 2: signature mismatch");
}

#[test]
fn rfc8032_test2_verify() {
    let pk = h32(TEST2_PK);
    let sig = h64(TEST2_SIG);
    let msg = h(TEST2_MSG);
    assert!(verify(&sig, &pk, &msg), "TEST 2: verification rejected valid sig");
}

#[test]
fn rfc8032_test3_pk() {
    let seed = h32(TEST3_SEED);
    let pk = public_key_from_seed(&seed);
    assert_eq!(pk, h32(TEST3_PK), "TEST 3: derived public key mismatch");
}

#[test]
fn rfc8032_test3_sign() {
    let seed = h32(TEST3_SEED);
    let msg = h(TEST3_MSG);
    let mut sig = [0u8; 64];
    sign(&mut sig, &seed, &msg);
    assert_eq!(sig, h64(TEST3_SIG), "TEST 3: signature mismatch");
}

#[test]
fn rfc8032_test3_verify() {
    let pk = h32(TEST3_PK);
    let sig = h64(TEST3_SIG);
    let msg = h(TEST3_MSG);
    assert!(verify(&sig, &pk, &msg), "TEST 3: verification rejected valid sig");
}

// Sanity: verify must REJECT a corrupted signature.
#[test]
fn rfc8032_test2_reject_bad_sig() {
    let pk = h32(TEST2_PK);
    let mut sig = h64(TEST2_SIG);
    sig[0] ^= 1; // flip a bit in R
    let msg = h(TEST2_MSG);
    assert!(!verify(&sig, &pk, &msg), "TEST 2: corrupted sig was accepted");
}

#[test]
fn rfc8032_test2_reject_bad_msg() {
    let pk = h32(TEST2_PK);
    let sig = h64(TEST2_SIG);
    assert!(
        !verify(&sig, &pk, &[0x73]), // off-by-one message
        "TEST 2: sig of wrong message was accepted"
    );
}
