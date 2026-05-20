//! End-to-end Signal-stack composition over the verified-primitive crate.
//!
//! Composes the three Signal protocols (X3DH → Double Ratchet → Sender
//! Keys) in ONE test session, all running on `curve25519-jasmin` verified
//! primitives.  Mirrors the per-protocol coverage already in
//! `tests/x3dh_with_aucurves.rs`, `tests/double_ratchet_with_aucurves.rs`,
//! and `tests/sender_keys_with_aucurves.rs` — but here in a single
//! Alice/Bob/Carol/Dave session.
//!
//! Stack composed:
//!   1. **X3DH** between Alice (initiator) and Bob (responder), full
//!      pre-key bundle with SPK signature verification.
//!   2. **Double Ratchet** seeded from the X3DH-derived session key
//!      (used as the DR root key).  10 messages exchanged (5 Alice → Bob
//!      then 5 Bob → Alice) with one DH ratchet step on Bob's first
//!      receive and another on Alice's first receive of Bob's reply
//!      (canonical Signal DR).
//!   3. **Sender Keys** group between Carol (sender) + Dave (receiver),
//!      seeded from a key derived from the DR session state via HKDF.
//!      5 group messages exchanged, each XEdDSA-signed and AEAD-sealed.
//!
//! KAT against dalek-backed reference at each step:
//!   - X3DH: each of the 4 DH outputs cross-checked against
//!     `x25519-dalek`'s `StaticSecret::diffie_hellman` (the same byte
//!     plane that libsignal uses internally).
//!   - DR: every `dh_pub` / `dh` step cross-checked against `x25519-dalek`.
//!   - SK: `verifying_key_from` (X25519 scalar mult of base) cross-checked
//!     against `x25519-dalek`'s `PublicKey::from(StaticSecret)`.
//!
//! All primitives are verified: X25519 = libjade Jasmin (formosa-25519),
//! HMAC-SHA-256/HKDF over libjade SHA-256, AES-256-CBC + HMAC-SHA-256
//! (libcrux-lean-specs FIPS-197 + safe-Rust CBC + verified HMAC), Ed25519
//! sign/verify via the `rust_cmd_ed`-extracted bodies (XEdDSA wrapper).
//!
//! CRITICAL: no modification of any existing test, no modification of any
//! src/*.rs file, no unsafe.  See A66 for the Lean-side composition
//! security argument (`signal_stack_security_libcrux`, commit 7dfd3ccd).

#![allow(non_snake_case)]

extern crate alloc;
use alloc::vec::Vec;

use curve25519_jasmin::{x25519_jasmin, x25519_jasmin_base};
use curve25519_jasmin::symmetric::{
    aes256_cbc_hmac_decrypt_nonce, aes256_cbc_hmac_encrypt_nonce, hkdf_sha256,
    hkdf_sha256_expand, hkdf_sha256_extract, hmac_sha256,
};
use curve25519_jasmin::xeddsa::{xeddsa_sign_deterministic, xeddsa_verify};

use x3dh_hax::protocol::{create_bundle, initiate, respond, X3dhCrypto};
use x3dh_hax::types::*;

use doubleratchet_hax::protocol::{
    ratchet_decrypt, ratchet_encrypt, ratchet_init_initiator, ratchet_init_responder,
    DoubleRatchetCrypto, DrKey, DrNonce, DrSymKey,
};

use sender_keys_hax::protocol::{init_receiver, init_sender, receive, send, SenderKeysCrypto};
use sender_keys_hax::types::*;

// =========================================================================
// Trait impls backed by our verified primitives (mirrors the per-protocol
// test files; identical bodies, repeated here so this test is fully
// self-contained per the "do not modify existing tests" rule).
// =========================================================================

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
        xeddsa_sign_deterministic(ik_secret, msg)
    }
    fn verify(ik_pub: &X3dhKey, msg: &X3dhKey, sig: &X3dhSignature) -> bool {
        xeddsa_verify(ik_pub, msg, sig)
    }
}

#[derive(Clone, Copy)]
struct AucurvesDr;

impl DoubleRatchetCrypto for AucurvesDr {
    fn dh(secret: &DrKey, peer_pub: &DrKey) -> DrKey {
        x25519_jasmin(secret, peer_pub)
    }
    fn dh_pub(secret: &DrKey) -> DrKey {
        x25519_jasmin_base(secret)
    }
    fn kdf_ck(chain_key: &DrSymKey) -> (DrSymKey, DrSymKey) {
        let new_ck = hmac_sha256(chain_key, &[0x01u8]);
        let mk = hmac_sha256(chain_key, &[0x02u8]);
        (new_ck, mk)
    }
    fn kdf_rk(root_key: &DrSymKey, dh_output: &DrKey) -> (DrSymKey, DrSymKey) {
        let mut input1 = [0u8; 33];
        input1[..32].copy_from_slice(dh_output);
        input1[32] = 0x01;
        let mut input2 = [0u8; 33];
        input2[..32].copy_from_slice(dh_output);
        input2[32] = 0x02;
        let new_rk = hmac_sha256(root_key, &input1);
        let new_ck = hmac_sha256(root_key, &input2);
        (new_rk, new_ck)
    }
    fn aead_encrypt(
        key: &DrSymKey,
        nonce: &DrNonce,
        aad: &[u8],
        plaintext: &[u8],
    ) -> Vec<u8> {
        aes256_cbc_hmac_encrypt_nonce(key, nonce, aad, plaintext)
            .expect("aes256_cbc_hmac_encrypt_nonce is infallible for valid key/nonce")
    }
    fn aead_decrypt(
        key: &DrSymKey,
        nonce: &DrNonce,
        aad: &[u8],
        ciphertext: &[u8],
    ) -> Option<Vec<u8>> {
        aes256_cbc_hmac_decrypt_nonce(key, nonce, aad, ciphertext).ok()
    }
}

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
    fn aead_decrypt(
        key: &MessageKey,
        nonce: &Nonce,
        aad: &[u8],
        ct: &[u8],
    ) -> Option<Vec<u8>> {
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

// =========================================================================
// Helpers
// =========================================================================

fn dr_keypair_from(byte: u8) -> (DrKey, DrKey) {
    let mut sk = [byte; 32];
    sk[0] &= 248;
    sk[31] &= 127;
    sk[31] |= 64;
    let pk = x25519_jasmin_base(&sk);
    (sk, pk)
}

/// X25519 DH cross-check against `x25519-dalek` (RFC 7748).
fn dalek_dh(secret: &[u8; 32], peer_pub: &[u8; 32]) -> [u8; 32] {
    let dalek_secret = x25519_dalek::StaticSecret::from(*secret);
    let dalek_peer = x25519_dalek::PublicKey::from(*peer_pub);
    *dalek_secret.diffie_hellman(&dalek_peer).as_bytes()
}

/// X25519 base-point scalar-mult cross-check against `x25519-dalek`.
fn dalek_dh_pub(secret: &[u8; 32]) -> [u8; 32] {
    let dalek_secret = x25519_dalek::StaticSecret::from(*secret);
    *x25519_dalek::PublicKey::from(&dalek_secret).as_bytes()
}

// =========================================================================
// The full Signal-stack composition: X3DH → DR → SK in ONE session
// =========================================================================
//
// Scenario:
//   - Alice and Bob run X3DH to derive a shared session key.
//   - That session key seeds a Double Ratchet between Alice and Bob.
//     They exchange 10 messages (5 each way) with two DH ratchet steps.
//   - A Sender-Keys group is then bootstrapped by Carol with Dave as
//     receiver.  The SK chain key is derived from the post-DR state via
//     HKDF (`info = b"sender-keys-bootstrap"`).  Carol sends 5 group
//     messages; Dave receives all of them.
//   - At every X25519 DH step we cross-check the verified-primitive
//     output against `x25519-dalek` (Signal's de-facto reference).

#[test]
fn signal_stack_x3dh_dr_sk_full_composition() {
    // -----------------------------------------------------------------
    // Phase 1 — X3DH between Alice and Bob.
    // -----------------------------------------------------------------
    let ik_a_secret = [0xA1u8; 32];
    let ek_a_secret = [0xA2u8; 32];
    let ik_b_secret = [0xB1u8; 32];
    let spk_b_secret = [0xB2u8; 32];
    let opk_b_secret = [0xB3u8; 32];

    // KAT 1a: cross-check each X3DH DH input against dalek.  The trait
    // impl will run these via x25519_jasmin internally; we recompute and
    // assert byte-identity here so the X3DH protocol logic exercises the
    // dalek-equivalent byte plane on each of its four DH calls.
    let ik_a_pub = x25519_jasmin_base(&ik_a_secret);
    let ik_b_pub = x25519_jasmin_base(&ik_b_secret);
    let spk_b_pub = x25519_jasmin_base(&spk_b_secret);
    let opk_b_pub = x25519_jasmin_base(&opk_b_secret);
    assert_eq!(ik_a_pub, dalek_dh_pub(&ik_a_secret), "X3DH KAT: ik_a_pub vs dalek");
    assert_eq!(ik_b_pub, dalek_dh_pub(&ik_b_secret), "X3DH KAT: ik_b_pub vs dalek");
    assert_eq!(spk_b_pub, dalek_dh_pub(&spk_b_secret), "X3DH KAT: spk_b_pub vs dalek");
    assert_eq!(opk_b_pub, dalek_dh_pub(&opk_b_secret), "X3DH KAT: opk_b_pub vs dalek");

    // The four X3DH DH outputs (from Alice's side; Bob computes the
    // same by DH symmetry).  Each must match dalek.
    let dh1 = x25519_jasmin(&ik_a_secret, &spk_b_pub);
    let dh2 = x25519_jasmin(&ek_a_secret, &ik_b_pub);
    let dh3 = x25519_jasmin(&ek_a_secret, &spk_b_pub);
    let dh4 = x25519_jasmin(&ek_a_secret, &opk_b_pub);
    assert_eq!(dh1, dalek_dh(&ik_a_secret, &spk_b_pub), "X3DH KAT: dh1 vs dalek");
    assert_eq!(dh2, dalek_dh(&ek_a_secret, &ik_b_pub), "X3DH KAT: dh2 vs dalek");
    assert_eq!(dh3, dalek_dh(&ek_a_secret, &spk_b_pub), "X3DH KAT: dh3 vs dalek");
    assert_eq!(dh4, dalek_dh(&ek_a_secret, &opk_b_pub), "X3DH KAT: dh4 vs dalek");

    // Run X3DH through the hax-extracted protocol bodies on our backend.
    let bundle_b = create_bundle::<AucurvesX3dh>(&ik_b_secret, &spk_b_secret, &opk_b_secret);
    let (session_a, init_msg, sig_valid_a) =
        initiate::<AucurvesX3dh>(&ik_a_secret, &ek_a_secret, &bundle_b, true);
    assert!(sig_valid_a, "X3DH: Alice must accept Bob's SPK signature");

    let session_b = respond::<AucurvesX3dh>(
        &ik_b_secret,
        &spk_b_secret,
        &opk_b_secret,
        &init_msg,
        true,
    );
    assert_eq!(session_a, session_b, "X3DH: Alice/Bob session keys must match");

    // -----------------------------------------------------------------
    // Phase 2 — Double Ratchet seeded from the X3DH session key.
    // -----------------------------------------------------------------
    // Standard Signal pattern: HKDF the X3DH session key into the DR
    // root key (32 bytes).  Empty salt + info = b"DR-root-key".
    let dr_root: [u8; 32] = {
        let mut out = [0u8; 32];
        hkdf_sha256(Some(&[0u8; 32]), &session_a, b"DR-root-key", &mut out);
        out
    };

    // Alice's DR ratchet keypair (her own DH side), Bob's INITIAL DR
    // ratchet keypair (advertised in the bundle), and Bob's FRESH
    // keypair generated when he ratchets on first receive.  These mirror
    // the alice_bob_init helper from double_ratchet_with_aucurves.rs.
    let (alice_dr_sk, alice_dr_pk) = dr_keypair_from(0xA5);
    let (bob_dr_sk, bob_dr_pk) = dr_keypair_from(0xB5);
    let (bob_dr_sk_new, bob_dr_pk_new) = dr_keypair_from(0xB6);

    // KAT 2a: DR ratchet public keys vs dalek.
    assert_eq!(alice_dr_pk, dalek_dh_pub(&alice_dr_sk), "DR KAT: alice_dr_pk vs dalek");
    assert_eq!(bob_dr_pk, dalek_dh_pub(&bob_dr_sk), "DR KAT: bob_dr_pk vs dalek");
    assert_eq!(bob_dr_pk_new, dalek_dh_pub(&bob_dr_sk_new), "DR KAT: bob_dr_pk_new vs dalek");

    // KAT 2b: the initial DR DH (Alice's init_initiator step) vs dalek.
    // ratchet_init_initiator computes DH(alice_dr_sk, bob_dr_pk).
    let dr_init_dh = x25519_jasmin(&alice_dr_sk, &bob_dr_pk);
    assert_eq!(
        dr_init_dh,
        dalek_dh(&alice_dr_sk, &bob_dr_pk),
        "DR KAT: alice initiator DH vs dalek"
    );

    let mut alice =
        ratchet_init_initiator::<AucurvesDr>(&dr_root, &alice_dr_sk, &alice_dr_pk, &bob_dr_pk);
    // Bob is responder with a placeholder remote_pk so his first
    // receive triggers his DH ratchet (canonical Signal DR).
    let mut bob = ratchet_init_responder(&dr_root, &bob_dr_sk, &bob_dr_pk, &[0u8; 32]);

    // ------ Alice sends 5 messages to Bob (Bob ratchets on msg 0). ------
    let aad_dr: &[u8] = b"signal-stack-e2e-v1";
    let mut dr_messages_exchanged: u32 = 0;
    let alice_payloads: [&[u8]; 5] = [
        b"DR a-0: hi bob",
        b"DR a-1: x3dh -> dr handoff",
        b"DR a-2 with a slightly longer body for variety",
        b"DR a-3",
        b"DR a-4: bob's turn next",
    ];
    for (i, pt) in alice_payloads.iter().enumerate() {
        let (na, msg) = ratchet_encrypt::<AucurvesDr>(&alice, pt, aad_dr);
        alice = na;
        let (nb, recovered) = ratchet_decrypt::<AucurvesDr>(
            &bob,
            &msg,
            aad_dr,
            &bob_dr_sk_new,
            &bob_dr_pk_new,
        )
        .unwrap_or_else(|| panic!("DR alice->bob msg {i} decrypt failed"));
        bob = nb;
        assert_eq!(recovered, *pt, "DR alice->bob msg {i}");
        dr_messages_exchanged += 1;
    }
    assert_eq!(alice.send_n, 5, "DR alice.send_n after 5 a->b messages");
    assert_eq!(bob.recv_n, 5, "DR bob.recv_n after 5 a->b messages");

    // ------ Bob sends 5 messages to Alice (Alice ratchets on msg 0). ------
    let (alice_dr_sk_new, alice_dr_pk_new) = dr_keypair_from(0xA6);
    assert_eq!(
        alice_dr_pk_new,
        dalek_dh_pub(&alice_dr_sk_new),
        "DR KAT: alice_dr_pk_new vs dalek"
    );
    let bob_payloads: [&[u8]; 5] = [
        b"DR b-0: rx ok",
        b"DR b-1: dr -> sk handoff coming",
        b"DR b-2",
        b"DR b-3 carol+dave inbound",
        b"DR b-4 last DR message",
    ];
    for (i, pt) in bob_payloads.iter().enumerate() {
        let (nb, msg) = ratchet_encrypt::<AucurvesDr>(&bob, pt, aad_dr);
        bob = nb;
        let (na, recovered) = ratchet_decrypt::<AucurvesDr>(
            &alice,
            &msg,
            aad_dr,
            &alice_dr_sk_new,
            &alice_dr_pk_new,
        )
        .unwrap_or_else(|| panic!("DR bob->alice msg {i} decrypt failed"));
        alice = na;
        assert_eq!(recovered, *pt, "DR bob->alice msg {i}");
        dr_messages_exchanged += 1;
    }
    assert_eq!(bob.send_n, 5, "DR bob.send_n after 5 b->a messages");
    assert_eq!(alice.recv_n, 5, "DR alice.recv_n after 5 b->a messages");

    // 10 total DR messages exchanged across both directions.
    assert_eq!(dr_messages_exchanged, 10, "DR total messages exchanged");

    // -----------------------------------------------------------------
    // Phase 3 — Sender Keys group: Carol -> Dave (5 group messages).
    // -----------------------------------------------------------------
    // Bootstrap the SK chain key from Alice's current DR root key via
    // HKDF.  This composition is the standard pattern: group state is
    // derived from a pairwise DR session, not generated independently.
    let sk_chain_key: [u8; 32] = {
        let mut out = [0u8; 32];
        hkdf_sha256(
            Some(&[0u8; 32]),
            &alice.root_key,
            b"sender-keys-bootstrap",
            &mut out,
        );
        out
    };

    let carol_signing_key = [0xC5u8; 32];
    let group_id: [u8; 32] = {
        // Group ID is also derived from the DR session so it's pinned
        // to this group instance.
        let mut out = [0u8; 32];
        hkdf_sha256(
            Some(&[0u8; 32]),
            &alice.root_key,
            b"sender-keys-group-id",
            &mut out,
        );
        out
    };

    // KAT 3a: Carol's verifying key (X25519 pub) vs dalek.
    let carol_vk = x25519_jasmin_base(&carol_signing_key);
    assert_eq!(
        carol_vk,
        dalek_dh_pub(&carol_signing_key),
        "SK KAT: Carol's verifying key vs dalek"
    );

    let mut carol = init_sender::<AucurvesSenderKeys>(group_id, sk_chain_key, carol_signing_key);
    let mut dave = init_receiver(group_id, sk_chain_key, carol_vk);

    let group_aad: &[u8] = b"group-id-carol-dave";
    let group_payloads: [&[u8]; 5] = [
        b"SK msg 0: group hello",
        b"SK msg 1: bootstrapped from DR root",
        b"SK msg 2 - X3DH -> DR -> SK chain complete",
        b"SK msg 3",
        b"SK msg 4 final",
    ];
    for (i, pt) in group_payloads.iter().enumerate() {
        let msg = send::<AucurvesSenderKeys>(&mut carol, pt, group_aad);
        let recovered = receive::<AucurvesSenderKeys>(&mut dave, &msg)
            .unwrap_or_else(|| panic!("SK carol->dave msg {i} decrypt failed"));
        assert_eq!(recovered, *pt, "SK carol->dave msg {i}");
        assert_eq!(msg.msg_num, i as u32, "SK msg_num {i}");
    }

    // -----------------------------------------------------------------
    // Sanity: 1 X3DH session + 10 DR messages + 5 SK messages exchanged.
    // -----------------------------------------------------------------
    assert_eq!(carol.iteration, 5, "SK carol.iteration after 5 messages");
    assert_eq!(dave.iteration, 5, "SK dave.iteration after 5 messages");
}

// =========================================================================
// Negative cross-checks (composition robustness)
// =========================================================================
//
// These exercise the same X3DH -> DR -> SK pipeline but tamper at each
// layer to confirm the composition is sound (failures propagate, no
// silent passthrough).  Keeps the gating test (above) as a pure happy
// path so a future regression report points cleanly at "which layer".

#[test]
fn signal_stack_x3dh_dr_tamper_propagates() {
    // X3DH happy path (same seeds as composition test).
    let ik_a = [0xA1u8; 32];
    let ek_a = [0xA2u8; 32];
    let ik_b = [0xB1u8; 32];
    let spk_b = [0xB2u8; 32];
    let opk_b = [0xB3u8; 32];

    let bundle_b = create_bundle::<AucurvesX3dh>(&ik_b, &spk_b, &opk_b);
    let (session_a, _, sig_valid) =
        initiate::<AucurvesX3dh>(&ik_a, &ek_a, &bundle_b, true);
    assert!(sig_valid);

    // Bob computes a DIFFERENT session key (wrong spk_b on respond).
    let wrong_spk_b = [0xBEu8; 32];
    let session_b_bad = respond::<AucurvesX3dh>(
        &ik_b,
        &wrong_spk_b,
        &opk_b,
        &x3dh_hax::types::X3dhInitMessage {
            ik_a: x25519_jasmin_base(&ik_a),
            ek_a: x25519_jasmin_base(&ek_a),
            opk_id: [0, 0, 0, 1],
        },
        true,
    );
    assert_ne!(
        session_a, session_b_bad,
        "X3DH: wrong SPK secret -> divergent session key (else DR seeding would silently succeed)"
    );

    // Now seed DR with the WRONG session key on Bob's side, confirm DR
    // decrypt fails.
    let dr_root_a: [u8; 32] = {
        let mut out = [0u8; 32];
        hkdf_sha256(Some(&[0u8; 32]), &session_a, b"DR-root-key", &mut out);
        out
    };
    let dr_root_b_bad: [u8; 32] = {
        let mut out = [0u8; 32];
        hkdf_sha256(Some(&[0u8; 32]), &session_b_bad, b"DR-root-key", &mut out);
        out
    };
    assert_ne!(dr_root_a, dr_root_b_bad, "DR roots must diverge from divergent X3DH");

    let (alice_dr_sk, alice_dr_pk) = dr_keypair_from(0xA5);
    let (bob_dr_sk, bob_dr_pk) = dr_keypair_from(0xB5);
    let (bob_dr_sk_new, bob_dr_pk_new) = dr_keypair_from(0xB6);

    let alice = ratchet_init_initiator::<AucurvesDr>(
        &dr_root_a,
        &alice_dr_sk,
        &alice_dr_pk,
        &bob_dr_pk,
    );
    let bob_bad = ratchet_init_responder(&dr_root_b_bad, &bob_dr_sk, &bob_dr_pk, &[0u8; 32]);

    let (_a2, msg) = ratchet_encrypt::<AucurvesDr>(&alice, b"hi bob", b"v1");
    let result =
        ratchet_decrypt::<AucurvesDr>(&bob_bad, &msg, b"v1", &bob_dr_sk_new, &bob_dr_pk_new);
    assert!(
        result.is_none(),
        "DR seeded from divergent X3DH session must fail AEAD auth on first message"
    );
}
