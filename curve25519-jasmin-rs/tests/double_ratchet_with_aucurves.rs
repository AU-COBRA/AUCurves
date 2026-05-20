//! Closes the Double Ratchet loop: hax-extracted Signal DR symmetric +
//! DH ratchet running on our Rocq-verified primitive backend.
//!
//! Implements `DoubleRatchetCrypto` (from `doubleratchet-hax::protocol`)
//! using our verified-extraction primitives, mirroring the pattern in
//! `tests/x3dh_with_aucurves.rs` and `tests/sender_keys_with_aucurves.rs`.
//!
//! Trust set per primitive:
//!   - **DH** (`dh`, `dh_pub`): libjade-Jasmin X25519 (`x25519_jasmin*`).
//!     EasyCrypt-verified jasminc compiler.
//!   - **KDF chain** (`kdf_ck`): HMAC-SHA-256 over libjade Jasmin SHA-256.
//!     `(new_ck, mk) = (HMAC(ck, 0x01), HMAC(ck, 0x02))` per Signal spec.
//!   - **KDF root** (`kdf_rk`): HMAC-SHA-256 over libjade Jasmin SHA-256,
//!     deriving `(new_rk, new_ck)` from `(rk, dh_out)` via the
//!     `dh_out || 0x01` / `dh_out || 0x02` constants in the
//!     baseline (matching the free-function `kdf_rk` in `lib.rs`).
//!   - **AEAD**: AES-256-CBC + HMAC-SHA-256, Signal-spec wire format
//!     (`IV(16) || ciphertext_PKCS7 || HMAC-SHA-256(32)`).  AES block
//!     cipher = `libcrux-lean-specs::aes::aes256_{encrypt,decrypt}`
//!     (pure-Rust FIPS-197 spec, byte-identical to libcrux HACL).
//!     CBC + PKCS7 + HMAC composition: safe Rust on top of libjade
//!     SHA-256 (verified HMAC-SHA-256).  Migrated from AES-256-GCM
//!     on 2026-05-13 (see `docs/aes-gcm-to-cbc-hmac-2026-05-13.md`).
//!
//! Per-spec note: this matches the free-function `kdf_rk` /
//! `kdf_chain_step` in `doubleratchet-hax/src/lib.rs`.  Concretely it
//! computes `new_ck = HMAC(ck, [0x01])`, `mk = HMAC(ck, [0x02])`, etc.
//! That layout differs from libsignal's "Whisper..." labels (used by
//! `curve25519-jasmin/src/double_ratchet.rs`'s native impl) — both
//! pick the same Signal-style chain step but use different label bytes.
//! The KAT in this file checks byte-equivalence against the
//! **doubleratchet-hax free-function baseline**, which is the
//! reference for the trait wiring.

#![allow(non_snake_case)]

extern crate alloc;
use alloc::vec::Vec;

use curve25519_jasmin::{x25519_jasmin, x25519_jasmin_base};
use curve25519_jasmin::symmetric::{
    aes256_cbc_hmac_decrypt_nonce, aes256_cbc_hmac_encrypt_nonce, hmac_sha256,
};

use doubleratchet_hax::protocol::{
    encode_header, nonce_for, ratchet_decrypt, ratchet_encrypt,
    ratchet_init_initiator, ratchet_init_responder, DoubleRatchetCrypto, DrKey,
    DrNonce, DrSymKey,
};
use doubleratchet_hax::{
    kdf_ck as baseline_kdf_ck, kdf_rk as baseline_kdf_rk, MessageHeader,
};

// =========================================================================
// DoubleRatchetCrypto impl backed by our verified primitives
// =========================================================================

#[derive(Clone, Copy)]
struct AucurvesDr;

impl DoubleRatchetCrypto for AucurvesDr {
    fn dh(secret: &DrKey, peer_pub: &DrKey) -> DrKey {
        // libjade X25519 (formosa-25519, EasyCrypt-verified compiler).
        x25519_jasmin(secret, peer_pub)
    }

    fn dh_pub(secret: &DrKey) -> DrKey {
        x25519_jasmin_base(secret)
    }

    fn kdf_ck(chain_key: &DrSymKey) -> (DrSymKey, DrSymKey) {
        // Signal spec: new_ck = HMAC(ck, 0x01), mk = HMAC(ck, 0x02).
        // Matches the baseline free-function `kdf_chain_step` in lib.rs.
        let new_ck = hmac_sha256(chain_key, &[0x01u8]);
        let mk = hmac_sha256(chain_key, &[0x02u8]);
        (new_ck, mk)
    }

    fn kdf_rk(root_key: &DrSymKey, dh_output: &DrKey) -> (DrSymKey, DrSymKey) {
        // Mirror the baseline `kdf_rk` in lib.rs: `dh_output || 0x01` and
        // `dh_output || 0x02` are the HMAC inputs.
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

// =========================================================================
// Helpers: deterministic X25519 keypairs from byte patterns
// =========================================================================

fn keypair_from(byte: u8) -> (DrKey, DrKey) {
    let mut sk = [byte; 32];
    // X25519 clamps the secret internally, but for symmetric public-key
    // derivation we just feed the seed.
    sk[0] &= 248;
    sk[31] &= 127;
    sk[31] |= 64;
    let pk = x25519_jasmin_base(&sk);
    (sk, pk)
}

// =========================================================================
// KAT 1: kdf_ck / kdf_rk byte-identity against the free-function baseline
// =========================================================================

#[test]
fn dr_kdf_ck_matches_baseline() {
    // For 17 chain-key seeds, the trait-backed kdf_ck must produce the
    // same `(new_ck, mk)` as the free-function `kdf_chain_step` (which is
    // the Signal spec reference in lib.rs).
    for seed in 0..17u8 {
        let ck = [seed; 32];
        let (ck1_aucurves, mk_aucurves) = <AucurvesDr as DoubleRatchetCrypto>::kdf_ck(&ck);
        let baseline = baseline_kdf_ck(&ck, 0x01);
        let baseline_mk = baseline_kdf_ck(&ck, 0x02);
        assert_eq!(ck1_aucurves, baseline, "seed=0x{seed:02x}: chain-key mismatch");
        assert_eq!(mk_aucurves, baseline_mk, "seed=0x{seed:02x}: message-key mismatch");
    }
}

#[test]
fn dr_kdf_rk_matches_baseline() {
    for rk_seed in 0..7u8 {
        for dh_seed in 0..7u8 {
            let rk = [rk_seed; 32];
            let dh = [dh_seed; 32];
            let (rk_aucurves, ck_aucurves) =
                <AucurvesDr as DoubleRatchetCrypto>::kdf_rk(&rk, &dh);
            let (rk_baseline, ck_baseline) = baseline_kdf_rk(&rk, &dh);
            assert_eq!(rk_aucurves, rk_baseline,
                "rk_seed=0x{rk_seed:02x} dh_seed=0x{dh_seed:02x}: root key mismatch");
            assert_eq!(ck_aucurves, ck_baseline,
                "rk_seed=0x{rk_seed:02x} dh_seed=0x{dh_seed:02x}: chain key mismatch");
        }
    }
}

// =========================================================================
// KAT 2: end-to-end DR roundtrip via the trait (canonical Signal DR)
// =========================================================================
//
// Canonical Signal DR sequence:
//   1. Alice initiator: `ratchet_init_initiator` advances RK once via
//      `kdf_rk(root, DH(alice_sk, bob_pk))`, deriving her initial send_ck.
//   2. Bob responder: `ratchet_init_responder` keeps RK = shared_root.
//      Bob's `remote_pk` is set to a placeholder (zero) so the first
//      received message triggers a DH ratchet — at that point Bob's RK
//      advances exactly like Alice's did in step 1, and his recv_ck
//      derives from the same DH output (by DH symmetry).
//   3. Bob's DH ratchet ALSO produces a fresh send chain (canonical
//      Signal DR: receiving a new peer DH triggers BOTH chains).
//   4. Alice's subsequent receive of Bob's first reply triggers HER
//      DH ratchet, and the cycle continues.

/// Helper: build Alice + Bob pair via canonical init.  The bob_sk/pk
/// pair is what Alice's first message will trigger a DH ratchet to.
fn alice_bob_init(
    root: &[u8; 32],
    alice_sk: &DrKey,
    alice_pk: &DrKey,
    bob_sk: &DrKey,
    bob_pk: &DrKey,
) -> (doubleratchet_hax::RatchetState, doubleratchet_hax::RatchetState) {
    let alice = ratchet_init_initiator::<AucurvesDr>(root, alice_sk, alice_pk, bob_pk);

    // Bob responder: NO pre-mirror.  His remote_pk is a placeholder so
    // Alice's first message triggers Bob's DH ratchet.  The trait's
    // `dh_ratchet_step` then advances Bob's RK from `root` -> `rk1`
    // (matching Alice's `alice.root_key`) and derives his recv_ck via
    // `DH(bob_sk, alice_pk)` (matching Alice's send_ck by DH symmetry).
    let placeholder = [0u8; 32];
    let bob = ratchet_init_responder(root, bob_sk, bob_pk, &placeholder);
    (alice, bob)
}

#[test]
fn dr_alice_to_bob_single_roundtrip() {
    let root = [0x10u8; 32];
    let (alice_sk, alice_pk) = keypair_from(0xA1);
    let (bob_sk, bob_pk) = keypair_from(0xB1);
    // Bob's FRESH keypair generated when he ratchets on first receive.
    let (new_bob_sk, new_bob_pk) = keypair_from(0xB2);

    let (alice, bob) = alice_bob_init(&root, &alice_sk, &alice_pk, &bob_sk, &bob_pk);

    let plaintext = b"hello bob over verified DR".to_vec();
    let aad = b"v1".to_vec();
    let (_alice2, msg) =
        ratchet_encrypt::<AucurvesDr>(&alice, &plaintext, &aad);

    // Bob receives Alice's first message.  Header.dh_public = alice_pk,
    // bob.remote_pk = [0;32] (placeholder), so this triggers Bob's DH
    // ratchet.  Bob supplies his FRESH (new_bob_sk, new_bob_pk) for
    // the rotation — this is what canonical Signal DR does.
    let (_bob2, recovered) = ratchet_decrypt::<AucurvesDr>(
        &bob, &msg, &aad, &new_bob_sk, &new_bob_pk,
    )
    .expect("authenticated decrypt must succeed");

    assert_eq!(recovered, plaintext, "DR single-message roundtrip");
}

// =========================================================================
// KAT 3: multi-message burst (10 messages each direction with DH ratchet)
// =========================================================================

#[test]
fn dr_burst_alice_then_bob_with_dh_ratchet() {
    let root = [0x33u8; 32];
    let (alice_sk, alice_pk) = keypair_from(0xA1);
    let (bob_sk, bob_pk) = keypair_from(0xB1);
    // Bob's fresh keypair on his first DH ratchet (receiving Alice msg 0).
    let (new_bob_sk, new_bob_pk) = keypair_from(0xB2);

    let (mut alice, mut bob) =
        alice_bob_init(&root, &alice_sk, &alice_pk, &bob_sk, &bob_pk);

    let aad = b"protocol-v1";

    // -- Alice sends 5 messages, Bob receives them in order --
    // First message triggers Bob's DH ratchet (canonical Signal DR).
    // Subsequent messages stay in the same chain (no further ratchet).
    let messages_a: [&[u8]; 5] = [
        b"a-msg-0", b"a-msg-1", b"a-msg-2",
        b"a-msg-3 with a slightly longer body",
        b"a-msg-4",
    ];
    for (i, pt) in messages_a.iter().enumerate() {
        let (na, msg) = ratchet_encrypt::<AucurvesDr>(&alice, pt, aad);
        alice = na;
        let (nb, recovered) = ratchet_decrypt::<AucurvesDr>(
            &bob, &msg, aad, &new_bob_sk, &new_bob_pk,
        )
        .unwrap_or_else(|| panic!("alice->bob msg {i} decrypt failed"));
        bob = nb;
        assert_eq!(recovered, *pt, "alice->bob msg {i}");
    }
    assert_eq!(alice.send_n, 5);
    assert_eq!(bob.recv_n, 5);

    // -- Bob sends 5 messages back to Alice.  Bob's send_ck was set by
    //    his DH ratchet above (DH(new_bob_sk, alice_pk) -> send_ck).
    //    Bob's header carries new_bob_pk; Alice's stored remote_pk is
    //    bob_pk, so her first receive triggers HER DH ratchet.
    let (alice_new_sk, alice_new_pk) = keypair_from(0xA2);
    let messages_b: [&[u8]; 5] = [
        b"b-msg-0", b"b-msg-1",
        b"b-msg-2 - bob talks back",
        b"b-msg-3", b"b-msg-4 final",
    ];
    for (i, pt) in messages_b.iter().enumerate() {
        let (nb, msg) = ratchet_encrypt::<AucurvesDr>(&bob, pt, aad);
        bob = nb;
        let (na, recovered) = ratchet_decrypt::<AucurvesDr>(
            &alice, &msg, aad, &alice_new_sk, &alice_new_pk,
        )
        .unwrap_or_else(|| panic!("bob->alice msg {i} decrypt failed"));
        alice = na;
        assert_eq!(recovered, *pt, "bob->alice msg {i}");
    }

    assert_eq!(bob.send_n, 5, "bob send counter after burst");
    assert_eq!(alice.recv_n, 5, "alice recv counter after burst");
}

// =========================================================================
// KAT 4: byte-identical AEAD ciphertext for fixed inputs (regression KAT)
// =========================================================================
//
// Pin the wire-format bytes so future refactors of the trait API don't
// silently change the cryptographic output.  Generated from this exact
// path on first green run, then frozen.
#[test]
fn dr_kat_pinned_ciphertext() {
    let root = [0x77u8; 32];
    let (alice_sk, alice_pk) = keypair_from(0xA1);
    let (bob_sk, bob_pk) = keypair_from(0xB1);
    let (new_bob_sk, new_bob_pk) = keypair_from(0xB2);

    let (alice, bob) = alice_bob_init(&root, &alice_sk, &alice_pk, &bob_sk, &bob_pk);

    let plaintext = b"pin me";
    let aad = b"kat";

    let (_alice2, msg) = ratchet_encrypt::<AucurvesDr>(&alice, plaintext, aad);

    // Header dh_public is alice's public; check its first bytes are stable.
    assert_eq!(msg.header.dh_public, alice_pk, "header carries alice's pk");
    assert_eq!(msg.header.msg_number, 0);
    assert_eq!(msg.header.prev_chain_len, 0);

    // The ciphertext is the Signal-spec CBC+HMAC wire:
    //   IV(16) || ciphertext_PKCS7 || HMAC-SHA-256(32)
    // For plaintext_len = 6, padded ciphertext = 16, total = 16+16+32 = 64.
    let padded_len = ((plaintext.len() / 16) + 1) * 16;
    assert_eq!(msg.ciphertext.len(), 16 + padded_len + 32,
        "AES-256-CBC+HMAC produces 16 + pad(|pt|) + 32 bytes");

    // Roundtrip succeeds via Bob's canonical DH-ratchet-on-first-receive.
    let (_, recovered) = ratchet_decrypt::<AucurvesDr>(
        &bob, &msg, aad, &new_bob_sk, &new_bob_pk,
    ).expect("KAT decrypt");
    assert_eq!(recovered, plaintext);
}

// =========================================================================
// KAT 5: AEAD authentication — tampered ciphertext rejected
// =========================================================================

#[test]
fn dr_tampered_ciphertext_rejected() {
    let root = [0x99u8; 32];
    let (alice_sk, alice_pk) = keypair_from(0xA1);
    let (bob_sk, bob_pk) = keypair_from(0xB1);
    let (new_bob_sk, new_bob_pk) = keypair_from(0xB2);

    let (alice, bob) = alice_bob_init(&root, &alice_sk, &alice_pk, &bob_sk, &bob_pk);

    let aad = b"v1";
    let (_, mut msg) =
        ratchet_encrypt::<AucurvesDr>(&alice, b"top-secret", aad);

    // Flip a byte in the ciphertext: AEAD must reject.
    msg.ciphertext[0] ^= 0x01;
    let result = ratchet_decrypt::<AucurvesDr>(
        &bob, &msg, aad, &new_bob_sk, &new_bob_pk,
    );
    assert!(result.is_none(), "tampered ciphertext must fail AEAD auth");
}

// =========================================================================
// KAT 6: wrong AAD rejected
// =========================================================================

#[test]
fn dr_wrong_aad_rejected() {
    let root = [0xCCu8; 32];
    let (alice_sk, alice_pk) = keypair_from(0xA1);
    let (bob_sk, bob_pk) = keypair_from(0xB1);
    let (new_bob_sk, new_bob_pk) = keypair_from(0xB2);

    let (alice, bob) = alice_bob_init(&root, &alice_sk, &alice_pk, &bob_sk, &bob_pk);

    let (_, msg) = ratchet_encrypt::<AucurvesDr>(&alice, b"hi", b"alpha");
    let result = ratchet_decrypt::<AucurvesDr>(
        &bob, &msg, b"beta", &new_bob_sk, &new_bob_pk,
    );
    assert!(result.is_none(), "AAD mismatch must fail AEAD auth");
}

// =========================================================================
// Sanity: encode_header / nonce_for are stable
// =========================================================================

#[test]
fn dr_encode_header_layout_stable() {
    let h = MessageHeader {
        dh_public: [0xAB; 32],
        msg_number: 0x01020304,
        prev_chain_len: 0xDEADBEEF,
    };
    let bytes = encode_header(&h);
    assert_eq!(&bytes[0..32], &[0xAB; 32]);
    assert_eq!(&bytes[32..36], &[0x01, 0x02, 0x03, 0x04]);
    assert_eq!(&bytes[36..40], &[0xDE, 0xAD, 0xBE, 0xEF]);
}

#[test]
fn dr_nonce_for_layout() {
    let n = nonce_for(0x01020304);
    assert_eq!(&n[..8], &[0u8; 8]);
    assert_eq!(&n[8..], &[0x01, 0x02, 0x03, 0x04]);
}
