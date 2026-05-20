//! Double Ratchet message protocol — Signal's Double Ratchet
//! algorithm wired end-to-end on our verified primitive backends.
//!
//! Reference: <https://signal.org/docs/specifications/doubleratchet/>
//!
//! ## What this demonstrates
//!
//! A working Double Ratchet using:
//!   - X25519 (formosa-25519 Jasmin, ~26 µs per DH)         — Rocq-verified
//!   - HKDF-SHA256 (libjade SHA-256 + RFC 5869 over HMAC)  — verified hash + Rust composition
//!   - HMAC-SHA256 (libjade SHA-256 + RFC 2104 composition) — verified hash + Rust composition
//!   - AES-256-CBC + HMAC-SHA-256 (libcrux-lean-specs pure-Rust AES + safe-Rust CBC + libjade HMAC) — Signal-spec AEAD as of 2026-05-13
//!
//! Composes to:
//!   - Symmetric ratchet (chain → message keys + next chain key)
//!   - DH ratchet (new ephemeral DH pair per direction change)
//!   - Root-key update on each new DH agreement
//!   - Header-encryption-free variant (the "standard" DR, not HE-DR)
//!
//! ## Verification status
//!
//! Functional correctness: this module passes a self-consistency
//! roundtrip test (Alice encrypts a sequence, Bob decrypts in
//! arbitrary order including skips).  Forward secrecy + post-
//! compromise security are PROTOCOL properties verified separately
//! in CatCrypt's `DoubleRatchet_UC.lean` formalization — wiring
//! that proof to this Rust impl is Track F1 work.
//!
//! ## What this is NOT
//!
//! - Not byte-compat with libsignal's wire format (we use a simple
//!   header struct; libsignal uses Protobuf with specific tags).
//! - Not a state-of-the-art skip-cache implementation (we use a
//!   simple `Vec` for skipped keys; production would use bounded
//!   storage).
//! - No header encryption (HE variant); plain headers only.

use crate::{x25519_jasmin, x25519_jasmin_base};
use crate::symmetric::{
    hkdf_sha256, hmac_sha256,
    aes256_cbc_hmac_encrypt_nonce as aead_encrypt_nonce,
    aes256_cbc_hmac_decrypt_nonce as aead_decrypt_nonce,
};

const RK_INFO: &[u8] = b"WhisperRatchet";
const HK_LABEL_MK: &[u8] = b"WhisperMessageKey";
const HK_LABEL_CK: &[u8] = b"WhisperChainKey";

/// 32-byte symmetric key.
pub type Key32 = [u8; 32];

/// Message header: Alice/Bob's current DH public key + counters.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Header {
    /// Sender's current DH ratchet public key.
    pub dh: [u8; 32],
    /// Number of messages in the PREVIOUS sending chain (PN).
    pub pn: u32,
    /// Message number in the CURRENT sending chain (N).
    pub n: u32,
}

impl Header {
    fn encode(&self) -> [u8; 40] {
        let mut buf = [0u8; 40];
        buf[0..32].copy_from_slice(&self.dh);
        buf[32..36].copy_from_slice(&self.pn.to_be_bytes());
        buf[36..40].copy_from_slice(&self.n.to_be_bytes());
        buf
    }
}

/// Double Ratchet session state.
pub struct DrState {
    /// DH ratchet sending key (private).
    dhs_priv: [u8; 32],
    dhs_pub: [u8; 32],
    /// DH ratchet receiving key (peer's public).
    dhr_pub: Option<[u8; 32]>,
    /// Root key.
    rk: Key32,
    /// Sending chain key.
    cks: Option<Key32>,
    /// Receiving chain key.
    ckr: Option<Key32>,
    /// Number of messages in the current sending chain.
    n_send: u32,
    /// Number of messages in the current receiving chain.
    n_recv: u32,
    /// Number of messages in the previous sending chain.
    pn: u32,
    /// Skipped-message keys, indexed by (peer_dh, n).
    skipped: Vec<((Vec<u8>, u32), Key32)>,
}

/// Internal KDF helpers.

/// KDF_RK: root-key update.  Given current root key and a DH
/// output, derive a new (root_key, chain_key).
fn kdf_rk(rk: &Key32, dh_out: &[u8; 32]) -> (Key32, Key32) {
    let mut okm = [0u8; 64];
    hkdf_sha256(Some(rk), dh_out, RK_INFO, &mut okm);
    let mut new_rk = [0u8; 32];
    let mut new_ck = [0u8; 32];
    new_rk.copy_from_slice(&okm[..32]);
    new_ck.copy_from_slice(&okm[32..]);
    (new_rk, new_ck)
}

/// KDF_CK: chain-key step.  Given current chain key, derive a
/// message key and advance the chain key.
fn kdf_ck(ck: &Key32) -> (Key32, Key32) {
    let mk = hmac_sha256(ck, HK_LABEL_MK);
    let new_ck = hmac_sha256(ck, HK_LABEL_CK);
    (mk, new_ck)
}

impl DrState {
    /// Alice's initial state.  `shared_secret` is the X3DH output.
    /// `bob_dh_pub` is Bob's signed prekey (the initial DH receive).
    pub fn init_alice(shared_secret: &Key32, bob_dh_pub: &[u8; 32]) -> Self {
        // Alice generates her first ratchet DH pair from the shared secret.
        // In practice this is fresh randomness; for determinism we derive.
        let mut alice_dh_priv = [0u8; 32];
        hkdf_sha256(Some(shared_secret), b"alice-dh-init", b"DR-init", &mut alice_dh_priv);
        let alice_dh_pub = x25519_jasmin_base(&alice_dh_priv);

        let dh_out = x25519_jasmin(&alice_dh_priv, bob_dh_pub);
        let (rk, cks) = kdf_rk(shared_secret, &dh_out);

        DrState {
            dhs_priv: alice_dh_priv,
            dhs_pub: alice_dh_pub,
            dhr_pub: Some(*bob_dh_pub),
            rk,
            cks: Some(cks),
            ckr: None,
            n_send: 0,
            n_recv: 0,
            pn: 0,
            skipped: Vec::new(),
        }
    }

    /// Bob's initial state.  `shared_secret` is the X3DH output.
    /// `bob_dh_priv` is the X25519 key that matched Alice's first DH.
    pub fn init_bob(shared_secret: &Key32, bob_dh_priv: &[u8; 32]) -> Self {
        let bob_dh_pub = x25519_jasmin_base(bob_dh_priv);
        DrState {
            dhs_priv: *bob_dh_priv,
            dhs_pub: bob_dh_pub,
            dhr_pub: None,
            rk: *shared_secret,
            cks: None,
            ckr: None,
            n_send: 0,
            n_recv: 0,
            pn: 0,
            skipped: Vec::new(),
        }
    }

    /// Encrypt a message.  Advances Alice's sending chain.
    pub fn encrypt(&mut self, plaintext: &[u8], aad: &[u8])
        -> Result<(Header, Vec<u8>), ()>
    {
        let cks = self.cks.as_ref().ok_or(())?;
        let (mk, new_cks) = kdf_ck(cks);
        self.cks = Some(new_cks);

        let header = Header {
            dh: self.dhs_pub,
            pn: self.pn,
            n: self.n_send,
        };
        self.n_send += 1;

        // AEAD nonce: 12 bytes derived from message number.
        let mut nonce = [0u8; 12];
        nonce[8..12].copy_from_slice(&header.n.to_be_bytes());
        // AEAD AAD = caller AAD || header encoding.
        let header_bytes = header.encode();
        let mut full_aad = Vec::with_capacity(aad.len() + 40);
        full_aad.extend_from_slice(aad);
        full_aad.extend_from_slice(&header_bytes);

        let ct = aead_encrypt_nonce(&mk, &nonce, &full_aad, plaintext)?;
        Ok((header, ct))
    }

    /// Decrypt a message.  May trigger a DH ratchet step if the
    /// incoming header has a new peer DH public key.
    pub fn decrypt(&mut self, header: &Header, ciphertext: &[u8], aad: &[u8])
        -> Result<Vec<u8>, ()>
    {
        // 1. Check for a stored skipped message key.
        if let Some(idx) = self.skipped.iter().position(|((dh, n), _)| {
            dh.as_slice() == &header.dh[..] && *n == header.n
        }) {
            let ((_dh, _n), mk) = self.skipped.remove(idx);
            return decrypt_with_mk(&mk, header, ciphertext, aad);
        }

        // 2. New DH ratchet step?
        if self.dhr_pub.as_ref().map_or(true, |dhr| dhr != &header.dh) {
            self.dh_ratchet(header)?;
        }

        // 3. Skip messages in the current receiving chain.
        self.skip_message_keys(header.n)?;

        // 4. Advance the receiving chain by one.
        let ckr = self.ckr.as_ref().ok_or(())?;
        let (mk, new_ckr) = kdf_ck(ckr);
        self.ckr = Some(new_ckr);
        self.n_recv += 1;
        decrypt_with_mk(&mk, header, ciphertext, aad)
    }

    /// Perform a DH ratchet step: incorporate the peer's new DH pub
    /// key, generate our new pair, update root + chain keys.
    fn dh_ratchet(&mut self, header: &Header) -> Result<(), ()> {
        // Skip ahead in the OLD receiving chain to header.pn.
        if self.ckr.is_some() {
            self.skip_message_keys(header.pn)?;
        }
        self.pn = self.n_send;
        self.n_send = 0;
        self.n_recv = 0;

        // Adopt peer's new DH pub.
        self.dhr_pub = Some(header.dh);

        // DH ratchet step 1: derive new (rk, ckr) from incoming DH.
        let dh_out_recv = x25519_jasmin(&self.dhs_priv, &header.dh);
        let (rk1, ckr) = kdf_rk(&self.rk, &dh_out_recv);
        self.rk = rk1;
        self.ckr = Some(ckr);

        // Generate our new DH pair.  Derive from RK for determinism in
        // this PoC (production uses fresh randomness).
        let mut new_priv = [0u8; 32];
        hkdf_sha256(Some(&self.rk), b"dh-ratchet-new-priv", b"DR-DH", &mut new_priv);
        self.dhs_priv = new_priv;
        self.dhs_pub = x25519_jasmin_base(&new_priv);

        // DH ratchet step 2: derive new (rk, cks) from outgoing DH.
        let dh_out_send = x25519_jasmin(&self.dhs_priv, &header.dh);
        let (rk2, cks) = kdf_rk(&self.rk, &dh_out_send);
        self.rk = rk2;
        self.cks = Some(cks);
        Ok(())
    }

    /// Skip message keys in the current receiving chain up to `until`.
    fn skip_message_keys(&mut self, until: u32) -> Result<(), ()> {
        if self.ckr.is_none() { return Ok(()); }
        let dhr = self.dhr_pub.ok_or(())?;
        while self.n_recv < until {
            let ckr = self.ckr.as_ref().ok_or(())?;
            let (mk, new_ckr) = kdf_ck(ckr);
            self.skipped.push(((dhr.to_vec(), self.n_recv), mk));
            self.ckr = Some(new_ckr);
            self.n_recv += 1;
        }
        Ok(())
    }
}

fn decrypt_with_mk(mk: &Key32, header: &Header, ciphertext: &[u8], aad: &[u8])
    -> Result<Vec<u8>, ()>
{
    let mut nonce = [0u8; 12];
    nonce[8..12].copy_from_slice(&header.n.to_be_bytes());
    let header_bytes = header.encode();
    let mut full_aad = Vec::with_capacity(aad.len() + 40);
    full_aad.extend_from_slice(aad);
    full_aad.extend_from_slice(&header_bytes);
    aead_decrypt_nonce(mk, &nonce, &full_aad, ciphertext)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::x3dh::{x3dh_initiate_alice, x3dh_respond_bob};
    use crate::xeddsa::xeddsa_sign;

    fn alice_bob_via_x3dh() -> (DrState, DrState, [u8; 32]) {
        // Run X3DH to get a shared secret.  Signal-spec X3DH uses
        // XEdDSA for the SPK signature (Bob's X25519 identity key
        // doubles as XEdDSA signing key — no separate Ed25519 key).
        let ik_a_priv = [0xA1u8; 32];
        let ik_b_priv = [0xB1u8; 32];
        let spk_b_priv = [0xB3u8; 32];
        let opk_b_priv = [0xB4u8; 32];
        let ek_a_priv = [0xA5u8; 32];

        let ik_a_pub = x25519_jasmin_base(&ik_a_priv);
        let ik_b_pub = x25519_jasmin_base(&ik_b_priv);
        let spk_b_pub = x25519_jasmin_base(&spk_b_priv);
        let opk_b_pub = x25519_jasmin_base(&opk_b_priv);
        let ek_a_pub = x25519_jasmin_base(&ek_a_priv);
        let spk_sig_random = [0xB2u8; 64];
        let spk_sig = xeddsa_sign(&ik_b_priv, &spk_b_pub, &spk_sig_random);

        let sk_a = x3dh_initiate_alice(
            &ik_a_priv, &ek_a_priv, &ik_b_pub,
            &spk_b_pub, &spk_sig, Some(&opk_b_pub),
        ).expect("X3DH init");
        let sk_b = x3dh_respond_bob(
            &ik_b_priv, &spk_b_priv, Some(&opk_b_priv),
            &ik_a_pub, &ek_a_pub,
        );
        assert_eq!(sk_a, sk_b);

        // Bob's signed prekey becomes Alice's initial DR receive key.
        let alice = DrState::init_alice(&sk_a, &spk_b_pub);
        let bob = DrState::init_bob(&sk_b, &spk_b_priv);
        (alice, bob, sk_a)
    }

    #[test]
    fn dr_alice_to_bob_single_message() {
        let (mut alice, mut bob, _) = alice_bob_via_x3dh();
        let (header, ct) = alice.encrypt(b"hi bob", b"v1").unwrap();
        let pt = bob.decrypt(&header, &ct, b"v1").unwrap();
        assert_eq!(pt, b"hi bob");
    }

    #[test]
    fn dr_alice_to_bob_burst() {
        let (mut alice, mut bob, _) = alice_bob_via_x3dh();
        for i in 0..5 {
            let msg = format!("msg-{}", i);
            let (header, ct) = alice.encrypt(msg.as_bytes(), b"v1").unwrap();
            let pt = bob.decrypt(&header, &ct, b"v1").unwrap();
            assert_eq!(pt, msg.as_bytes());
        }
    }

    #[test]
    fn dr_bidirectional_with_dh_ratchet() {
        // Alice sends, Bob receives.
        // Bob sends, Alice receives — DH ratchet triggered (peer DH changes).
        let (mut alice, mut bob, _) = alice_bob_via_x3dh();

        // Alice → Bob
        let (h1, c1) = alice.encrypt(b"alice-msg-1", b"v1").unwrap();
        assert_eq!(bob.decrypt(&h1, &c1, b"v1").unwrap(), b"alice-msg-1");

        // Bob → Alice (triggers DH ratchet on Alice's side when she receives)
        let (h2, c2) = bob.encrypt(b"bob-msg-1", b"v1").unwrap();
        assert_eq!(alice.decrypt(&h2, &c2, b"v1").unwrap(), b"bob-msg-1");

        // Alice → Bob again (new DH ratchet on Bob's side)
        let (h3, c3) = alice.encrypt(b"alice-msg-2", b"v1").unwrap();
        assert_eq!(bob.decrypt(&h3, &c3, b"v1").unwrap(), b"alice-msg-2");
    }

    #[test]
    fn dr_out_of_order_with_skip() {
        let (mut alice, mut bob, _) = alice_bob_via_x3dh();
        // Alice sends 3 messages.
        let (h1, c1) = alice.encrypt(b"m1", b"v1").unwrap();
        let (h2, c2) = alice.encrypt(b"m2", b"v1").unwrap();
        let (h3, c3) = alice.encrypt(b"m3", b"v1").unwrap();
        // Bob receives m3 first (m1, m2 in flight).
        assert_eq!(bob.decrypt(&h3, &c3, b"v1").unwrap(), b"m3");
        // Then m1.
        assert_eq!(bob.decrypt(&h1, &c1, b"v1").unwrap(), b"m1");
        // Then m2.
        assert_eq!(bob.decrypt(&h2, &c2, b"v1").unwrap(), b"m2");
    }

    #[test]
    fn dr_aad_mismatch_rejects() {
        let (mut alice, mut bob, _) = alice_bob_via_x3dh();
        let (header, ct) = alice.encrypt(b"hi bob", b"v1").unwrap();
        // Wrong AAD on decrypt.
        let r = bob.decrypt(&header, &ct, b"v2");
        assert!(r.is_err(), "AAD mismatch should fail authentication");
    }
}
