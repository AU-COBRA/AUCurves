//! Sender Keys — Signal's group messaging protocol.
//!
//! Symmetric ratchet only (no DH ratchet, no out-of-order recovery
//! beyond the skip cache).  Each group member maintains a sending
//! chain; receivers maintain per-sender receiving chains.
//!
//! Reference: <https://signal.org/docs/specifications/sesame/>
//! (Sesame addresses sender-key distribution; the chain itself is
//! a straight Signal-style symmetric ratchet.)
//!
//! ## State per sender
//!
//! - `chain_key`: 32-byte symmetric key (advances per message).
//! - `iteration`: u32 counter (next message number).
//! - `signature_key`: per-sender Ed25519 public key (for message
//!   authenticity — group members can verify the sender signed).
//!
//! ## Operations
//!
//! - `derive_message_key(chain_key, iter)`: returns 32-byte MK.
//! - `advance_chain(chain_key)`: returns next chain key.
//! - `encrypt(state, plaintext)`: produces ciphertext + iteration tag.
//! - `decrypt(state, ciphertext, iter)`: ratchet forward, decrypt.

use crate::symmetric::{
    hmac_sha256,
    aes256_cbc_hmac_encrypt_nonce as aead_encrypt_nonce,
    aes256_cbc_hmac_decrypt_nonce as aead_decrypt_nonce,
};

const SK_MSG_KEY_LABEL: &[u8] = b"WhisperGroup-MessageKey";
const SK_CHAIN_LABEL:   &[u8] = b"WhisperGroup-ChainKey";

pub type SenderKey = [u8; 32];

/// Per-sender state (one per group member).
pub struct SenderRatchet {
    /// Current chain key.
    pub chain_key: SenderKey,
    /// Next message iteration number.
    pub iteration: u32,
}

impl SenderRatchet {
    pub fn new(initial_chain_key: SenderKey) -> Self {
        SenderRatchet { chain_key: initial_chain_key, iteration: 0 }
    }

    /// Derive the message key for the current iteration without
    /// advancing the chain.  Caller advances via `advance()`.
    pub fn current_message_key(&self) -> SenderKey {
        hmac_sha256(&self.chain_key, SK_MSG_KEY_LABEL)
    }

    /// Advance the chain by one step.
    pub fn advance(&mut self) {
        self.chain_key = hmac_sha256(&self.chain_key, SK_CHAIN_LABEL);
        self.iteration += 1;
    }

    /// Encrypt a message.  Returns (iteration, ciphertext).
    /// Iteration is the message number (so receiver can ratchet to it).
    pub fn encrypt(&mut self, plaintext: &[u8], aad: &[u8])
        -> Result<(u32, Vec<u8>), ()>
    {
        let mk = self.current_message_key();
        let iter = self.iteration;
        self.advance();
        let mut nonce = [0u8; 12];
        nonce[8..12].copy_from_slice(&iter.to_be_bytes());
        let ct = aead_encrypt_nonce(&mk, &nonce, aad, plaintext)?;
        Ok((iter, ct))
    }

    /// Decrypt a message at iteration `iter`.  Ratchets the chain
    /// forward to that point (advancing past any skipped messages).
    /// In production, skipped message keys would be cached for
    /// out-of-order delivery; this PoC strict-forward-only.
    pub fn decrypt(&mut self, iter: u32, ciphertext: &[u8], aad: &[u8])
        -> Result<Vec<u8>, ()>
    {
        if iter < self.iteration {
            return Err(()); // replay or stale message
        }
        // Ratchet forward to iter.
        while self.iteration < iter {
            self.advance();
        }
        let mk = self.current_message_key();
        let mut nonce = [0u8; 12];
        nonce[8..12].copy_from_slice(&iter.to_be_bytes());
        let pt = aead_decrypt_nonce(&mk, &nonce, aad, ciphertext)?;
        self.advance();
        Ok(pt)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sender_keys_alice_to_group() {
        let initial = [0x42u8; 32];
        let mut alice = SenderRatchet::new(initial);
        let mut bob = SenderRatchet::new(initial); // receiver mirrors sender's chain
        let mut carol = SenderRatchet::new(initial);

        let (it1, ct1) = alice.encrypt(b"hello group", b"v1").unwrap();
        assert_eq!(bob.decrypt(it1, &ct1, b"v1").unwrap(), b"hello group");
        assert_eq!(carol.decrypt(it1, &ct1, b"v1").unwrap(), b"hello group");

        let (it2, ct2) = alice.encrypt(b"second", b"v1").unwrap();
        assert_eq!(bob.decrypt(it2, &ct2, b"v1").unwrap(), b"second");
        assert_eq!(carol.decrypt(it2, &ct2, b"v1").unwrap(), b"second");
    }

    #[test]
    fn sender_keys_replay_rejected() {
        let mut alice = SenderRatchet::new([0x11u8; 32]);
        let mut bob = SenderRatchet::new([0x11u8; 32]);
        let (it1, ct1) = alice.encrypt(b"once", b"v1").unwrap();
        let _ = bob.decrypt(it1, &ct1, b"v1").unwrap();
        // Replay should fail (iter < current).
        let r = bob.decrypt(it1, &ct1, b"v1");
        assert!(r.is_err(), "replay should be rejected");
    }

    #[test]
    fn sender_keys_skip_forward() {
        let mut alice = SenderRatchet::new([0x22u8; 32]);
        let mut bob = SenderRatchet::new([0x22u8; 32]);
        // Alice sends 5; bob receives only the 5th (1-4 dropped).
        let mut ct5 = (0u32, Vec::new());
        for i in 0..5 {
            ct5 = alice.encrypt(format!("m{}", i).as_bytes(), b"v1").unwrap();
        }
        let pt = bob.decrypt(ct5.0, &ct5.1, b"v1").unwrap();
        assert_eq!(pt, b"m4");
    }
}
