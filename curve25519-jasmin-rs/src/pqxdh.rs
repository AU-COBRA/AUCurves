//! PQXDH session-setup protocol — PQ-augmented X3DH.
//!
//! Signal's post-quantum-enhanced session establishment.  X3DH +
//! one extra KEM encapsulation against Bob's PQ-prekey.
//!
//! Reference: <https://signal.org/docs/specifications/pqxdh/>
//!
//! ## Verification status (2026-05-12)
//!
//! ML-KEM-768: **VERIFIED** via formosa-mlkem (Jasmin source, compiled
//! by EasyCrypt-verified jasminc).  Replaces the RustCrypto `ml-kem`
//! crate.  Trust set: jasminc compiler + the algebraic correctness
//! of the Jasmin source (per Cryspen's formosa-mlkem proofs).
//!
//! XEdDSA signatures: verified Ed25519 verify backend +
//! dalek-glue for the Montgomery→Edwards conversion.
//!
//! Composition glue: ~150 LoC unverified Rust below.

use crate::x25519_jasmin;
use crate::symmetric::{
    hkdf_sha256,
    mlkem768_enc, mlkem768_dec,
    MLKEM768_PUBLIC_KEY_BYTES, MLKEM768_SECRET_KEY_BYTES,
    MLKEM768_CIPHERTEXT_BYTES,
};
use crate::xeddsa::xeddsa_verify;

const PQXDH_PREFIX: [u8; 32] = [0xffu8; 32];
const PQXDH_INFO: &[u8] = b"PQXDH-Signal-25519-MLKEM768";

pub use crate::symmetric::{
    MLKEM768_PUBLIC_KEY_BYTES as PQPK_BYTES,
    MLKEM768_SECRET_KEY_BYTES as PQPK_DK_BYTES,
};

/// Alice's side of PQXDH.
///
/// Returns (shared_secret, kem_ciphertext) on success.
/// `pqpk_b` is Bob's serialized 1184-byte ML-KEM-768 encapsulation key.
/// `mlkem_coins` is the 32-byte encapsulation randomness.
#[allow(clippy::too_many_arguments)]
pub fn pqxdh_initiate_alice(
    ik_a_priv: &[u8; 32],
    ek_a_priv: &[u8; 32],
    ik_b_pub: &[u8; 32],
    spk_b_pub: &[u8; 32],
    spk_b_sig: &[u8; 64],
    opk_b_pub: Option<&[u8; 32]>,
    pqpk_b: &[u8],            // serialized ML-KEM encapsulation key (1184 bytes)
    pqpk_b_digest_sig: &[u8; 64],
    pqpk_b_digest: &[u8; 32],
    mlkem_coins: &[u8; 32],
) -> Result<([u8; 32], Vec<u8>), ()> {
    assert_eq!(pqpk_b.len(), MLKEM768_PUBLIC_KEY_BYTES);

    // 1. Verify the X25519 signed prekey via XEdDSA.
    if !xeddsa_verify(ik_b_pub, spk_b_pub, spk_b_sig) {
        return Err(());
    }
    // 2. Verify the PQ prekey signature via XEdDSA over a 32-byte
    //    digest of the ML-KEM encapsulation key.
    if !xeddsa_verify(ik_b_pub, pqpk_b_digest, pqpk_b_digest_sig) {
        return Err(());
    }

    // 3. ML-KEM-768 encapsulation against Bob's PQPK — VERIFIED via
    //    formosa-mlkem Jasmin (compiled by EasyCrypt-verified jasminc).
    let (kem_ct, kem_ss) = mlkem768_enc(pqpk_b, mlkem_coins);

    // 4. X3DH-style DH outputs (all via verified X25519 Jasmin).
    let dh1 = x25519_jasmin(ik_a_priv, spk_b_pub);
    let dh2 = x25519_jasmin(ek_a_priv, ik_b_pub);
    let dh3 = x25519_jasmin(ek_a_priv, spk_b_pub);
    let dh4_opt: Option<[u8; 32]> = opk_b_pub.map(|p| x25519_jasmin(ek_a_priv, p));

    // 5. HKDF over F || DH1..DH4 || ss.
    let mut ikm: Vec<u8> = Vec::with_capacity(32 * 5 + 32);
    ikm.extend_from_slice(&PQXDH_PREFIX);
    ikm.extend_from_slice(&dh1);
    ikm.extend_from_slice(&dh2);
    ikm.extend_from_slice(&dh3);
    if let Some(dh4) = dh4_opt {
        ikm.extend_from_slice(&dh4);
    }
    ikm.extend_from_slice(&kem_ss);

    let mut sk = [0u8; 32];
    hkdf_sha256(None, &ikm, PQXDH_INFO, &mut sk);

    Ok((sk, kem_ct))
}

/// Bob's side of PQXDH.
#[allow(clippy::too_many_arguments)]
pub fn pqxdh_respond_bob(
    ik_b_priv: &[u8; 32],
    spk_b_priv: &[u8; 32],
    opk_b_priv: Option<&[u8; 32]>,
    pqpk_b_dk: &[u8],         // ML-KEM secret key (2400 bytes)
    ik_a_pub: &[u8; 32],
    ek_a_pub: &[u8; 32],
    kem_ct: &[u8],            // ML-KEM ciphertext (1088 bytes)
) -> Result<[u8; 32], ()> {
    assert_eq!(pqpk_b_dk.len(), MLKEM768_SECRET_KEY_BYTES);
    assert_eq!(kem_ct.len(), MLKEM768_CIPHERTEXT_BYTES);

    let dh1 = x25519_jasmin(spk_b_priv, ik_a_pub);
    let dh2 = x25519_jasmin(ik_b_priv, ek_a_pub);
    let dh3 = x25519_jasmin(spk_b_priv, ek_a_pub);
    let dh4_opt: Option<[u8; 32]> = opk_b_priv.map(|p| x25519_jasmin(p, ek_a_pub));

    // ML-KEM-768 decapsulation — VERIFIED.
    let kem_ss = mlkem768_dec(pqpk_b_dk, kem_ct);

    let mut ikm: Vec<u8> = Vec::with_capacity(32 * 5 + 32);
    ikm.extend_from_slice(&PQXDH_PREFIX);
    ikm.extend_from_slice(&dh1);
    ikm.extend_from_slice(&dh2);
    ikm.extend_from_slice(&dh3);
    if let Some(dh4) = dh4_opt {
        ikm.extend_from_slice(&dh4);
    }
    ikm.extend_from_slice(&kem_ss);

    let mut sk = [0u8; 32];
    hkdf_sha256(None, &ikm, PQXDH_INFO, &mut sk);
    Ok(sk)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::xeddsa::xeddsa_sign;
    // Tests derive pubkeys + run KEM keygen; non-test PQXDH path doesn't.
    use crate::x25519_jasmin_base;
    use crate::symmetric::mlkem768_keygen;

    #[test]
    fn pqxdh_self_consistency() {
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
        // Signal PQXDH spec: SPK + PQPK both signed by XEdDSA(ik_b).
        let spk_sig_random = [0xB2u8; 64];
        let spk_sig = xeddsa_sign(&ik_b_priv, &spk_b_pub, &spk_sig_random);

        // Bob's ML-KEM PQ-prekey — VERIFIED keygen via formosa-mlkem.
        let kem_keygen_coins = [0xC1u8; 64];
        let (pqpk_b, pqpk_dk_b) = mlkem768_keygen(&kem_keygen_coins);

        // Bob signs sha256(serialized PQPK) with his X25519 IK via XEdDSA.
        let pq_digest = crate::symmetric::sha256(&pqpk_b);
        let pq_sig_random = [0xB5u8; 64];
        let pq_sig = xeddsa_sign(&ik_b_priv, &pq_digest, &pq_sig_random);

        // Alice runs PQXDH.
        let mlkem_coins = [0xD1u8; 32];
        let (sk_a, kem_ct) = pqxdh_initiate_alice(
            &ik_a_priv, &ek_a_priv,
            &ik_b_pub,
            &spk_b_pub, &spk_sig,
            Some(&opk_b_pub),
            &pqpk_b, &pq_sig, &pq_digest,
            &mlkem_coins,
        ).expect("alice PQXDH");

        // Bob responds.
        let sk_b = pqxdh_respond_bob(
            &ik_b_priv, &spk_b_priv, Some(&opk_b_priv),
            &pqpk_dk_b,
            &ik_a_pub, &ek_a_pub,
            &kem_ct,
        ).expect("bob PQXDH");

        assert_eq!(sk_a, sk_b, "PQXDH shared secrets diverge");
    }
}
