//! X3DH session-setup protocol (Track C1 of the Signal end-to-end plan).
//!
//! Composes our verified primitives — X25519 (formosa Jasmin),
//! XEdDSA (Ed25519 over X25519 keys), HKDF-SHA256 (libjade SHA-256
//! + RFC 5869 HKDF) — into Signal's Extended Triple Diffie-Hellman
//! initial key agreement.
//!
//! References:
//!   - Signal Protocol Specification "X3DH":
//!     <https://signal.org/docs/specifications/x3dh/>
//!   - Section 3.3 (Sending the initial message).
//!
//! ## Protocol (Alice initiating to Bob)
//!
//! Bob publishes: IK_b (identity key, X25519 pub), SPK_b (signed
//! prekey, X25519 pub), Sig_b = XEdDSA-sign(IK_b, encode(SPK_b)),
//! OPK_b (one-time prekey, X25519 pub, optional).
//!
//! Alice's side:
//!   1. Verify Sig_b against (IK_b as XEdDSA verify-key, encode(SPK_b)).
//!   2. Generate ephemeral key pair EK_a (priv, pub).
//!   3. Compute the four DH outputs:
//!        DH1 = DH(IK_a_priv, SPK_b_pub)
//!        DH2 = DH(EK_a_priv, IK_b_pub)
//!        DH3 = DH(EK_a_priv, SPK_b_pub)
//!        DH4 = DH(EK_a_priv, OPK_b_pub)   // if OPK present
//!   4. SK = HKDF-SHA256( salt=0, IKM=F||DH1||DH2||DH3||DH4,
//!                       info="X3DH-Signal-25519" )
//!      where F = 0xFF * 32 (Curve25519 prefix per spec §2.5).
//!   5. AD = encode(IK_a_pub) || encode(IK_b_pub).
//!   6. First message to Bob: (IK_a_pub, EK_a_pub, OPK_b_id,
//!                              AEAD(SK, plaintext, AD)).
//!
//! Bob's side: mirror DHs with his private keys.
//!
//! ## What this module provides
//!
//! - `x3dh_initiate_alice`: Alice's side of the agreement.
//! - `x3dh_respond_bob`: Bob's side (compute matching SK).
//!
//! The first message format (and the AEAD step) is the
//! application layer's responsibility; this module computes the
//! shared 32-byte secret only.

use crate::x25519_jasmin;
use crate::symmetric::hkdf_sha256;
// Signal-spec-compliant X3DH: SPK signature uses XEdDSA (Bob's X25519
// identity key doubles as XEdDSA signing key).
use crate::xeddsa::xeddsa_verify;

/// Curve25519 prefix per X3DH spec §2.5 ("X3DH uses F=0xFF...0xFF
/// (32 bytes)").
const X3DH_PREFIX: [u8; 32] = [0xffu8; 32];

const X3DH_INFO: &[u8] = b"X3DH-Signal-25519";

/// Alice's side of X3DH.
///
/// Returns Ok(shared_secret) on success, or Err(()) if the
/// signed-prekey signature fails to verify.
///
/// `ek_a_priv` is Alice's freshly-generated ephemeral key, passed
/// in by the caller (RNG is outside this module).
///
/// `opk_b_pub` is `None` if Bob didn't publish a one-time prekey.
#[allow(clippy::too_many_arguments)]
pub fn x3dh_initiate_alice(
    ik_a_priv: &[u8; 32],
    ek_a_priv: &[u8; 32],
    ik_b_pub: &[u8; 32],
    spk_b_pub: &[u8; 32],
    spk_b_sig: &[u8; 64],
    opk_b_pub: Option<&[u8; 32]>,
) -> Result<[u8; 32], ()> {
    // 1. Verify the signed prekey.  Signal-spec-compliant: XEdDSA
    //    verify with Bob's X25519 identity key (which doubles as
    //    XEdDSA signing key).  No separate Ed25519 keypair needed.
    if !xeddsa_verify(ik_b_pub, spk_b_pub, spk_b_sig) {
        return Err(());
    }

    // 2-3. Four DH operations.
    let dh1 = x25519_jasmin(ik_a_priv, spk_b_pub);
    let dh2 = x25519_jasmin(ek_a_priv, ik_b_pub);
    let dh3 = x25519_jasmin(ek_a_priv, spk_b_pub);
    let dh4_opt: Option<[u8; 32]> = opk_b_pub.map(|p| x25519_jasmin(ek_a_priv, p));

    // 4. HKDF over F || DH1 || DH2 || DH3 || [DH4].
    let mut ikm: Vec<u8> = Vec::with_capacity(32 * 5);
    ikm.extend_from_slice(&X3DH_PREFIX);
    ikm.extend_from_slice(&dh1);
    ikm.extend_from_slice(&dh2);
    ikm.extend_from_slice(&dh3);
    if let Some(dh4) = dh4_opt {
        ikm.extend_from_slice(&dh4);
    }

    let mut sk = [0u8; 32];
    hkdf_sha256(None, &ikm, X3DH_INFO, &mut sk);
    Ok(sk)
}

/// Bob's side of X3DH.
///
/// Bob already published IK_b, SPK_b, OPK_b; he holds the
/// corresponding private keys.  When Alice's first message arrives
/// containing (IK_a_pub, EK_a_pub, OPK_b_id), Bob computes the
/// same shared secret with mirrored DHs.
///
/// If Alice didn't use an OPK (because Bob's pool was exhausted),
/// pass `opk_b_priv = None`.
#[allow(clippy::too_many_arguments)]
pub fn x3dh_respond_bob(
    ik_b_priv: &[u8; 32],
    spk_b_priv: &[u8; 32],
    opk_b_priv: Option<&[u8; 32]>,
    ik_a_pub: &[u8; 32],
    ek_a_pub: &[u8; 32],
) -> [u8; 32] {
    // Mirror DHs.  DH(a, b·G) = DH(b, a·G) by commutativity.
    let dh1 = x25519_jasmin(spk_b_priv, ik_a_pub);    // mirrors DH(IK_a, SPK_b)
    let dh2 = x25519_jasmin(ik_b_priv,  ek_a_pub);    // mirrors DH(EK_a, IK_b)
    let dh3 = x25519_jasmin(spk_b_priv, ek_a_pub);    // mirrors DH(EK_a, SPK_b)
    let dh4_opt: Option<[u8; 32]> = opk_b_priv.map(|p| x25519_jasmin(p, ek_a_pub));

    let mut ikm: Vec<u8> = Vec::with_capacity(32 * 5);
    ikm.extend_from_slice(&X3DH_PREFIX);
    ikm.extend_from_slice(&dh1);
    ikm.extend_from_slice(&dh2);
    ikm.extend_from_slice(&dh3);
    if let Some(dh4) = dh4_opt {
        ikm.extend_from_slice(&dh4);
    }

    let mut sk = [0u8; 32];
    hkdf_sha256(None, &ikm, X3DH_INFO, &mut sk);
    sk
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::xeddsa::xeddsa_sign;
    // Tests derive pubkeys from privkeys; non-test X3DH path doesn't.
    use crate::x25519_jasmin_base;

    /// Self-consistency check: Alice and Bob compute the same shared
    /// secret when running the protocol.  Uses pseudo-random keys
    /// (NOT cryptographic randomness — for KAT only).
    #[test]
    fn x3dh_self_consistency_with_opk() {
        let ik_a_priv = [0x01u8; 32];
        let ik_b_priv = [0x02u8; 32];
        let spk_b_priv = [0x03u8; 32];
        let opk_b_priv = [0x04u8; 32];
        let ek_a_priv = [0x05u8; 32];

        let ik_a_pub = x25519_jasmin_base(&ik_a_priv);
        let ik_b_pub = x25519_jasmin_base(&ik_b_priv);
        let spk_b_pub = x25519_jasmin_base(&spk_b_priv);
        let opk_b_pub = x25519_jasmin_base(&opk_b_priv);
        let ek_a_pub = x25519_jasmin_base(&ek_a_priv);

        // Signal-spec X3DH: Bob signs SPK with XEdDSA over his X25519
        // identity key (no separate Ed25519 keypair).
        let spk_sig_random = [0x07u8; 64];
        let spk_sig = xeddsa_sign(&ik_b_priv, &spk_b_pub, &spk_sig_random);

        // Alice's side.
        let sk_a = x3dh_initiate_alice(
            &ik_a_priv, &ek_a_priv,
            &ik_b_pub, &spk_b_pub, &spk_sig,
            Some(&opk_b_pub),
        )
        .expect("signed-prekey verify");

        // Bob's side.
        let sk_b = x3dh_respond_bob(
            &ik_b_priv, &spk_b_priv,
            Some(&opk_b_priv),
            &ik_a_pub, &ek_a_pub,
        );

        assert_eq!(sk_a, sk_b, "Alice and Bob compute different shared secrets");
    }

    #[test]
    fn x3dh_self_consistency_without_opk() {
        let ik_a_priv = [0x11u8; 32];
        let ik_b_priv = [0x21u8; 32];
        let spk_b_priv = [0x23u8; 32];
        let ek_a_priv = [0x25u8; 32];

        let ik_a_pub = x25519_jasmin_base(&ik_a_priv);
        let ik_b_pub = x25519_jasmin_base(&ik_b_priv);
        let spk_b_pub = x25519_jasmin_base(&spk_b_priv);
        let ek_a_pub = x25519_jasmin_base(&ek_a_priv);

        let spk_sig_random = [0x17u8; 64];
        let spk_sig = xeddsa_sign(&ik_b_priv, &spk_b_pub, &spk_sig_random);

        let sk_a = x3dh_initiate_alice(
            &ik_a_priv, &ek_a_priv,
            &ik_b_pub, &spk_b_pub, &spk_sig, None,
        )
        .expect("signed-prekey verify");

        let sk_b = x3dh_respond_bob(
            &ik_b_priv, &spk_b_priv, None,
            &ik_a_pub, &ek_a_pub,
        );

        assert_eq!(sk_a, sk_b);
    }

    #[test]
    fn x3dh_rejects_bad_signed_prekey_sig() {
        let ik_a_priv = [0x31u8; 32];
        let ik_b_priv = [0x32u8; 32];
        let spk_b_priv = [0x33u8; 32];
        let ek_a_priv = [0x35u8; 32];

        let ik_b_pub = x25519_jasmin_base(&ik_b_priv);
        let spk_b_pub = x25519_jasmin_base(&spk_b_priv);

        let spk_sig = [0u8; 64];

        let result = x3dh_initiate_alice(
            &ik_a_priv, &ek_a_priv,
            &ik_b_pub, &spk_b_pub, &spk_sig, None,
        );
        assert!(result.is_err(), "X3DH should reject bogus SPK sig");
    }
}
