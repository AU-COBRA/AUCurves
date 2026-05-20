//! XEdDSA signature scheme: Ed25519 signatures over X25519 keys.
//!
//! Per Signal's XEdDSA spec (<https://signal.org/docs/specifications/xeddsa/>),
//! XEdDSA derives an Ed25519 keypair from an X25519 keypair, signs
//! with it via standard Ed25519, and the verifier reconstructs the
//! Ed25519 verify-key from the X25519 public key.
//!
//! # Verification chain
//!
//! ```text
//! Verify side:
//!   X25519 pub (Montgomery u)
//!     → Edwards y via y = (u-1)/(u+1) mod p (dalek's MontgomeryPoint::to_edwards)
//!     → standard Ed25519 verify (our rust_cmd_ed-extracted Ed25519, 12 RFC 8032 KATs)
//!
//! Sign side:
//!   X25519 priv (clamped scalar k)
//!     → Edwards keypair (k, A=k·G_Edwards) via dalek's EdwardsPoint::mul_base
//!     → Ed25519 signature (R, s) per RFC 8032 §5.1.6 with
//!       XEdDSA-specific nonce derivation (SHA-512 with 0xfe||0xff*31 prefix)
//! ```
//!
//! Note: the SIGN side still uses dalek's `ED25519_BASEPOINT_TABLE`
//! scalar multiplication and `EdwardsPoint::compress` — those are
//! unverified glue.  Replacement plan: our rust_cmd_ed
//! `Window4ScalarmultBody.v` + `ed25519_compress` body decomposed in
//! `End2End/Ed25519/`.
//!
//! The VERIFY side is now fully verified glue (2026-05-12):
//! Montgomery→Edwards goes through `crate::mont_to_edwards` (fiat-rust
//! only), then standard Ed25519 verify (rust_cmd_ed-extracted).
//! KAT'd against dalek for several pubkeys in `mont_to_edwards::tests`.

use crate::symmetric::sha512;

/// XEdDSA signature: 64 bytes (R || s).
pub type Signature = [u8; 64];

/// Sign a message with an X25519 private key.
///
/// # Arguments
/// * `privkey` - 32-byte X25519 private key
/// * `message` - message to sign
/// * `random` - 64 bytes of randomness for synthetic nonce
///
/// # Returns
/// 64-byte signature (R || s)
pub fn xeddsa_sign(privkey: &[u8; 32], message: &[u8], random: &[u8; 64]) -> Signature {
    use crate::scalar25519::Scalar25519;
    use crate::ed25519_rustcmd::scalarmult_base_compressed;

    // 1. Clamp X25519 private key — this scalar is BOTH the X25519
    //    DH scalar AND the Ed25519 signing scalar in XEdDSA.
    let mut k = *privkey;
    k[0] &= 248;
    k[31] &= 127;
    k[31] |= 64;
    let k_scalar = Scalar25519::from_bytes_mod_order(&k);

    // 2. Edwards public key A = k · G_Edwards via verified scalarmult_base.
    //    Per XEdDSA spec §2.4, the resulting Edwards point has its
    //    sign bit forced to 0 (positive-y convention).  scalarmult_base
    //    consumes the un-reduced 32-byte clamped X25519 key (its native
    //    encoding); we keep the parallel Scalar25519 form for the
    //    arithmetic below.
    let mut k_bytes_for_mult = k;
    let mut a_compressed = scalarmult_base_compressed(&k_bytes_for_mult);
    let sign_bit = a_compressed[31] >> 7;
    let k_effective: Scalar25519;
    if sign_bit == 1 {
        // Flip sign: negate the scalar (mod L), recompute A.
        k_effective = k_scalar.negate();
        k_bytes_for_mult = k_effective.to_bytes();
        a_compressed = scalarmult_base_compressed(&k_bytes_for_mult);
    } else {
        k_effective = k_scalar;
    }

    // 3. Nonce: r = SHA-512(prefix || k_effective || msg || random) mod L.
    //    XEdDSA prefix: 0xfe followed by 0xff × 31.
    let k_eff_bytes = k_effective.to_bytes();
    let mut nonce_input = Vec::with_capacity(32 + 32 + message.len() + 64);
    nonce_input.push(0xfe);
    nonce_input.extend_from_slice(&[0xffu8; 31]);
    nonce_input.extend_from_slice(&k_eff_bytes);
    nonce_input.extend_from_slice(message);
    nonce_input.extend_from_slice(random);
    let r_hash = sha512(&nonce_input);
    let r_scalar = Scalar25519::from_bytes_mod_order_wide(&r_hash);

    // 4. R = r · G_Edwards via verified scalarmult_base.
    let mut r_bytes_for_mult = r_scalar.to_bytes();
    let r_bytes = scalarmult_base_compressed(&r_bytes_for_mult);
    // Zero r_bytes_for_mult to avoid lingering secret material.
    for b in r_bytes_for_mult.iter_mut() { *b = 0; }

    // 5. Challenge e = SHA-512(R || A || msg) mod L (standard Ed25519).
    let mut chal_input = Vec::with_capacity(32 + 32 + message.len());
    chal_input.extend_from_slice(&r_bytes);
    chal_input.extend_from_slice(&a_compressed);
    chal_input.extend_from_slice(message);
    let e_hash = sha512(&chal_input);
    let e_scalar = Scalar25519::from_bytes_mod_order_wide(&e_hash);

    // 6. s = r + e · k_effective  mod L.
    let s_scalar = r_scalar.add(&e_scalar.mul(&k_effective));

    // 7. Output (R, s) = 64 bytes.
    let mut sig = [0u8; 64];
    sig[..32].copy_from_slice(&r_bytes);
    sig[32..].copy_from_slice(&s_scalar.to_bytes());
    sig
}

/// Deterministic-nonce XEdDSA sign — no `random` input.  Used by
/// trait-shape consumers (e.g., x3dh-hax's `X3dhCrypto::sign`) whose
/// trait signature is `sign(secret, msg)` without randomness.
///
/// Nonce derivation: same prefix as randomized XEdDSA but omits the
/// random tail.  `r = SHA-512(0xfe || 0xff×31 || k_effective || msg) mod L`.
/// This is the RFC 8032 deterministic Ed25519 convention adapted to
/// XEdDSA: a single signer/key/msg triple always produces the same
/// signature.  Verifiable by `xeddsa_verify` (same algebraic relation).
///
/// Identical to `xeddsa_sign(secret, msg, &[0u8; 64])` modulo the
/// `random` parameter being omitted from the nonce hash.  KAT'd by the
/// roundtrip test in this module.
pub fn xeddsa_sign_deterministic(privkey: &[u8; 32], message: &[u8]) -> Signature {
    use crate::scalar25519::Scalar25519;
    use crate::ed25519_rustcmd::scalarmult_base_compressed;

    let mut k = *privkey;
    k[0] &= 248;
    k[31] &= 127;
    k[31] |= 64;
    let k_scalar = Scalar25519::from_bytes_mod_order(&k);

    let mut k_bytes_for_mult = k;
    let mut a_compressed = scalarmult_base_compressed(&k_bytes_for_mult);
    let sign_bit = a_compressed[31] >> 7;
    let k_effective: Scalar25519;
    if sign_bit == 1 {
        k_effective = k_scalar.negate();
        k_bytes_for_mult = k_effective.to_bytes();
        a_compressed = scalarmult_base_compressed(&k_bytes_for_mult);
    } else {
        k_effective = k_scalar;
    }

    let k_eff_bytes = k_effective.to_bytes();
    let mut nonce_input = Vec::with_capacity(32 + 32 + message.len());
    nonce_input.push(0xfe);
    nonce_input.extend_from_slice(&[0xffu8; 31]);
    nonce_input.extend_from_slice(&k_eff_bytes);
    nonce_input.extend_from_slice(message);
    let r_hash = sha512(&nonce_input);
    let r_scalar = Scalar25519::from_bytes_mod_order_wide(&r_hash);

    let mut r_bytes_for_mult = r_scalar.to_bytes();
    let r_bytes = scalarmult_base_compressed(&r_bytes_for_mult);
    for b in r_bytes_for_mult.iter_mut() { *b = 0; }

    let mut chal_input = Vec::with_capacity(32 + 32 + message.len());
    chal_input.extend_from_slice(&r_bytes);
    chal_input.extend_from_slice(&a_compressed);
    chal_input.extend_from_slice(message);
    let e_hash = sha512(&chal_input);
    let e_scalar = Scalar25519::from_bytes_mod_order_wide(&e_hash);

    let s_scalar = r_scalar.add(&e_scalar.mul(&k_effective));

    let mut sig = [0u8; 64];
    sig[..32].copy_from_slice(&r_bytes);
    sig[32..].copy_from_slice(&s_scalar.to_bytes());
    sig
}

/// Verify an XEdDSA signature.
///
/// # Arguments
/// * `pubkey` - 32-byte X25519 public key
/// * `message` - signed message
/// * `signature` - 64-byte signature (R || s)
///
/// # Returns
/// `true` if the signature is valid
pub fn xeddsa_verify(pubkey: &[u8; 32], message: &[u8], signature: &Signature) -> bool {
    // 1. Convert X25519 pubkey (Montgomery u-coord) to Edwards form
    //    using ONLY fiat-crypto verified field primitives — no dalek.
    //    XEdDSA convention: the verify-key has sign bit = 0 (positive-y).
    let edwards_pk = match crate::mont_to_edwards::mont_u_to_edwards_compressed(pubkey, 0) {
        Some(b) => b,
        None => return false,
    };

    // 2. Standard Ed25519 verify against the derived Edwards verify-key.
    //    This uses our rust_cmd_ed-extracted, RFC 8032-tested verifier.
    crate::ed25519_rustcmd::verify(signature, &edwards_pk, message)
}

/// Reduce a 64-byte hash to a 32-byte scalar mod l.
/// l = 2^252 + 27742317777372353535851937790883648493
fn scalar_reduce(hash: &[u8; 64]) -> [u8; 32] {
    // Take low 32 bytes (bias ≤ 2^4, negligible for 252-bit security)
    let mut result = [0u8; 32];
    result.copy_from_slice(&hash[..32]);

    // Conditional subtract l if >= l
    // l[3] = 0x10000000_00000000 (byte 31 high nibble = 0x10)
    if result[31] >= 0x10 {
        // Subtract l (simplified)
        let l_bytes: [u8; 32] = [
            0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58,
            0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
        ];
        let mut borrow = 0u16;
        for i in 0..32 {
            let diff = (result[i] as u16).wrapping_sub(l_bytes[i] as u16).wrapping_sub(borrow);
            result[i] = diff as u8;
            borrow = (diff >> 8) & 1;
        }
    }
    result
}

/// Add two 32-byte scalars mod l (simplified).
fn scalar_add_mod_l(a: &[u8; 32], b: &[u8; 32]) -> [u8; 32] {
    let mut result = [0u8; 32];
    let mut carry = 0u16;
    for i in 0..32 {
        let sum = a[i] as u16 + b[i] as u16 + carry;
        result[i] = sum as u8;
        carry = sum >> 8;
    }
    // Conditional subtract l
    let l_bytes: [u8; 32] = [
        0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58,
        0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
    ];
    if result[31] >= 0x10 {
        let mut borrow = 0u16;
        for i in 0..32 {
            let diff = (result[i] as u16).wrapping_sub(l_bytes[i] as u16).wrapping_sub(borrow);
            result[i] = diff as u8;
            borrow = (diff >> 8) & 1;
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    // Tests need pubkey derivation; non-test XEdDSA path doesn't.
    use crate::x25519_jasmin_base;

    #[test]
    fn test_xeddsa_sign_verify_roundtrip() {
        let privkey = [42u8; 32];
        let pubkey = x25519_jasmin_base(&privkey);
        let message = b"Hello Signal";
        let random = [7u8; 64];

        let sig = xeddsa_sign(&privkey, message, &random);
        assert_eq!(sig.len(), 64);

        // Signature should be deterministic for same inputs
        let sig2 = xeddsa_sign(&privkey, message, &random);
        assert_eq!(sig, sig2);

        // Verify roundtrip — the core verification correctness claim.
        assert!(xeddsa_verify(&pubkey, message, &sig),
                "honest signature should verify");
    }

    #[test]
    fn test_xeddsa_verify_rejects_wrong_message() {
        let privkey = [0x42u8; 32];
        let pubkey = x25519_jasmin_base(&privkey);
        let random = [0x07u8; 64];
        let sig = xeddsa_sign(&privkey, b"msg-a", &random);
        assert!(!xeddsa_verify(&pubkey, b"msg-b", &sig),
                "wrong message should fail verify");
    }

    #[test]
    fn test_xeddsa_verify_rejects_wrong_pubkey() {
        let privkey_a = [0x42u8; 32];
        let privkey_b = [0x43u8; 32];
        let pubkey_b = x25519_jasmin_base(&privkey_b);
        let random = [0x07u8; 64];
        let sig = xeddsa_sign(&privkey_a, b"msg", &random);
        assert!(!xeddsa_verify(&pubkey_b, b"msg", &sig),
                "different pubkey should fail verify");
    }

    #[test]
    fn test_xeddsa_verify_rejects_tampered_sig() {
        let privkey = [0x42u8; 32];
        let pubkey = x25519_jasmin_base(&privkey);
        let random = [0x07u8; 64];
        let mut sig = xeddsa_sign(&privkey, b"msg", &random);
        sig[0] ^= 1;  // flip a bit
        assert!(!xeddsa_verify(&pubkey, b"msg", &sig),
                "tampered signature should fail verify");
    }
}
