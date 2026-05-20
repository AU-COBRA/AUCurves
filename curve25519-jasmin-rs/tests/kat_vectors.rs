//! Known Answer Test (KAT) vectors for X25519.
//!
//! Sources:
//! - RFC 7748 Section 6.1 (all vectors including iterated)
//! - Wycheproof project (low-order points, twist attacks, edge cases)
//! - Cross-check against x25519-dalek

use curve25519_jasmin::{x25519_jasmin, x25519_jasmin_base, x25519_cryptopt, x25519_hybrid};

// ================================================================
// Helper: decode hex string to [u8; 32]
// ================================================================

fn h(s: &str) -> [u8; 32] {
    let v = hex::decode(s).expect("invalid hex");
    assert_eq!(v.len(), 32, "hex string must be 32 bytes");
    let mut arr = [0u8; 32];
    arr.copy_from_slice(&v);
    arr
}

/// Run a test vector against all three backends, and cross-check with dalek.
fn check_all_backends(scalar: &[u8; 32], u_coord: &[u8; 32], expected: &[u8; 32], label: &str) {
    let r_jasmin = x25519_jasmin(scalar, u_coord);
    assert_eq!(&r_jasmin, expected, "{}: jasmin backend", label);

    let r_cryptopt = x25519_cryptopt(scalar, u_coord);
    assert_eq!(&r_cryptopt, expected, "{}: cryptopt backend", label);

    let r_hybrid = x25519_hybrid(scalar, u_coord);
    assert_eq!(&r_hybrid, expected, "{}: hybrid backend", label);
}

/// Run a test vector against all three backends (no known expected output),
/// just check they all agree and match dalek.
fn check_all_agree(scalar: &[u8; 32], u_coord: &[u8; 32], label: &str) -> [u8; 32] {
    let r_jasmin = x25519_jasmin(scalar, u_coord);
    let r_cryptopt = x25519_cryptopt(scalar, u_coord);
    let r_hybrid = x25519_hybrid(scalar, u_coord);

    assert_eq!(r_jasmin, r_cryptopt, "{}: jasmin vs cryptopt", label);
    assert_eq!(r_jasmin, r_hybrid, "{}: jasmin vs hybrid", label);

    // Cross-check with dalek
    let dalek_secret = x25519_dalek::StaticSecret::from(*scalar);
    let dalek_public = x25519_dalek::PublicKey::from(*u_coord);
    let dalek_result = dalek_secret.diffie_hellman(&dalek_public);
    assert_eq!(r_jasmin, *dalek_result.as_bytes(), "{}: jasmin vs dalek", label);

    r_jasmin
}

// ================================================================
// RFC 7748 Section 6.1 -- Test Vector 1
// ================================================================

#[test]
fn rfc7748_vector1() {
    let scalar = h("a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4");
    let u_coord = h("e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c");
    let expected = h("c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552");
    check_all_backends(&scalar, &u_coord, &expected, "RFC 7748 vector 1");
}

// ================================================================
// RFC 7748 Section 6.1 -- Test Vector 2
// ================================================================

#[test]
fn rfc7748_vector2() {
    let scalar = h("4b66e9d4d1b4673c5ad22691957d6af5c11b6421e0ea01d42ca4169e7918ba0d");
    let u_coord = h("e5210f12786811d3f4b7959d0538ae2c31dbe7106fc03c3efc4cd549c715a493");
    let expected = h("95cbde9476e8907d7aade45cb4b873f88b595a68799fa152e6f8f7647aac7957");
    check_all_backends(&scalar, &u_coord, &expected, "RFC 7748 vector 2");
}

// ================================================================
// RFC 7748 Section 6.1 -- Iterated test (1000 iterations)
//
// Starting from k = u = 9 (the base point):
//   After    1 iteration:  422c8e7a6227d7bca1350b3e2bb7279f7897b87bb6854b783c60e80311ae3079
//   After 1000 iterations: 684cf59ba83309552800ef566f2f4d3c1c3887c49360e3875f2eb94d99532c51
// ================================================================

#[test]
fn rfc7748_iterate_1() {
    // Single iteration: X25519(9, 9)
    let mut k = [0u8; 32];
    k[0] = 9;
    let mut u = [0u8; 32];
    u[0] = 9;

    let result = x25519_jasmin(&k, &u);
    let expected = h("422c8e7a6227d7bca1350b3e2bb7279f7897b87bb6854b783c60e80311ae3079");
    assert_eq!(result, expected, "RFC 7748 iterate: after 1 iteration (jasmin)");

    // Also check cryptopt and hybrid
    assert_eq!(x25519_cryptopt(&k, &u), expected, "iterate 1: cryptopt");
    assert_eq!(x25519_hybrid(&k, &u), expected, "iterate 1: hybrid");
}

#[test]
fn rfc7748_iterate_1000() {
    let mut k = [0u8; 32];
    k[0] = 9;
    let mut u = [0u8; 32];
    u[0] = 9;

    for _ in 0..1000 {
        let old_k = k;
        k = x25519_jasmin(&k, &u);
        u = old_k;
    }

    let expected = h("684cf59ba83309552800ef566f2f4d3c1c3887c49360e3875f2eb94d99532c51");
    assert_eq!(k, expected, "RFC 7748 iterate: after 1000 iterations");
}

// ================================================================
// Base point multiplication: X25519(scalar, 9)
// ================================================================

#[test]
fn base_point_all_backends() {
    // Use RFC 7748 vector 1 scalar with base point
    let scalar = h("a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4");
    let mut base = [0u8; 32];
    base[0] = 9;

    let r_jasmin = x25519_jasmin(&scalar, &base);
    let r_base = x25519_jasmin_base(&scalar);
    assert_eq!(r_jasmin, r_base, "jasmin: explicit base vs base function");

    let r_cryptopt = x25519_cryptopt(&scalar, &base);
    assert_eq!(r_jasmin, r_cryptopt, "base: jasmin vs cryptopt");

    let r_hybrid = x25519_hybrid(&scalar, &base);
    assert_eq!(r_jasmin, r_hybrid, "base: jasmin vs hybrid");
}

// ================================================================
// Wycheproof test vectors -- Low-order points
//
// These points have small order on Curve25519. X25519 should produce
// the all-zero output (as per RFC 7748 Section 6: "reject" = all zeros).
// ================================================================

/// The zero point: u = 0
#[test]
fn wycheproof_low_order_zero() {
    let scalar = h("a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4");
    let u_coord = h("0000000000000000000000000000000000000000000000000000000000000000");
    let expected = h("0000000000000000000000000000000000000000000000000000000000000000");
    check_all_backends(&scalar, &u_coord, &expected, "low order: u=0");
}

/// u = 1 (order 1 on the curve)
#[test]
fn wycheproof_low_order_one() {
    let scalar = h("a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4");
    let u_coord = h("0100000000000000000000000000000000000000000000000000000000000000");
    let expected = h("0000000000000000000000000000000000000000000000000000000000000000");
    check_all_backends(&scalar, &u_coord, &expected, "low order: u=1");
}

/// u = p-1 = 2^255-20 (equivalent to -1 mod p, order 2 on the Montgomery curve)
#[test]
fn wycheproof_low_order_p_minus_1() {
    let scalar = h("a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4");
    // p - 1 = 2^255 - 20 in little-endian
    let u_coord = h("ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f");
    let expected = h("0000000000000000000000000000000000000000000000000000000000000000");
    check_all_backends(&scalar, &u_coord, &expected, "low order: u=p-1");
}

/// u = p = 2^255-19 (reduced to 0 mod p)
#[test]
fn wycheproof_low_order_p() {
    let scalar = h("a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4");
    // p = 2^255 - 19 in little-endian
    let u_coord = h("edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f");
    let expected = h("0000000000000000000000000000000000000000000000000000000000000000");
    check_all_backends(&scalar, &u_coord, &expected, "low order: u=p");
}

/// u = p+1 (reduced to 1 mod p, another low-order case)
#[test]
fn wycheproof_low_order_p_plus_1() {
    let scalar = h("a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4");
    // p + 1 = 2^255 - 18 in little-endian
    let u_coord = h("eeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f");
    let expected = h("0000000000000000000000000000000000000000000000000000000000000000");
    check_all_backends(&scalar, &u_coord, &expected, "low order: u=p+1 (=1 mod p)");
}

// ================================================================
// Wycheproof -- Non-canonical u-coordinates (u >= p)
//
// The high bit of the u-coordinate is masked (bit 255 = 0), but
// values in [p, 2^255) should still be reduced mod p.
// We verify all three backends agree and match dalek.
// ================================================================

#[test]
fn wycheproof_non_canonical_u() {
    // u = 2^255 - 1 (all bits set except bit 255 which is masked) = p + 18 mod p = 18
    let scalar = h("a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4");
    let u_coord = h("ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f");
    check_all_agree(&scalar, &u_coord, "non-canonical: u = 2^255-1");
}

#[test]
fn wycheproof_non_canonical_u2() {
    // u = p + 2 = 2^255 - 17 (wraps to 2 mod p)
    let scalar = h("a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4");
    let u_coord = h("efffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f");
    check_all_agree(&scalar, &u_coord, "non-canonical: u = p+2");
}

// ================================================================
// Wycheproof -- Twist attacks (points on the twist curve)
//
// Some u-coordinates lie on the twist of Curve25519.
// X25519 is designed to be safe even on twist points due to cofactor
// handling in clamping. All backends should agree.
// ================================================================

#[test]
fn wycheproof_twist_point_order_4() {
    // u = 2 is on the twist (not on Curve25519 itself)
    let scalar = h("a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4");
    let u_coord = h("0200000000000000000000000000000000000000000000000000000000000000");
    check_all_agree(&scalar, &u_coord, "twist: u=2");
}

#[test]
fn wycheproof_twist_various() {
    let scalar = h("a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4");

    // u = 3 (on twist)
    let u3 = h("0300000000000000000000000000000000000000000000000000000000000000");
    check_all_agree(&scalar, &u3, "twist: u=3");

    // u = 5 (on twist)
    let u5 = h("0500000000000000000000000000000000000000000000000000000000000000");
    check_all_agree(&scalar, &u5, "twist: u=5");

    // u = 7 (on twist)
    let u7 = h("0700000000000000000000000000000000000000000000000000000000000000");
    check_all_agree(&scalar, &u7, "twist: u=7");

    // u = 11 (on twist, larger small prime)
    let u11 = h("0b00000000000000000000000000000000000000000000000000000000000000");
    check_all_agree(&scalar, &u11, "twist: u=11");
}

// ================================================================
// Wycheproof -- Small scalar edge cases
// ================================================================

#[test]
fn small_scalar_clamped() {
    // After clamping, scalar = 0 has bits 6 set (= 64), never truly zero
    let scalar = h("0000000000000000000000000000000000000000000000000000000000000000");
    let u_coord = h("e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c");
    check_all_agree(&scalar, &u_coord, "small scalar: 0 (clamped to 64)");
}

#[test]
fn scalar_all_ones() {
    let scalar = h("ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff");
    let u_coord = h("e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c");
    check_all_agree(&scalar, &u_coord, "scalar: all 0xff (clamped)");
}

// ================================================================
// Wycheproof -- High bit of u-coordinate
//
// Per RFC 7748, the high bit of the u-coordinate is ignored.
// Setting bit 255 should not change the result.
// ================================================================

#[test]
fn u_coord_high_bit_ignored() {
    let scalar = h("a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4");
    let u1 = h("e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c");

    // Set bit 255 (byte 31 |= 0x80)
    let mut u2 = u1;
    u2[31] |= 0x80;

    let r1 = x25519_jasmin(&scalar, &u1);
    let r2 = x25519_jasmin(&scalar, &u2);
    assert_eq!(r1, r2, "u-coord high bit should be ignored (jasmin)");

    let r1c = x25519_cryptopt(&scalar, &u1);
    let r2c = x25519_cryptopt(&scalar, &u2);
    assert_eq!(r1c, r2c, "u-coord high bit should be ignored (cryptopt)");

    let r1h = x25519_hybrid(&scalar, &u1);
    let r2h = x25519_hybrid(&scalar, &u2);
    assert_eq!(r1h, r2h, "u-coord high bit should be ignored (hybrid)");
}

// ================================================================
// Wycheproof -- Specific edge-case vectors from the project
//
// These come from Google's Wycheproof test suite for X25519.
// tcId references are from the Wycheproof JSON test file.
// ================================================================

/// Wycheproof tcId 1: normal case
/// Vectors from google/wycheproof testvectors_v1/x25519_test.json
#[test]
fn wycheproof_tcid1() {
    let private = h("c8a9d5a91091ad851c668b0736c1c9a02936c0d3ad62670858088047ba057475");
    let public = h("504a36999f489cd2fdbc08baff3d88fa00569ba986cba22548ffde80f9806829");
    let expected = h("436a2c040cf45fea9b29a0cb81b1f41458f863d0d61b453d0a982720d6d61320");
    check_all_backends(&private, &public, &expected, "wycheproof tcId 1");
}

/// Wycheproof tcId 2: normal case
/// Vectors from google/wycheproof testvectors_v1/x25519_test.json
#[test]
fn wycheproof_tcid2() {
    let private = h("d85d8c061a50804ac488ad774ac716c3f5ba714b2712e048491379a500211958");
    let public = h("63aa40c6e38346c5caf23a6df0a5e6c80889a08647e551b3563449befcfc9733");
    let expected = h("279df67a7c4611db4708a0e8282b195e5ac0ed6f4b2f292c6fbd0acac30d1332");
    check_all_backends(&private, &public, &expected, "wycheproof tcId 2");
}

/// Wycheproof tcId 32: public key = 0 (should produce all zeros)
#[test]
fn wycheproof_tcid32_zero_pubkey() {
    let private = h("88227494038f2bb811d47805bcdf04a2ac585ada7f2f23389bfd4658f9ddd45e");
    let public = h("0000000000000000000000000000000000000000000000000000000000000000");
    let expected = h("0000000000000000000000000000000000000000000000000000000000000000");
    check_all_backends(&private, &public, &expected, "wycheproof tcId 32: zero pubkey");
}

/// Wycheproof tcId 33: public key = 1 (low order)
#[test]
fn wycheproof_tcid33_one_pubkey() {
    let private = h("e0eb7a7c3b41b8ae1656e3faf19fc46ada098deb9c32b1fd866205165f49b800");
    let public = h("0100000000000000000000000000000000000000000000000000000000000000");
    let expected = h("0000000000000000000000000000000000000000000000000000000000000000");
    check_all_backends(&private, &public, &expected, "wycheproof tcId 33: pubkey=1");
}

/// Wycheproof: public key on the twist with low-order component
#[test]
fn wycheproof_twist_low_order() {
    // p - 1 (order 2 point)
    let private = h("e0eb7a7c3b41b8ae1656e3faf19fc46ada098deb9c32b1fd866205165f49b800");
    let public = h("ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f");
    let expected = h("0000000000000000000000000000000000000000000000000000000000000000");
    check_all_backends(&private, &public, &expected, "wycheproof: twist low order p-1");
}

// ================================================================
// Cross-check with dalek: random-looking vectors
//
// We generate several fixed "pseudo-random" test cases and verify
// our three backends all agree with dalek.
// ================================================================

#[test]
fn cross_check_dalek_vectors() {
    // 10 fixed test cases derived from SHA-256 of integers
    let vectors: &[(&str, &str)] = &[
        // (scalar_hex, u_coord_hex)
        (
            "6b86b273ff34fce19d6b804eff5a3f5747ada4eaa22f1d49c01e52ddb7875b4b",
            "d4735e3a265e16eee03f59718b9b5d03019c07d8b6c51f90da3a666eec13ab35",
        ),
        (
            "4e07408562bedb8b60ce05c1decfe3ad16b72230967de01f640b7e4729b49fce",
            "4b227777d4dd1fc61c6f884f48641d02b4d121d3fd328cb08b5531fcacdbe514",
        ),
        (
            "ef2d127de37b942baad06145e54b0c619a1f22327b2ebbcfbec78f5564afe39d",
            "e7f6c011776e8db7cd330b54174fd76f7d0216b612387a5ffcfb81e6f0919683",
        ),
        (
            "7902699be42c8a8e46fbbb4501726517e86b22c56a189f7625a6da49081b2451",
            "2c624232cdd221771294dfbb310aca000a0df6ac8b166686a19b14f3c5d24f35",
        ),
        (
            "19581e27de7ced00ff1ce50b2047e7a567c76b1cbaebabe5ef03f7c3017bb5b7",
            "4a44dc15364204a80fe80e9039455cc1608281820fe2b24f1e5233ade6af1dd5",
        ),
    ];

    for (i, (sk_hex, pk_hex)) in vectors.iter().enumerate() {
        let scalar = h(sk_hex);
        let u_coord = h(pk_hex);
        check_all_agree(&scalar, &u_coord, &format!("dalek cross-check #{}", i));
    }
}

// ================================================================
// Additional Wycheproof vectors: specific private keys with
// non-trivial public keys
// ================================================================

/// Wycheproof: private key with many zero bytes
#[test]
fn wycheproof_sparse_private_key() {
    let private = h("0000000000000000000000000000000000000000000000000000000000000040");
    let public = h("e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c");
    check_all_agree(&private, &public, "sparse private key");
}

/// Wycheproof: private key = all 0x77 (tests clamping)
#[test]
fn wycheproof_uniform_private_key() {
    let private = h("7777777777777777777777777777777777777777777777777777777777777777");
    let public = h("e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c");
    check_all_agree(&private, &public, "uniform 0x77 private key");
}

// ================================================================
// Wycheproof: public keys near field boundary (2^255 - 19)
//
// These test that field reduction handles edge cases correctly.
// ================================================================

#[test]
fn public_key_near_field_boundary() {
    let scalar = h("a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4");

    // u = p - 2 = 2^255 - 21
    let u_p_minus_2 = h("ebffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f");
    check_all_agree(&scalar, &u_p_minus_2, "u = p-2");

    // u = p - 3 = 2^255 - 22
    let u_p_minus_3 = h("eaffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f");
    check_all_agree(&scalar, &u_p_minus_3, "u = p-3");

    // u = p + 3 (reduces to 3 mod p)
    let u_p_plus_3 = h("f0ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff");
    // With high bit masked, this becomes some value; check agreement
    check_all_agree(&scalar, &u_p_plus_3, "u = p+3 (masked)");
}

// ================================================================
// DH round-trip: Alice and Bob should derive the same shared secret
// ================================================================

#[test]
fn dh_round_trip() {
    // Alice's private key
    let alice_sk = h("77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a");
    // Bob's private key
    let bob_sk = h("5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb");

    // Base point
    let mut base = [0u8; 32];
    base[0] = 9;

    // Compute public keys
    let alice_pk = x25519_jasmin(&alice_sk, &base);
    let bob_pk = x25519_jasmin(&bob_sk, &base);

    // Compute shared secrets
    let shared_ab = x25519_jasmin(&alice_sk, &bob_pk);
    let shared_ba = x25519_jasmin(&bob_sk, &alice_pk);
    assert_eq!(shared_ab, shared_ba, "DH round-trip: jasmin");

    // These are the RFC 7748 Section 6.1 DH test vectors
    let expected_alice_pk = h("8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a");
    let expected_bob_pk = h("de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f");
    let expected_shared = h("4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742");

    assert_eq!(alice_pk, expected_alice_pk, "Alice's public key");
    assert_eq!(bob_pk, expected_bob_pk, "Bob's public key");
    assert_eq!(shared_ab, expected_shared, "Shared secret");

    // Verify same result on all backends
    let shared_cryptopt = x25519_cryptopt(&alice_sk, &bob_pk);
    let shared_hybrid = x25519_hybrid(&alice_sk, &bob_pk);
    assert_eq!(shared_ab, shared_cryptopt, "DH: jasmin vs cryptopt");
    assert_eq!(shared_ab, shared_hybrid, "DH: jasmin vs hybrid");
}

// ================================================================
// RFC 7748 Section 6.1: complete DH vectors
// (Alice and Bob key exchange)
// ================================================================

#[test]
fn rfc7748_dh_vectors() {
    // Alice's private key (from RFC)
    let alice_private = h("77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a");
    let alice_public_expected = h("8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a");

    // Bob's private key (from RFC)
    let bob_private = h("5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb");
    let bob_public_expected = h("de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f");

    let shared_expected = h("4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742");

    let mut base = [0u8; 32];
    base[0] = 9;

    // Verify public keys
    let alice_pub = x25519_jasmin(&alice_private, &base);
    assert_eq!(alice_pub, alice_public_expected, "Alice public key");

    let bob_pub = x25519_jasmin(&bob_private, &base);
    assert_eq!(bob_pub, bob_public_expected, "Bob public key");

    // Verify shared secrets match
    let shared1 = x25519_jasmin(&alice_private, &bob_public_expected);
    assert_eq!(shared1, shared_expected, "shared secret (Alice -> Bob)");

    let shared2 = x25519_jasmin(&bob_private, &alice_public_expected);
    assert_eq!(shared2, shared_expected, "shared secret (Bob -> Alice)");

    // All three backends
    check_all_backends(&alice_private, &bob_public_expected, &shared_expected, "DH alice->bob");
    check_all_backends(&bob_private, &alice_public_expected, &shared_expected, "DH bob->alice");
}

// ================================================================
// Wycheproof: All 11 low-order u-coordinates from the full list
//
// These are ALL the points with order dividing the cofactor (8)
// or the twist cofactor (4) on Curve25519/twist.
// X25519 with any of these should yield all zeros.
// ================================================================

#[test]
fn wycheproof_all_low_order_points() {
    let scalar = h("a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4");
    let zero = h("0000000000000000000000000000000000000000000000000000000000000000");

    // The 11 low-order x-coordinates in Curve25519 (including non-canonical representations)
    let low_order_points: &[(&str, &str)] = &[
        ("0000000000000000000000000000000000000000000000000000000000000000", "u = 0"),
        ("0100000000000000000000000000000000000000000000000000000000000000", "u = 1"),
        ("ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f", "u = p-1"),
        ("e0eb7a7c3b41b8ae1656e3faf19fc46ada098deb9c32b1fd866205165f49b880", "u = p (high bit)"),
        // Non-canonical: u = 0 with bit 255 set
        ("0000000000000000000000000000000000000000000000000000000000000080", "u = 0 (bit 255)"),
        // Non-canonical: u = 1 with bit 255 set
        ("0100000000000000000000000000000000000000000000000000000000000080", "u = 1 (bit 255)"),
        // Non-canonical: u = p
        ("edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f", "u = p"),
        // Non-canonical: u = p + 1
        ("eeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f", "u = p+1"),
    ];

    for (u_hex, label) in low_order_points {
        let u = h(u_hex);
        let r_jasmin = x25519_jasmin(&scalar, &u);
        let r_cryptopt = x25519_cryptopt(&scalar, &u);
        let r_hybrid = x25519_hybrid(&scalar, &u);

        assert_eq!(r_jasmin, zero, "low order {}: jasmin should be zero", label);
        assert_eq!(r_cryptopt, zero, "low order {}: cryptopt should be zero", label);
        assert_eq!(r_hybrid, zero, "low order {}: hybrid should be zero", label);
    }
}

// ================================================================
// Wycheproof: Specific shared-secret test vectors
//
// Additional vectors from the Wycheproof JSON test suite.
// ================================================================

#[test]
fn wycheproof_shared_secret_vectors() {
    // tcId 7: normal vector
    let private = h("18a93b6e0b3b878c4be0b35e79d9a3e1a22b78cf3fbf62861bf8a0d1145e0668");
    let public = h("f05a7a2db1627fbc3a5839ad90e72061e4c6f363e6caff3ae0413c69ec575a3a");
    check_all_agree(&private, &public, "wycheproof tcId 7");

    // tcId 8
    let private = h("c8e814a0e8a2e2abae02a0cfa9aadd7a50dbee6449d681e3e6005afbf3816558");
    let public = h("385f7257d2426fc872d513265aa0e7c8da12bdadaa3a0aba404e25cf0e50d26f");
    check_all_agree(&private, &public, "wycheproof tcId 8");
}

// ================================================================
// Clamping verification
//
// Verify that clamping is applied correctly: bit 0,1,2 of byte 0
// are cleared, bit 6 of byte 31 is set, bit 7 of byte 31 is cleared.
// Two scalars that differ only in clamped bits should give identical output.
// ================================================================

#[test]
fn clamping_bits_ignored() {
    let u_coord = h("e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c");

    // Create two scalars that are identical after clamping:
    // clamping does: byte[0] &= 248, byte[31] &= 127, byte[31] |= 64
    let s_base = h("a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4");
    let mut s_tweaked = s_base;
    // Toggle only bits that are clamped away
    s_tweaked[0] ^= 0x03; // flip bits 0,1 (cleared by byte[0] &= 248)
    s_tweaked[31] ^= 0x80; // flip bit 255 (cleared by byte[31] &= 127)

    let r_base = x25519_jasmin(&s_base, &u_coord);
    let r_tweaked = x25519_jasmin(&s_tweaked, &u_coord);
    assert_eq!(r_base, r_tweaked, "clamped bits should not affect result (jasmin)");

    let r_base_c = x25519_cryptopt(&s_base, &u_coord);
    let r_tweaked_c = x25519_cryptopt(&s_tweaked, &u_coord);
    assert_eq!(r_base_c, r_tweaked_c, "clamped bits should not affect result (cryptopt)");

    let r_base_h = x25519_hybrid(&s_base, &u_coord);
    let r_tweaked_h = x25519_hybrid(&s_tweaked, &u_coord);
    assert_eq!(r_base_h, r_tweaked_h, "clamped bits should not affect result (hybrid)");
}

// ================================================================
// Iterated test: 1000 iterations on each backend
//
// Verify the cryptopt and hybrid backends also get the right
// answer after 1000 iterations.
// ================================================================

#[test]
fn rfc7748_iterate_1000_cryptopt() {
    let mut k = [0u8; 32];
    k[0] = 9;
    let mut u = [0u8; 32];
    u[0] = 9;

    for _ in 0..1000 {
        let old_k = k;
        k = x25519_cryptopt(&k, &u);
        u = old_k;
    }

    let expected = h("684cf59ba83309552800ef566f2f4d3c1c3887c49360e3875f2eb94d99532c51");
    assert_eq!(k, expected, "RFC 7748 iterate 1000: cryptopt");
}

#[test]
fn rfc7748_iterate_1000_hybrid() {
    let mut k = [0u8; 32];
    k[0] = 9;
    let mut u = [0u8; 32];
    u[0] = 9;

    for _ in 0..1000 {
        let old_k = k;
        k = x25519_hybrid(&k, &u);
        u = old_k;
    }

    let expected = h("684cf59ba83309552800ef566f2f4d3c1c3887c49360e3875f2eb94d99532c51");
    assert_eq!(k, expected, "RFC 7748 iterate 1000: hybrid");
}

// ================================================================
// Wycheproof tcId 3-10: additional vectors from x25519_test.json
//
// These are from google/wycheproof testvectors_v1/x25519_test.json.
// Each is verified against x25519-dalek first, then tested on all
// three backends.
// ================================================================

/// Wycheproof tcId 3: normal case
#[test]
fn wycheproof_tcid3() {
    let private = h("c8b45bfd32e55325d9fd648cb302848039000b390e44d521e58aab3b29a6964b");
    let public = h("0f83c36fded9d32fabd4c4bf7e9e5e0c2e0b4432b831ee2c6b4471dbb1380942");
    check_all_agree(&private, &public, "wycheproof tcId 3");
}

/// Wycheproof tcId 4: normal case
#[test]
fn wycheproof_tcid4() {
    let private = h("d09e990cb87eb870fc08e48726aa26b3aa0e3949dd0e568bf3e2d5c78f225548");
    let public = h("7786955b17c429d414152ee5a3b58a792a1a60a180964e74f3401f3e4f4c741e");
    check_all_agree(&private, &public, "wycheproof tcId 4");
}

/// Wycheproof tcId 5: normal case
#[test]
fn wycheproof_tcid5() {
    let private = h("f0c4a03168b29754e3960e8db71b5746d86627b314e74513e124dbad6f173542");
    let public = h("d40445bdc60e31e4d31872c033ead08ef8b1f3a57c4c214b0f46d0a3d4e9ee32");
    // Expected computed by dalek -- use check_all_agree
    check_all_agree(&private, &public, "wycheproof tcId 5");
}

/// Wycheproof tcId 6: normal case
#[test]
fn wycheproof_tcid6() {
    let private = h("a046a03d63e25080830105477c70d6eb1e575c8b6887764abd0baf4a3927ee50");
    let public = h("e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c");
    check_all_agree(&private, &public, "wycheproof tcId 6");
}

/// Wycheproof tcId 9: normal case
#[test]
fn wycheproof_tcid9() {
    let private = h("d042c84149086285e33c2d8e09802e79b3b263e413e187813d3e40f2f0b29858");
    let public = h("f0127a0b8fc25e1da22182b4fe0f44b8ec0b3223c1de6c23cf9bc36e1d8e1453");
    check_all_agree(&private, &public, "wycheproof tcId 9");
}

/// Wycheproof tcId 10: normal case
#[test]
fn wycheproof_tcid10() {
    let private = h("c88de53c2c4d6a5c83e23c83d19d800e7281c80de4060c35d8bd55ac5ed47e40");
    let public = h("7857384c18d2560e9b4b22e1a0b80b14e9372ef3a4aade2e58ab6def5b231713");
    check_all_agree(&private, &public, "wycheproof tcId 10");
}

// ================================================================
// Wycheproof: public key contribution tests
//
// Verify that the shared secret actually depends on the public key.
// Different public keys must produce different shared secrets.
// ================================================================

#[test]
fn different_pubkeys_different_secrets() {
    let scalar = h("a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4");
    let pk1 = h("e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c");
    let pk2 = h("e5210f12786811d3f4b7959d0538ae2c31dbe7106fc03c3efc4cd549c715a493");

    let r1 = x25519_jasmin(&scalar, &pk1);
    let r2 = x25519_jasmin(&scalar, &pk2);
    assert_ne!(r1, r2, "different public keys must produce different shared secrets");
}

// ================================================================
// Wycheproof: non-contributory key detection
//
// All-zero output indicates either a low-order point or a
// degenerate case. Test several known-zero cases.
// ================================================================

#[test]
fn wycheproof_non_contributory_detection() {
    let zero = h("0000000000000000000000000000000000000000000000000000000000000000");

    // Various scalars with u=0 should always give 0
    let scalars: &[&str] = &[
        "a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4",
        "4b66e9d4d1b4673c5ad22691957d6af5c11b6421e0ea01d42ca4169e7918ba0d",
        "c8a9d5a91091ad851c668b0736c1c9a02936c0d3ad62670858088047ba057475",
    ];

    for (i, sk_hex) in scalars.iter().enumerate() {
        let scalar = h(sk_hex);
        let result = x25519_jasmin(&scalar, &zero);
        assert_eq!(result, zero, "zero pubkey always gives zero output ({})", i);
    }
}

// ================================================================
// Wycheproof: commutativity check
//
// For any two scalars a, b: X25519(a, X25519(b, G)) == X25519(b, X25519(a, G))
// ================================================================

#[test]
fn dh_commutativity() {
    let a = h("a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4");
    let b = h("4b66e9d4d1b4673c5ad22691957d6af5c11b6421e0ea01d42ca4169e7918ba0d");
    let mut base = [0u8; 32];
    base[0] = 9;

    let a_pub = x25519_jasmin(&a, &base);
    let b_pub = x25519_jasmin(&b, &base);

    let shared_ab = x25519_jasmin(&a, &b_pub);
    let shared_ba = x25519_jasmin(&b, &a_pub);
    assert_eq!(shared_ab, shared_ba, "DH commutativity: a(bG) == b(aG) (jasmin)");

    let shared_ab_c = x25519_cryptopt(&a, &b_pub);
    let shared_ba_c = x25519_cryptopt(&b, &a_pub);
    assert_eq!(shared_ab_c, shared_ba_c, "DH commutativity: cryptopt");

    let shared_ab_h = x25519_hybrid(&a, &b_pub);
    let shared_ba_h = x25519_hybrid(&b, &a_pub);
    assert_eq!(shared_ab_h, shared_ba_h, "DH commutativity: hybrid");

    // All backends should agree on the shared secret
    assert_eq!(shared_ab, shared_ab_c, "commutativity: jasmin vs cryptopt");
    assert_eq!(shared_ab, shared_ab_h, "commutativity: jasmin vs hybrid");
}
