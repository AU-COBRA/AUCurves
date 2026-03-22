use bls12_pairing::pairing;

const FP_WORDS: usize = 6;
const FP12_WORDS: usize = 72;

const FP_ONE_MONT: [u64; 6] = [
    0x760900000002fffd, 0xebf4000bc40c0002,
    0x5f48985753c758ba, 0x77ce585370525745,
    0x5c071a97a256ec6d, 0x15f65ec3fa80e493,
];

const G1_X: [u64; 6] = [
    0x5cb38790fd530c16, 0x7817fc679976fff5,
    0x154f95c7143ba1c1, 0xf0ae6acdf3d0e747,
    0xedce6ecc21dbf440, 0x120177419e0bfb75,
];
const G1_Y: [u64; 6] = [
    0xbaac93d50ce72271, 0x8c22631a7918fd8e,
    0xdd595f13570725ce, 0x51ac582950405194,
    0x0e1c8c3fad0059c0, 0x0bbc3efc5008a26a,
];
const G2_X: [u64; 12] = [
    0xf5f28fa202940a10, 0xb3f5fb2687b4961a,
    0xa1a893b53e2ae580, 0x9894999d1a3caee9,
    0x6f67b7631863366b, 0x058191924350bcd7,
    0xa5a9c0759e23f606, 0xaaa0c59dbccd60c3,
    0x3bb17e18e2867806, 0x1b1ab6cc8541b367,
    0xc2b6ed0ef2158547, 0x11922a097360edf3,
];
const G2_Y: [u64; 12] = [
    0x4c730af860494c4a, 0x597cfa1f5e369c5a,
    0xe7e6856caa0a635a, 0xbbefb5e96e0d495f,
    0x07d3a975f0ef25a2, 0x0083fd8e7e80dae5,
    0xadc0fc92df64b05d, 0x18aa270a2b1461dc,
    0x86adac6a3be4eba0, 0x79495c4ec93da33a,
    0xe7175850a43ccaed, 0x00b2bc2a163de1bf,
];

fn fp12_is_one(x: &[u64; FP12_WORDS]) -> bool {
    if x[..FP_WORDS] != FP_ONE_MONT {
        return false;
    }
    x[FP_WORDS..].iter().all(|&v| v == 0)
}

fn fp12_is_nonzero(x: &[u64; FP12_WORDS]) -> bool {
    x.iter().any(|&v| v != 0)
}

#[test]
fn test_fp12_mul_one_one() {
    let mut one = [0u64; FP12_WORDS];
    one[..FP_WORDS].copy_from_slice(&FP_ONE_MONT);

    let mut result = [0u64; FP12_WORDS];
    pairing::bls12_Fp12_mul(
        result.as_mut_ptr() as u64,
        one.as_ptr() as u64,
        one.as_ptr() as u64,
    );
    assert!(fp12_is_one(&result), "Fp12: 1 * 1 should equal 1");
}

#[test]
fn test_fp12_square_one() {
    let mut one = [0u64; FP12_WORDS];
    one[..FP_WORDS].copy_from_slice(&FP_ONE_MONT);

    let mut result = [0u64; FP12_WORDS];
    pairing::bls12_Fp12_square(
        result.as_mut_ptr() as u64,
        one.as_ptr() as u64,
    );
    assert!(fp12_is_one(&result), "Fp12: 1^2 should equal 1");
}

#[test]
fn test_fp12_conjugate_involution() {
    let mut one = [0u64; FP12_WORDS];
    one[..FP_WORDS].copy_from_slice(&FP_ONE_MONT);

    let mut conj1 = [0u64; FP12_WORDS];
    let mut conj2 = [0u64; FP12_WORDS];
    pairing::bls12_Fp12_conjugate(
        conj1.as_mut_ptr() as u64,
        one.as_ptr() as u64,
    );
    pairing::bls12_Fp12_conjugate(
        conj2.as_mut_ptr() as u64,
        conj1.as_ptr() as u64,
    );
    assert_eq!(one, conj2, "Fp12: conj(conj(1)) should equal 1");
}

#[test]
fn test_fp12_inv_one() {
    let mut one = [0u64; FP12_WORDS];
    one[..FP_WORDS].copy_from_slice(&FP_ONE_MONT);

    let mut result = [0u64; FP12_WORDS];
    pairing::bls12_Fp12_inv(
        result.as_mut_ptr() as u64,
        one.as_ptr() as u64,
    );
    assert!(fp12_is_one(&result), "Fp12: inv(1) should equal 1");
}

#[test]
fn test_miller_loop() {
    let mut result = [0u64; FP12_WORDS];
    pairing::bls12_miller_loop(
        result.as_mut_ptr() as u64,
        G1_X.as_ptr() as u64,
        G1_Y.as_ptr() as u64,
        G2_X.as_ptr() as u64,
        G2_Y.as_ptr() as u64,
    );
    assert!(fp12_is_nonzero(&result), "Miller loop output should be non-zero");
    assert!(!fp12_is_one(&result), "Miller loop output should not be 1");

    // Check against known C output
    assert_eq!(result[0], 0x328e8c3298065878, "Miller loop[0] mismatch");
    assert_eq!(result[1], 0x81bd9cb54ac1a551, "Miller loop[1] mismatch");
}

#[test]
fn test_full_pairing() {
    let mut result = [0u64; FP12_WORDS];
    pairing::bls12_pairing(
        result.as_mut_ptr() as u64,
        G1_X.as_ptr() as u64,
        G1_Y.as_ptr() as u64,
        G2_X.as_ptr() as u64,
        G2_Y.as_ptr() as u64,
    );
    assert!(fp12_is_nonzero(&result), "Pairing output should be non-zero");
    assert!(!fp12_is_one(&result), "Pairing output should not be 1");

    // Check against known C output
    assert_eq!(result[0], 0x339dfcbe37135c6a, "e(G1,G2)[0] mismatch");
    assert_eq!(result[1], 0x8d4c8708f85ec79a, "e(G1,G2)[1] mismatch");
}

#[test]
fn test_pairing_sq_vs_mul() {
    let mut e = [0u64; FP12_WORDS];
    pairing::bls12_pairing(
        e.as_mut_ptr() as u64,
        G1_X.as_ptr() as u64,
        G1_Y.as_ptr() as u64,
        G2_X.as_ptr() as u64,
        G2_Y.as_ptr() as u64,
    );

    let mut e_sq = [0u64; FP12_WORDS];
    pairing::bls12_Fp12_square(e_sq.as_mut_ptr() as u64, e.as_ptr() as u64);

    let mut e_mul = [0u64; FP12_WORDS];
    pairing::bls12_Fp12_mul(
        e_mul.as_mut_ptr() as u64,
        e.as_ptr() as u64,
        e.as_ptr() as u64,
    );

    assert_eq!(e_sq, e_mul, "e(G1,G2)^2 should equal e(G1,G2)*e(G1,G2)");
}

#[test]
fn test_pairing_inv() {
    let mut e = [0u64; FP12_WORDS];
    pairing::bls12_pairing(
        e.as_mut_ptr() as u64,
        G1_X.as_ptr() as u64,
        G1_Y.as_ptr() as u64,
        G2_X.as_ptr() as u64,
        G2_Y.as_ptr() as u64,
    );

    let mut e_inv = [0u64; FP12_WORDS];
    pairing::bls12_Fp12_inv(e_inv.as_mut_ptr() as u64, e.as_ptr() as u64);

    let mut product = [0u64; FP12_WORDS];
    pairing::bls12_Fp12_mul(
        product.as_mut_ptr() as u64,
        e.as_ptr() as u64,
        e_inv.as_ptr() as u64,
    );

    assert!(
        fp12_is_one(&product),
        "e(G1,G2) * inv(e(G1,G2)) should equal 1"
    );
}
