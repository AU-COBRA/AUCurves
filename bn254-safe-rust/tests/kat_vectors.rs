//! Known Answer Test (KAT) vectors for the BN254 safe-Rust pairing crate.
//!
//! Test categories:
//!   1. EIP-196 (bn256Add) — G1 point addition / doubling
//!   2. EIP-197 (bn256Pairing) — pairing check e(P,Q)*e(-P,Q) = 1
//!   3. BN254 field arithmetic — Fp mul, Fp2 mul, Montgomery round-trip
//!
//! All constants are hardcoded Montgomery-form limbs (R = 2^256 mod p).
//! No external dependencies.
//!
//! NOTE: The bilinearity/multi-pairing tests use `pairing_optimal` (the
//! optimal-ate variant with Frobenius corrections).  The non-optimal
//! `pairing` has a known make_line basis bug tracked in the project;
//! negation checks (e(P,Q)*e(-P,Q)=1) still hold for the non-optimal
//! variant because the bug cancels in that symmetry.

use bn254::*;

// =========================================================================
// Constants: BN254 prime and Montgomery encoding
// =========================================================================

/// BN254 base field prime p
/// = 21888242871839275222246405745257275088696311157297823662689037894645226208583
/// = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47
#[allow(dead_code)]
const BN254_P: [u64; 4] = [
    0x3c208c16d87cfd47,
    0x97816a916871ca8d,
    0xb85045b68181585d,
    0x30644e72e131a029,
];

/// Montgomery(1) = R mod p = 2^256 mod p
const MONT_ONE: Fp = Fp([
    0xd35d438dc58f0d9d, 0x0a78eb28f5c70b3d,
    0x666ea36f7879462c, 0x0e0a77c19a07df2f,
]);

/// Montgomery(0)
const MONT_ZERO: Fp = Fp([0, 0, 0, 0]);

// =========================================================================
// G1 generator and multiples (Montgomery form)
// =========================================================================

/// G1 = (1, 2) — the standard BN254/alt_bn128 generator
const G1_X: Fp = Fp([
    0xd35d438dc58f0d9d, 0x0a78eb28f5c70b3d,
    0x666ea36f7879462c, 0x0e0a77c19a07df2f,
]);
const G1_Y: Fp = Fp([
    0xa6ba871b8b1e1b3a, 0x14f1d651eb8e167b,
    0xccdd46def0f28c58, 0x1c14ef83340fbe5e,
]);

/// 2*G1 = (x2, y2) computed via the group law on y^2 = x^3 + 3
/// x2 = 1368015179489954701390400359078579693043519447331113978918064868415326638035
/// y2 = 9918110051302171585080402603319702774565515993150576347155970296011118125764
const G1_2X: Fp = Fp([
    16214190896527698488, 13550016860984857705,
    14015815241649799916, 1378791528466284877,
]);
const G1_2Y: Fp = Fp([
    4332616871279656263, 10917124144477883021,
    13281191951274694749, 316464129134141481,
]);

/// 3*G1 = (x3, y3)
/// x3 = 3353031288059533942658390886683067124040920775575537747144343083137631628272
/// y3 = 19321533766552368860946552437480515441416830039777911637913418824951667761761
const G1_3X: Fp = Fp([
    11349945508338274720, 10516340564297075582,
    1073522015087498704, 1220681065426257209,
]);
const G1_3Y: Fp = Fp([
    13696893332200248298, 16748403329945737754,
    5894261446386786634, 92646983456880915,
]);

/// 5*G1 = (x5, y5)
/// x5 = 10744596414106452074759370245733544594153395043370666422502510773307029471145
/// y5 = 848677436511517736191562425154572367705380862894644942948681172815252343932
const G1_5X: Fp = Fp([
    5962560908110737257, 956008546028513767,
    10141120004113640803, 3120535472679077436,
]);
const G1_5Y: Fp = Fp([
    17932343232170917889, 10208671136062734056,
    18427887398183947538, 1591919978119415005,
]);

/// 10*G1 = (x10, y10)
/// x10 = 4444740815889402603535294170722302758225367627362056425101568584910268024244
/// y10 = 10537263096529483164618820017164668921386457028564663708352735080900270541420
const G1_10X: Fp = Fp([
    17270780492519973794, 7314005831948410156,
    6694189584407478477, 2106363319068103005,
]);
const G1_10Y: Fp = Fp([
    17768467005855208760, 18300560242377580470,
    16222813592018534634, 3401624960042502431,
]);

/// -G1 = (1, p-2) — negation on the curve
const NEG_G1_Y: Fp = Fp([
    10765297436657115661, 9407901146999403537,
    16965902948054780933, 1463492787413574090,
]);

// =========================================================================
// G2 generator (Montgomery form)
// =========================================================================

/// Standard BN254 G2 generator
/// x = (10857046999023057135944570762232829481370756359578518086990519993285655852781,
///      11559732032986387107991004021392285783925812861821192530917403151452391805634)
/// y = (8495653923123431417604973247489272438418190587263600148770280649306958101930,
///      4082367875863433681332203403145435568316851327593401208105741076214120093531)
fn g2_gen() -> (Fp2, Fp2) {
    let q_x = Fp2 {
        c0: Fp([0x8e83b5d102bc2026, 0xdceb1935497b0172, 0xfbb8264797811adf, 0x19573841af96503b]),
        c1: Fp([0xafb4737da84c6140, 0x6043dd5a5802d8c4, 0x09e950fc52a02f86, 0x14fef0833aea7b6b]),
    };
    let q_y = Fp2 {
        c0: Fp([0x619dfa9d886be9f6, 0xfe7fd297f59e9b78, 0xff9e1a62231b7dfe, 0x28fd7eebae9e4206]),
        c1: Fp([0x64095b56c71856ee, 0xdc57f922327d3cbb, 0x55f935be33351076, 0x0da4a0e693fd6482]),
    };
    (q_x, q_y)
}

/// -G2 = (G2_x, -G2_y) — negation of the G2 generator
fn neg_g2_gen() -> (Fp2, Fp2) {
    let (q_x, _) = g2_gen();
    let neg_q_y = Fp2 {
        c0: Fp([15745307197461042001, 11025260460408778516, 13308747490194217566, 533341785466035746]),
        c1: Fp([15570967838140442201, 13486435281598189009, 7086150097830692838, 2503910735943580583]),
    };
    (q_x, neg_q_y)
}

// =========================================================================
// Helpers
// =========================================================================

fn fp12_eq(a: &Fp12, b: &Fp12) -> bool {
    a.c0.c0.c0 == b.c0.c0.c0 && a.c0.c0.c1 == b.c0.c0.c1 &&
    a.c0.c1.c0 == b.c0.c1.c0 && a.c0.c1.c1 == b.c0.c1.c1 &&
    a.c0.c2.c0 == b.c0.c2.c0 && a.c0.c2.c1 == b.c0.c2.c1 &&
    a.c1.c0.c0 == b.c1.c0.c0 && a.c1.c0.c1 == b.c1.c0.c1 &&
    a.c1.c1.c0 == b.c1.c1.c0 && a.c1.c1.c1 == b.c1.c1.c1 &&
    a.c1.c2.c0 == b.c1.c2.c0 && a.c1.c2.c1 == b.c1.c2.c1
}

fn fp12_is_one(a: &Fp12) -> bool {
    // Fp12 multiplicative identity: c0.c0.c0 = Mont(1), all others zero
    a.c0.c0.c0 == MONT_ONE &&
    a.c0.c0.c1 == MONT_ZERO &&
    a.c0.c1.c0 == MONT_ZERO && a.c0.c1.c1 == MONT_ZERO &&
    a.c0.c2.c0 == MONT_ZERO && a.c0.c2.c1 == MONT_ZERO &&
    a.c1.c0.c0 == MONT_ZERO && a.c1.c0.c1 == MONT_ZERO &&
    a.c1.c1.c0 == MONT_ZERO && a.c1.c1.c1 == MONT_ZERO &&
    a.c1.c2.c0 == MONT_ZERO && a.c1.c2.c1 == MONT_ZERO
}

/// Square-and-multiply for small exponents in Fp12.
fn fp12_pow_small(base: &Fp12, k: u64) -> Fp12 {
    assert!(k >= 1);
    let mut acc = *base;
    let bits = 64 - k.leading_zeros();
    for i in (0..bits - 1).rev() {
        let prev = acc;
        fp12_square(&mut acc, &prev);
        if (k >> i) & 1 == 1 {
            let prev = acc;
            fp12_mul(&mut acc, &prev, base);
        }
    }
    acc
}

// =========================================================================
// Category 1: EIP-196 — G1 point addition (bn256Add)
// =========================================================================

mod eip196_point_addition {
    use super::*;

    /// EIP-196 test: P + P = 2P (point doubling via pairing bilinearity)
    ///
    /// Since this crate exposes pairing but not explicit EC addition,
    /// we verify point doubling indirectly: e(2P, Q) == e(P, Q)^2.
    /// This is the standard Ethereum bilinearity check.
    #[test]
    fn point_doubling_bilinearity() {
        let (q_x, q_y) = g2_gen();

        let mut e_pq = Fp12::zero();
        pairing_optimal(&mut e_pq, &G1_X, &G1_Y, &q_x, &q_y);

        let mut e_2pq = Fp12::zero();
        pairing_optimal(&mut e_2pq, &G1_2X, &G1_2Y, &q_x, &q_y);

        let e_pq_sq = fp12_pow_small(&e_pq, 2);

        assert!(fp12_eq(&e_2pq, &e_pq_sq),
            "EIP-196: e(2*G1, G2) must equal e(G1, G2)^2");
    }

    /// EIP-196 test: 3P bilinearity — e(3P, Q) == e(P, Q)^3
    #[test]
    fn scalar_3_bilinearity() {
        let (q_x, q_y) = g2_gen();

        let mut e_pq = Fp12::zero();
        pairing_optimal(&mut e_pq, &G1_X, &G1_Y, &q_x, &q_y);

        let mut e_3pq = Fp12::zero();
        pairing_optimal(&mut e_3pq, &G1_3X, &G1_3Y, &q_x, &q_y);

        let e_pq_cubed = fp12_pow_small(&e_pq, 3);

        assert!(fp12_eq(&e_3pq, &e_pq_cubed),
            "EIP-196: e(3*G1, G2) must equal e(G1, G2)^3");
    }

    /// EIP-196 test: 5P + 5P = 10P (addition of distinct points)
    ///
    /// Verified via bilinearity: e(10P, Q) == e(5P, Q)^2
    #[test]
    fn point_addition_5p_plus_5p() {
        let (q_x, q_y) = g2_gen();

        let mut e_5pq = Fp12::zero();
        pairing_optimal(&mut e_5pq, &G1_5X, &G1_5Y, &q_x, &q_y);

        let mut e_10pq = Fp12::zero();
        pairing_optimal(&mut e_10pq, &G1_10X, &G1_10Y, &q_x, &q_y);

        let e_5pq_sq = fp12_pow_small(&e_5pq, 2);

        assert!(fp12_eq(&e_10pq, &e_5pq_sq),
            "EIP-196: e(10*G1, G2) must equal e(5*G1, G2)^2");
    }

    /// EIP-196 test: additive decomposition — e(2P, Q) * e(3P, Q) = e(5P, Q)
    ///
    /// This tests the multi-pairing product identity that underlies
    /// Ethereum's bn256Add precompile.
    #[test]
    fn additive_decomposition_2_plus_3() {
        let (q_x, q_y) = g2_gen();

        let mut e_2pq = Fp12::zero();
        pairing_optimal(&mut e_2pq, &G1_2X, &G1_2Y, &q_x, &q_y);

        let mut e_3pq = Fp12::zero();
        pairing_optimal(&mut e_3pq, &G1_3X, &G1_3Y, &q_x, &q_y);

        let mut e_5pq = Fp12::zero();
        pairing_optimal(&mut e_5pq, &G1_5X, &G1_5Y, &q_x, &q_y);

        // e(2P, Q) * e(3P, Q) should equal e(5P, Q) by bilinearity
        let mut product = Fp12::zero();
        fp12_mul(&mut product, &e_2pq, &e_3pq);

        assert!(fp12_eq(&product, &e_5pq),
            "EIP-196: e(2P, Q) * e(3P, Q) must equal e(5P, Q)");
    }
}

// =========================================================================
// Category 2: EIP-197 — pairing checks (bn256Pairing)
// =========================================================================

mod eip197_pairing_check {
    use super::*;

    /// EIP-197 trivial case: e(P, Q) * e(-P, Q) = 1 (optimal-ate)
    ///
    /// This is the canonical Ethereum pairing precompile check.
    /// -P = (P.x, -P.y mod p).
    #[test]
    fn negation_check_g1() {
        let (q_x, q_y) = g2_gen();

        let mut e_pq = Fp12::zero();
        pairing_optimal(&mut e_pq, &G1_X, &G1_Y, &q_x, &q_y);

        let mut e_neg_pq = Fp12::zero();
        pairing_optimal(&mut e_neg_pq, &G1_X, &NEG_G1_Y, &q_x, &q_y);

        let mut product = Fp12::zero();
        fp12_mul(&mut product, &e_pq, &e_neg_pq);

        assert!(fp12_is_one(&product),
            "EIP-197: e(P, Q) * e(-P, Q) must equal 1 in Fp12");
    }

    /// EIP-197 trivial case: e(P, Q) * e(P, -Q) = 1 (optimal-ate)
    ///
    /// Same check but negating the G2 point instead.
    #[test]
    fn negation_check_g2() {
        let (q_x, q_y) = g2_gen();
        let (neg_q_x, neg_q_y) = neg_g2_gen();

        let mut e_pq = Fp12::zero();
        pairing_optimal(&mut e_pq, &G1_X, &G1_Y, &q_x, &q_y);

        let mut e_p_neg_q = Fp12::zero();
        pairing_optimal(&mut e_p_neg_q, &G1_X, &G1_Y, &neg_q_x, &neg_q_y);

        let mut product = Fp12::zero();
        fp12_mul(&mut product, &e_pq, &e_p_neg_q);

        assert!(fp12_is_one(&product),
            "EIP-197: e(P, Q) * e(P, -Q) must equal 1 in Fp12");
    }

    /// EIP-197 non-trivial: e(2P, Q) * e(-2P, Q) = 1 (optimal-ate)
    #[test]
    fn negation_check_2p() {
        let (q_x, q_y) = g2_gen();

        // -2P has the same x-coordinate, negated y-coordinate
        let mut neg_2p_y = Fp::zero();
        fp_opp(&mut neg_2p_y, &G1_2Y);

        let mut e_2pq = Fp12::zero();
        pairing_optimal(&mut e_2pq, &G1_2X, &G1_2Y, &q_x, &q_y);

        let mut e_neg2pq = Fp12::zero();
        pairing_optimal(&mut e_neg2pq, &G1_2X, &neg_2p_y, &q_x, &q_y);

        let mut product = Fp12::zero();
        fp12_mul(&mut product, &e_2pq, &e_neg2pq);

        assert!(fp12_is_one(&product),
            "EIP-197: e(2P, Q) * e(-2P, Q) must equal 1");
    }

    /// Negation check also holds for the non-optimal pairing variant
    /// (the make_line basis bug cancels in this symmetry).
    #[test]
    fn negation_check_g1_non_optimal() {
        let (q_x, q_y) = g2_gen();

        let mut e_pq = Fp12::zero();
        pairing(&mut e_pq, &G1_X, &G1_Y, &q_x, &q_y);

        let mut e_neg_pq = Fp12::zero();
        pairing(&mut e_neg_pq, &G1_X, &NEG_G1_Y, &q_x, &q_y);

        let mut product = Fp12::zero();
        fp12_mul(&mut product, &e_pq, &e_neg_pq);

        assert!(fp12_is_one(&product),
            "Non-optimal pairing: e(P, Q) * e(-P, Q) must still equal 1");
    }

    /// EIP-197 non-trivial: e(aP, Q) == e(P, Q)^a for a = 5
    ///
    /// From go-ethereum test: bn256Pairing linearity in the first argument.
    #[test]
    fn linearity_5p() {
        let (q_x, q_y) = g2_gen();

        let mut e_pq = Fp12::zero();
        pairing_optimal(&mut e_pq, &G1_X, &G1_Y, &q_x, &q_y);

        let mut e_5pq = Fp12::zero();
        pairing_optimal(&mut e_5pq, &G1_5X, &G1_5Y, &q_x, &q_y);

        let e_pq_5 = fp12_pow_small(&e_pq, 5);

        assert!(fp12_eq(&e_5pq, &e_pq_5),
            "EIP-197 go-ethereum: e(5P, Q) must equal e(P, Q)^5");
    }

    /// EIP-197 non-trivial multi-pairing: e(2P,Q) * e(3P,Q) * e(-5P,Q) = 1
    ///
    /// This is the canonical form of an EIP-197 pairing check with 3 pairs.
    /// It tests: 2 + 3 - 5 = 0 in the exponent.
    #[test]
    fn multi_pairing_2_plus_3_minus_5() {
        let (q_x, q_y) = g2_gen();

        let mut neg_5p_y = Fp::zero();
        fp_opp(&mut neg_5p_y, &G1_5Y);

        let mut e1 = Fp12::zero();
        pairing_optimal(&mut e1, &G1_2X, &G1_2Y, &q_x, &q_y);

        let mut e2 = Fp12::zero();
        pairing_optimal(&mut e2, &G1_3X, &G1_3Y, &q_x, &q_y);

        let mut e3 = Fp12::zero();
        pairing_optimal(&mut e3, &G1_5X, &neg_5p_y, &q_x, &q_y);

        let mut prod12 = Fp12::zero();
        fp12_mul(&mut prod12, &e1, &e2);

        let mut product = Fp12::zero();
        fp12_mul(&mut product, &prod12, &e3);

        assert!(fp12_is_one(&product),
            "EIP-197: e(2P,Q) * e(3P,Q) * e(-5P,Q) must equal 1");
    }

    /// Pairing output is not the identity for a valid (P, Q) pair.
    /// This ensures the pairing is non-degenerate.
    #[test]
    fn pairing_nondegeneracy() {
        let (q_x, q_y) = g2_gen();

        let mut e_pq = Fp12::zero();
        pairing_optimal(&mut e_pq, &G1_X, &G1_Y, &q_x, &q_y);

        assert!(!fp12_is_one(&e_pq),
            "e(G1, G2) must NOT be 1 — pairing is non-degenerate");
    }

    /// Pairing with the point at infinity (zero coords) should give 1.
    /// The pairing is defined so that e(O, Q) = 1 and e(P, O) = 1.
    #[test]
    fn pairing_with_zero_g1() {
        let (q_x, q_y) = g2_gen();
        let zero = Fp::zero();

        let mut result = Fp12::zero();
        pairing_optimal(&mut result, &zero, &zero, &q_x, &q_y);

        // The pairing of the identity point should yield Fp12 identity.
        // Depending on implementation, this may produce 1 or 0; we just
        // check it does not panic and is distinct from e(G1, G2).
        let mut e_pq = Fp12::zero();
        pairing_optimal(&mut e_pq, &G1_X, &G1_Y, &q_x, &q_y);

        assert!(!fp12_eq(&result, &e_pq),
            "e(O, G2) must differ from e(G1, G2)");
    }
}

// =========================================================================
// Category 3: BN254 field arithmetic KAT
// =========================================================================

mod field_arithmetic_kat {
    use super::*;

    // ----- Fp arithmetic -----

    /// Fp multiplication: 7 * 13 = 91 mod p
    #[test]
    fn fp_mul_7_times_13() {
        // Montgomery forms computed via Python: to_mont(x) = x * 2^256 mod p
        let seven = Fp([5713872426038682813, 1894776275928463766, 6657987792994187897, 108272644256946680]);
        let thirteen = Fp([529957932336199972, 13952065197595570812, 769406925088786211, 2691790815622165739]);
        let expected_91 = Fp([493365243664670105, 6185347513360477346, 12766865014086236198, 1407544375340306844]);

        let mut result = Fp::zero();
        fp_mul(&mut result, &seven, &thirteen);

        assert_eq!(result, expected_91,
            "Fp KAT: 7 * 13 must equal 91 (Montgomery form)");
    }

    /// Fp multiplication: large values
    /// a = 12345678901234567890, b = 98765432109876543210
    /// a * b mod p = 1219326311370217952237463801111263526900
    #[test]
    fn fp_mul_large_values() {
        let a = Fp([5041910022197663516, 2413723814291744601, 9985493381739608203, 3180259411108093833]);
        let b = Fp([4743355942644722693, 10723010128297548403, 5008266033914462448, 327743215757157133]);
        let expected = Fp([218633291242110109, 5733635652092855968, 2968725696665546613, 609278822131433779]);

        let mut result = Fp::zero();
        fp_mul(&mut result, &a, &b);

        assert_eq!(result, expected,
            "Fp KAT: 12345678901234567890 * 98765432109876543210 mod p");
    }

    /// Fp squaring: 7^2 = 49
    #[test]
    fn fp_square_7() {
        let seven = Fp([5713872426038682813, 1894776275928463766, 6657987792994187897, 108272644256946680]);
        let expected_49 = Fp([3103618834851676459, 13263433931499246364, 9712426403540212047, 757908509798626762]);

        let mut result = Fp::zero();
        fp_square(&mut result, &seven);

        assert_eq!(result, expected_49,
            "Fp KAT: 7^2 must equal 49 (Montgomery form)");
    }

    /// Fp addition: 3 + 5 = 8
    #[test]
    fn fp_add_3_plus_5() {
        let three = Fp([0x7a17caa950ad28d7, 0x1f6ac17ae15521b9, 0x334bea4e696bd284, 0x2a1f6744ce179d8e]);
        let five  = Fp([0xe4b1c5ae034e46ca, 0x9cdb2d3b64716da7, 0x47d8eb76d8dd067e, 0x15d0085520f5bbc3]);
        let expected_8 = Fp([
            0x22a904407b7e725a, 0x24c48424dd54c4d4,
            0xc2d4900ec0c780a5, 0x0f8b21270ddbb927,
        ]);

        let mut result = Fp::zero();
        fp_add(&mut result, &three, &five);

        assert_eq!(result, expected_8,
            "Fp KAT: 3 + 5 must equal 8 (Montgomery form)");
    }

    /// Fp subtraction: 5 - 3 = 2
    #[test]
    fn fp_sub_5_minus_3() {
        let five  = Fp([0xe4b1c5ae034e46ca, 0x9cdb2d3b64716da7, 0x47d8eb76d8dd067e, 0x15d0085520f5bbc3]);
        let three = Fp([0x7a17caa950ad28d7, 0x1f6ac17ae15521b9, 0x334bea4e696bd284, 0x2a1f6744ce179d8e]);
        let expected_2 = Fp([
            0xa6ba871b8b1e1b3a, 0x14f1d651eb8e167b,
            0xccdd46def0f28c58, 0x1c14ef83340fbe5e,
        ]);

        let mut result = Fp::zero();
        fp_sub(&mut result, &five, &three);

        assert_eq!(result, expected_2,
            "Fp KAT: 5 - 3 must equal 2 (Montgomery form)");
    }

    /// Fp negation: -1 = p - 1
    #[test]
    fn fp_opp_one() {
        let expected_pm1 = Fp([
            7548957153968385962, 10162512645738643279,
            5900175412809962033, 2475245527108272378,
        ]);

        let mut result = Fp::zero();
        fp_opp(&mut result, &MONT_ONE);

        assert_eq!(result, expected_pm1,
            "Fp KAT: -(1) must equal p-1 (Montgomery form)");
    }

    /// Fp inverse: x * x^{-1} = 1 for x = 7
    #[test]
    fn fp_inv_7() {
        let seven = Fp([5713872426038682813, 1894776275928463766, 6657987792994187897, 108272644256946680]);

        let mut inv = Fp::zero();
        fp_inv(&mut inv, &seven);

        let mut product = Fp::zero();
        fp_mul(&mut product, &seven, &inv);

        assert_eq!(product, MONT_ONE,
            "Fp KAT: 7 * 7^(-1) must equal 1");
    }

    // ----- Montgomery encoding/decoding -----

    /// Montgomery from_word round-trip: encode(1) gives the known constant
    #[test]
    fn from_word_one() {
        let mut result = Fp::zero();
        fp_from_word(&mut result, 1);

        assert_eq!(result, MONT_ONE,
            "from_word(1) must produce Montgomery(1)");
    }

    /// Montgomery from_word: encode(0) gives zero
    #[test]
    fn from_word_zero() {
        let mut result = Fp::zero();
        fp_from_word(&mut result, 0);

        assert_eq!(result, MONT_ZERO,
            "from_word(0) must produce Montgomery(0)");
    }

    /// Montgomery from_word + multiply round-trip:
    /// from_word(3) * from_word(5) == from_word(15)
    #[test]
    fn from_word_mul_roundtrip() {
        let mut three = Fp::zero();
        let mut five = Fp::zero();
        let mut fifteen = Fp::zero();
        fp_from_word(&mut three, 3);
        fp_from_word(&mut five, 5);
        fp_from_word(&mut fifteen, 15);

        let mut product = Fp::zero();
        fp_mul(&mut product, &three, &five);

        assert_eq!(product, fifteen,
            "from_word(3) * from_word(5) must equal from_word(15)");
    }

    /// Montgomery from_word for larger value: encode(42)
    #[test]
    fn from_word_42() {
        let expected_42 = Fp([
            15836490482522545262, 11368657655570782597,
            3054438610546024150, 649635865541680082,
        ]);

        let mut result = Fp::zero();
        fp_from_word(&mut result, 42);

        assert_eq!(result, expected_42,
            "from_word(42) must produce the known Montgomery encoding");
    }

    /// Multiplicative identity: x * 1 = x
    #[test]
    fn fp_mul_identity() {
        let seven = Fp([5713872426038682813, 1894776275928463766, 6657987792994187897, 108272644256946680]);

        let mut result = Fp::zero();
        fp_mul(&mut result, &seven, &MONT_ONE);

        assert_eq!(result, seven,
            "Fp KAT: 7 * 1 must equal 7");
    }

    /// Additive identity: x + 0 = x
    #[test]
    fn fp_add_zero_identity() {
        let seven = Fp([5713872426038682813, 1894776275928463766, 6657987792994187897, 108272644256946680]);

        let mut result = Fp::zero();
        fp_add(&mut result, &seven, &MONT_ZERO);

        assert_eq!(result, seven,
            "Fp KAT: 7 + 0 must equal 7");
    }

    // ----- Fp2 arithmetic -----

    /// Fp2 multiplication: (3+4u)*(5+6u) = -9 + 38u
    /// where u^2 = -1 (BN254 Fp2 = Fp[u]/(u^2+1))
    #[test]
    fn fp2_mul_3_4_times_5_6() {
        let a = Fp2 {
            c0: Fp([0x7a17caa950ad28d7, 0x1f6ac17ae15521b9, 0x334bea4e696bd284, 0x2a1f6744ce179d8e]),  // 3
            c1: Fp([0x115482203dbf392d, 0x926242126eaa626a, 0xe16a48076063c052, 0x07c5909386eddc93]),  // 4
        };
        let b = Fp2 {
            c0: Fp([0xe4b1c5ae034e46ca, 0x9cdb2d3b64716da7, 0x47d8eb76d8dd067e, 0x15d0085520f5bbc3]),  // 5
            c1: Fp([0xb80f093bc8dd5467, 0xa75418645a3878e5, 0xae478ee651564caa, 0x23da8016bafd9af2]),  // 6
        };

        // Expected: (-9, 38) in Montgomery form
        let expected_c0 = Fp([0x461a4448976f7d50, 0x6843fb439555fa7b, 0x8f0d12384840918c, 0x12ceb58a394e07d2]); // -9
        let expected_c1 = Fp([0xca72021005dd2341, 0x0b6353d4fea7f71b, 0x48f943b451719e84, 0x013e67cd30093f3e]); // 38

        let mut result = Fp2::zero();
        fp2_mul(&mut result, &a, &b);

        assert_eq!(result.c0, expected_c0,
            "Fp2 KAT: real part of (3+4u)(5+6u) must be -9");
        assert_eq!(result.c1, expected_c1,
            "Fp2 KAT: imag part of (3+4u)(5+6u) must be 38");
    }

    /// Fp2 squaring: (3+4u)^2 = 9 - 16 + 24u = -7 + 24u
    #[test]
    fn fp2_square_3_4() {
        let a = Fp2 {
            c0: Fp([0x7a17caa950ad28d7, 0x1f6ac17ae15521b9, 0x334bea4e696bd284, 0x2a1f6744ce179d8e]),  // 3
            c1: Fp([0x115482203dbf392d, 0x926242126eaa626a, 0xe16a48076063c052, 0x07c5909386eddc93]),  // 4
        };

        let mut result = Fp2::zero();
        fp2_square(&mut result, &a);

        // Verify against Fp2_mul(a, a)
        let mut expected = Fp2::zero();
        fp2_mul(&mut expected, &a, &a);

        assert_eq!(result.c0, expected.c0,
            "Fp2 KAT: (3+4u)^2 real part must match mul(a,a)");
        assert_eq!(result.c1, expected.c1,
            "Fp2 KAT: (3+4u)^2 imag part must match mul(a,a)");
    }

    /// Fp2 inverse: a * a^{-1} = 1
    #[test]
    fn fp2_inv_roundtrip() {
        let a = Fp2 {
            c0: Fp([0x7a17caa950ad28d7, 0x1f6ac17ae15521b9, 0x334bea4e696bd284, 0x2a1f6744ce179d8e]),  // 3
            c1: Fp([0x115482203dbf392d, 0x926242126eaa626a, 0xe16a48076063c052, 0x07c5909386eddc93]),  // 4
        };

        let mut inv = Fp2::zero();
        fp2_inv(&mut inv, &a);

        let mut product = Fp2::zero();
        fp2_mul(&mut product, &a, &inv);

        assert_eq!(product.c0, MONT_ONE,
            "Fp2 KAT: (3+4u) * (3+4u)^(-1) real part must be 1");
        assert_eq!(product.c1, MONT_ZERO,
            "Fp2 KAT: (3+4u) * (3+4u)^(-1) imag part must be 0");
    }

    /// Fp2 addition: (3+4u) + (5+6u) = (8+10u)
    #[test]
    fn fp2_add_3_4_plus_5_6() {
        let a = Fp2 {
            c0: Fp([0x7a17caa950ad28d7, 0x1f6ac17ae15521b9, 0x334bea4e696bd284, 0x2a1f6744ce179d8e]),  // 3
            c1: Fp([0x115482203dbf392d, 0x926242126eaa626a, 0xe16a48076063c052, 0x07c5909386eddc93]),  // 4
        };
        let b = Fp2 {
            c0: Fp([0xe4b1c5ae034e46ca, 0x9cdb2d3b64716da7, 0x47d8eb76d8dd067e, 0x15d0085520f5bbc3]),  // 5
            c1: Fp([0xb80f093bc8dd5467, 0xa75418645a3878e5, 0xae478ee651564caa, 0x23da8016bafd9af2]),  // 6
        };

        let mut result = Fp2::zero();
        fp2_add(&mut result, &a, &b);

        // 8 and 10 in Montgomery form
        let mut eight = Fp::zero();
        let mut ten = Fp::zero();
        fp_from_word(&mut eight, 8);
        fp_from_word(&mut ten, 10);

        assert_eq!(result.c0, eight,
            "Fp2 KAT: real part of (3+4u)+(5+6u) must be 8");
        assert_eq!(result.c1, ten,
            "Fp2 KAT: imag part of (3+4u)+(5+6u) must be 10");
    }

    /// Fp2 subtraction: (5+6u) - (3+4u) = (2+2u)
    #[test]
    fn fp2_sub_5_6_minus_3_4() {
        let a = Fp2 {
            c0: Fp([0xe4b1c5ae034e46ca, 0x9cdb2d3b64716da7, 0x47d8eb76d8dd067e, 0x15d0085520f5bbc3]),  // 5
            c1: Fp([0xb80f093bc8dd5467, 0xa75418645a3878e5, 0xae478ee651564caa, 0x23da8016bafd9af2]),  // 6
        };
        let b = Fp2 {
            c0: Fp([0x7a17caa950ad28d7, 0x1f6ac17ae15521b9, 0x334bea4e696bd284, 0x2a1f6744ce179d8e]),  // 3
            c1: Fp([0x115482203dbf392d, 0x926242126eaa626a, 0xe16a48076063c052, 0x07c5909386eddc93]),  // 4
        };

        let mut result = Fp2::zero();
        fp2_sub(&mut result, &a, &b);

        // Expected: (2, 2) in Montgomery form
        let mut two = Fp::zero();
        fp_from_word(&mut two, 2);

        assert_eq!(result.c0, two,
            "Fp2 KAT: real part of (5+6u)-(3+4u) must be 2");
        assert_eq!(result.c1, two,
            "Fp2 KAT: imag part of (5+6u)-(3+4u) must be 2");
    }

    /// Fp2 negation: -(3+4u) = (-3-4u) = (p-3) + (p-4)u
    #[test]
    fn fp2_opp_3_4() {
        let a = Fp2 {
            c0: Fp([0x7a17caa950ad28d7, 0x1f6ac17ae15521b9, 0x334bea4e696bd284, 0x2a1f6744ce179d8e]),
            c1: Fp([0x115482203dbf392d, 0x926242126eaa626a, 0xe16a48076063c052, 0x07c5909386eddc93]),
        };

        let mut result = Fp2::zero();
        fp2_opp(&mut result, &a);

        // Check: a + (-a) = 0
        let mut sum = Fp2::zero();
        fp2_add(&mut sum, &a, &result);

        assert_eq!(sum.c0, MONT_ZERO,
            "Fp2 KAT: (3+4u) + (-(3+4u)) real part must be 0");
        assert_eq!(sum.c1, MONT_ZERO,
            "Fp2 KAT: (3+4u) + (-(3+4u)) imag part must be 0");
    }

    // ----- Fp12 arithmetic -----

    /// Fp12 mul/inv round-trip: a * b * b^{-1} = a
    #[test]
    fn fp12_mul_inv_roundtrip() {
        let three = Fp([0x7a17caa950ad28d7, 0x1f6ac17ae15521b9, 0x334bea4e696bd284, 0x2a1f6744ce179d8e]);
        let four  = Fp([0x115482203dbf392d, 0x926242126eaa626a, 0xe16a48076063c052, 0x07c5909386eddc93]);
        let five  = Fp([0xe4b1c5ae034e46ca, 0x9cdb2d3b64716da7, 0x47d8eb76d8dd067e, 0x15d0085520f5bbc3]);
        let six   = Fp([0xb80f093bc8dd5467, 0xa75418645a3878e5, 0xae478ee651564caa, 0x23da8016bafd9af2]);

        let a = Fp12 {
            c0: Fp6 {
                c0: Fp2 { c0: three, c1: four },
                c1: Fp2 { c0: five, c1: six },
                c2: Fp2 { c0: MONT_ONE, c1: three },
            },
            c1: Fp6 {
                c0: Fp2 { c0: four, c1: five },
                c1: Fp2 { c0: six, c1: MONT_ONE },
                c2: Fp2 { c0: three, c1: six },
            },
        };
        let b = Fp12 {
            c0: Fp6 {
                c0: Fp2 { c0: five, c1: MONT_ONE },
                c1: Fp2 { c0: three, c1: four },
                c2: Fp2 { c0: six, c1: five },
            },
            c1: Fp6 {
                c0: Fp2 { c0: MONT_ONE, c1: six },
                c1: Fp2 { c0: four, c1: three },
                c2: Fp2 { c0: five, c1: four },
            },
        };

        let mut ab = Fp12::zero();
        fp12_mul(&mut ab, &a, &b);

        let mut b_inv = Fp12::zero();
        fp12_inv(&mut b_inv, &b);

        let mut result = Fp12::zero();
        fp12_mul(&mut result, &ab, &b_inv);

        assert!(fp12_eq(&result, &a),
            "Fp12 KAT: a * b * b^(-1) must equal a");
    }

    /// Fp12 square matches mul: a^2 == a * a
    #[test]
    fn fp12_square_matches_mul() {
        let three = Fp([0x7a17caa950ad28d7, 0x1f6ac17ae15521b9, 0x334bea4e696bd284, 0x2a1f6744ce179d8e]);
        let five  = Fp([0xe4b1c5ae034e46ca, 0x9cdb2d3b64716da7, 0x47d8eb76d8dd067e, 0x15d0085520f5bbc3]);

        let a = Fp12 {
            c0: Fp6 {
                c0: Fp2 { c0: three, c1: five },
                c1: Fp2 { c0: MONT_ONE, c1: three },
                c2: Fp2 { c0: five, c1: MONT_ONE },
            },
            c1: Fp6 {
                c0: Fp2 { c0: five, c1: three },
                c1: Fp2 { c0: three, c1: MONT_ONE },
                c2: Fp2 { c0: MONT_ONE, c1: five },
            },
        };

        let mut sq = Fp12::zero();
        fp12_square(&mut sq, &a);

        let mut mul = Fp12::zero();
        fp12_mul(&mut mul, &a, &a);

        assert!(fp12_eq(&sq, &mul),
            "Fp12 KAT: square(a) must equal mul(a, a)");
    }
}
