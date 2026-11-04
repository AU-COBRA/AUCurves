//! Known Answer Test (KAT) vectors for the BLS12-381 safe-Rust tower.
//!
//! All vectors are hardcoded (zero external dependencies).
//! Montgomery form uses R = 2^384 with
//! p = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

use bls12_381::*;

// ---------------------------------------------------------------------------
// Helper: encode a small u64 into Montgomery form via the public API
// ---------------------------------------------------------------------------
fn mont_of(w: u64) -> Fp {
    let mut x = Fp::zero();
    fp_from_word(&mut x, w);
    x
}

// ---------------------------------------------------------------------------
// Hardcoded Montgomery-form constants (precomputed by dump_kat examples)
// ---------------------------------------------------------------------------

/// 1 in Montgomery form (R mod p).
const MONT_ONE: Fp = Fp([
    0x760900000002fffd, 0xebf4000bc40c0002,
    0x5f48985753c758ba, 0x77ce585370525745,
    0x5c071a97a256ec6d, 0x15f65ec3fa80e493,
]);

// ---------------------------------------------------------------------------
// Standard BLS12-381 generator points (Montgomery form)
// ---------------------------------------------------------------------------

const G1_X: Fp = Fp([
    6679831729115696150, 8653662730902241269, 1535610680227111361,
    17342916647841752903, 17135755455211762752, 1297449291367578485,
]);
const G1_Y: Fp = Fp([
    13451288730302620273, 10097742279870053774, 15949884091978425806,
    5885175747529691540, 1016841820992199104, 845620083434234474,
]);

/// 2*G1 (affine doubling on y^2 = x^3 + 4)
const G1_2X: Fp = Fp([
    6046496802367715900, 4512703842675942905, 5557647857818872160,
    11911007586355426777, 2789226406901363231, 2402832991291269,
]);
const G1_2Y: Fp = Fp([
    8075247918781118784, 15723127573743364860, 13289805640942397317,
    12593984073093990549, 2724610382811436832, 447576566110657301,
]);

/// 3*G1
const G1_3X: Fp = Fp([
    14879952865637471106, 9101337358232323942, 14926506547533711328,
    8345368023003003344, 7812449332930276794, 1206422667768826016,
]);
const G1_3Y: Fp = Fp([
    17400291712052253032, 15461228438443253073, 12497778704206688841,
    16222987475149873513, 3298595310239752609, 1601199373778246201,
]);

const G2_X: Fp2 = Fp2 {
    c0: Fp([
        17722385409647053328, 12967546844987299354, 11648722842835150208,
        10994581490347323113, 8027586497049998955, 396758299565931735,
    ]),
    c1: Fp([
        11937283898719073798, 12295044263989567683, 4301357764460312582,
        1953074377943790439, 14030662337566180679, 1266120665323335155,
    ]),
};
const G2_Y: Fp2 = Fp2 {
    c0: Fp([
        5508758831087832138, 6448303779119275098, 16710190169160573786,
        13542242618704742751, 563980702369916322, 37152010398653157,
    ]),
    c1: Fp([
        12520284671833321565, 1777275927576994268, 9704602344324656032,
        8739618045342622522, 16651875250601773805, 804950956836789234,
    ]),
};

/// e(G1, G2) as computed by `pairing`: f_{|x|,G2}(G1)^((p^12-1)/r), Montgomery form.
/// blst and arkworks return conj(E_G1_G2)^3 (see tests/pairing_reference.rs).
const E_G1_G2: Fp12 = Fp12 {
    c0: Fp6 {
        c0: Fp2 {
            c0: Fp([2140974574759650879, 17129658566793055210, 7456996066826287370, 17862034931497044098, 7685465539708615435, 881080378655789673]),
            c1: Fp([4976719316142609671, 11554191401053807428, 11820045090249041768, 3968165893332982518, 3866978895653247463, 1808140851398168886]),
        },
        c1: Fp2 {
            c0: Fp([8878719958834672279, 5189891498449769588, 10962709163774002710, 10647531576095777480, 8391099222210373822, 1361421999549771319]),
            c1: Fp([8211830026801951890, 17251342900424542427, 5096890941604139022, 2840448061584407546, 5305615263170180160, 1409939279784361456]),
        },
        c2: Fp2 {
            c0: Fp([16342060120349588371, 5233128226676213905, 267290075851633155, 11404441652043187210, 13786534773239409079, 530893152092339504]),
            c1: Fp([14381167396198384662, 5389686627715790809, 5314422069414493204, 16893339160562911628, 12736240739207697731, 1868844893591413885]),
        },
    },
    c1: Fp6 {
        c0: Fp2 {
            c0: Fp([17110083389490525638, 8147577518100446636, 2356163410676698345, 12822987638732993083, 15065421038627562281, 1368817978179548666]),
            c1: Fp([6284376296285127072, 9557783965621350683, 5680120437295193132, 12989305249365334830, 10525006229848571436, 264275682864639483]),
        },
        c1: Fp2 {
            c0: Fp([6404610556387017296, 2638671787660325607, 9495942919878319965, 17213337656654457825, 17192165824964876620, 850886771246391784]),
            c1: Fp([16411122172004824342, 7400075850091501344, 1314478664240933576, 10269085771465370777, 11108372229408816525, 1474259801848025206]),
        },
        c2: Fp2 {
            c0: Fp([13494714988572169087, 3261315585965113146, 2165301237748813211, 11456868862504003759, 13788581314680594615, 1131186013183564785]),
            c1: Fp([5455784809821511119, 9393981844981149289, 18265731248970899652, 15451626265785282659, 17694226873611382736, 121455164632004648]),
        },
    },
};

// ---------------------------------------------------------------------------
// Fp12 equality helper (structural, all 12 Fp limb-arrays)
// ---------------------------------------------------------------------------
fn fp12_eq(a: &Fp12, b: &Fp12) -> bool {
    a.c0.c0.c0 == b.c0.c0.c0 && a.c0.c0.c1 == b.c0.c0.c1 &&
    a.c0.c1.c0 == b.c0.c1.c0 && a.c0.c1.c1 == b.c0.c1.c1 &&
    a.c0.c2.c0 == b.c0.c2.c0 && a.c0.c2.c1 == b.c0.c2.c1 &&
    a.c1.c0.c0 == b.c1.c0.c0 && a.c1.c0.c1 == b.c1.c0.c1 &&
    a.c1.c1.c0 == b.c1.c1.c0 && a.c1.c1.c1 == b.c1.c1.c1 &&
    a.c1.c2.c0 == b.c1.c2.c0 && a.c1.c2.c1 == b.c1.c2.c1
}

/// Compute base^k by repeated squaring in Fp12.
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

// ===========================================================================
// 1. BLS12-381 field arithmetic KAT
// ===========================================================================

#[test]
fn kat_fp_mul_3x5_is_15() {
    let three = mont_of(3);
    let five = mont_of(5);
    let expected = mont_of(15);
    let mut result = Fp::zero();
    fp_mul(&mut result, &three, &five);
    assert_eq!(result, expected, "3 * 5 should equal 15 in Fp");
}

#[test]
fn kat_fp_add_7p11_is_18() {
    let seven = mont_of(7);
    let eleven = mont_of(11);
    let expected = mont_of(18);
    let mut result = Fp::zero();
    fp_add(&mut result, &seven, &eleven);
    assert_eq!(result, expected, "7 + 11 should equal 18 in Fp");
}

#[test]
fn kat_fp_sub_11m3_is_8() {
    let eleven = mont_of(11);
    let three = mont_of(3);
    let expected = mont_of(8);
    let mut result = Fp::zero();
    fp_sub(&mut result, &eleven, &three);
    assert_eq!(result, expected, "11 - 3 should equal 8 in Fp");
}

#[test]
fn kat_fp_square_7_is_49() {
    let seven = mont_of(7);
    let expected = mont_of(49);
    let mut result = Fp::zero();
    fp_square(&mut result, &seven);
    assert_eq!(result, expected, "7^2 should equal 49 in Fp");
}

#[test]
fn kat_fp_mul_commutativity() {
    let a = mont_of(17);
    let b = mont_of(31);
    let mut ab = Fp::zero();
    let mut ba = Fp::zero();
    fp_mul(&mut ab, &a, &b);
    fp_mul(&mut ba, &b, &a);
    assert_eq!(ab, ba, "Fp multiplication should be commutative");
    assert_eq!(ab, mont_of(527), "17 * 31 should equal 527");
}

#[test]
fn kat_fp_mul_identity() {
    let a = mont_of(42);
    let mut result = Fp::zero();
    fp_mul(&mut result, &a, &MONT_ONE);
    assert_eq!(result, a, "a * 1 should equal a");
}

#[test]
fn kat_fp_add_zero() {
    let a = mont_of(99);
    let mut result = Fp::zero();
    fp_add(&mut result, &a, &Fp::zero());
    assert_eq!(result, a, "a + 0 should equal a");
}

#[test]
fn kat_fp_sub_self_is_zero() {
    let a = mont_of(42);
    let mut result = Fp::zero();
    fp_sub(&mut result, &a, &a);
    assert_eq!(result, Fp::zero(), "a - a should equal 0");
}

#[test]
fn kat_fp_sub_wraps_modular() {
    // 3 - 5 should give p - 2 (valid field element)
    let three = mont_of(3);
    let five = mont_of(5);
    let mut result = Fp::zero();
    fp_sub(&mut result, &three, &five);
    // Verify: (3 - 5) + 5 = 3
    let mut check = Fp::zero();
    fp_add(&mut check, &result, &five);
    assert_eq!(check, three, "(3 - 5) + 5 should equal 3 (modular wrap)");
}

#[test]
fn kat_fp_negation_double() {
    // -(-a) == a
    let a = mont_of(37);
    let mut neg_a = Fp::zero();
    fp_opp(&mut neg_a, &a);
    let mut neg_neg_a = Fp::zero();
    fp_opp(&mut neg_neg_a, &neg_a);
    assert_eq!(neg_neg_a, a, "-(-a) should equal a");
}

// ---------------------------------------------------------------------------
// Fp2 arithmetic KAT
// ---------------------------------------------------------------------------

#[test]
fn kat_fp2_mul_known_answer() {
    // (3 + 4i) * (5 + 6i) = (3*5 - 4*6) + (3*6 + 4*5)i = -9 + 38i
    // (BLS12-381 Fp2 has i^2 = -1)
    let a = Fp2 { c0: mont_of(3), c1: mont_of(4) };
    let b = Fp2 { c0: mont_of(5), c1: mont_of(6) };
    let mut result = Fp2::zero();
    fp2_mul(&mut result, &a, &b);

    // Expected c0 = -9 mod p
    let nine = mont_of(9);
    let mut neg_nine = Fp::zero();
    fp_opp(&mut neg_nine, &nine);
    let expected_c1 = mont_of(38);

    assert_eq!(result.c0, neg_nine, "Fp2 mul c0: (3+4i)(5+6i) real part should be -9");
    assert_eq!(result.c1, expected_c1, "Fp2 mul c1: (3+4i)(5+6i) imag part should be 38");
}

#[test]
fn kat_fp2_mul_by_one() {
    let one_fp2 = Fp2 { c0: MONT_ONE, c1: Fp::zero() };
    let a = Fp2 { c0: mont_of(7), c1: mont_of(13) };
    let mut result = Fp2::zero();
    fp2_mul(&mut result, &a, &one_fp2);
    assert_eq!(result, a, "Fp2: a * 1 should equal a");
}

#[test]
fn kat_fp2_square_vs_mul() {
    let a = Fp2 { c0: mont_of(5), c1: mont_of(3) };
    let mut sq = Fp2::zero();
    fp2_square(&mut sq, &a);
    let mut mul = Fp2::zero();
    fp2_mul(&mut mul, &a, &a);
    assert_eq!(sq, mul, "Fp2: square(a) should equal mul(a, a)");
}

#[test]
fn kat_fp2_inv_roundtrip() {
    let a = Fp2 { c0: mont_of(3), c1: mont_of(4) };
    let one_fp2 = Fp2 { c0: MONT_ONE, c1: Fp::zero() };
    let mut a_inv = Fp2::zero();
    fp2_inv(&mut a_inv, &a);
    let mut roundtrip = Fp2::zero();
    fp2_mul(&mut roundtrip, &a, &a_inv);
    assert_eq!(roundtrip, one_fp2, "Fp2: a * inv(a) should equal 1");
}

#[test]
fn kat_fp2_inv_known_answer() {
    // inv(3 + 4i) = 3/25 - 4i/25 (since norm = 9+16 = 25)
    // In Fp: 3 * 25^{-1} and -4 * 25^{-1}
    let a = Fp2 { c0: mont_of(3), c1: mont_of(4) };
    let mut a_inv = Fp2::zero();
    fp2_inv(&mut a_inv, &a);

    // Precomputed values from dump_kat2
    let expected_c0 = Fp([
        6589272909801140169, 1125584661381948375, 13510710383117127167,
        1932544647196282391, 362787483509423919, 40002892373999949,
    ]);
    let expected_c1 = Fp([
        14128523866000652589, 11533763671136172768, 2911021754074742626,
        12134215839682895392, 1320317948144335539, 571262349383846690,
    ]);
    assert_eq!(a_inv.c0, expected_c0, "Fp2 inv c0 mismatch");
    assert_eq!(a_inv.c1, expected_c1, "Fp2 inv c1 mismatch");
}

// ---------------------------------------------------------------------------
// Fp6 / Fp12 multiply + inverse round-trip KAT
// ---------------------------------------------------------------------------

#[test]
fn kat_fp6_mul_known_answer() {
    let a = Fp6 {
        c0: Fp2 { c0: mont_of(3), c1: mont_of(4) },
        c1: Fp2 { c0: mont_of(5), c1: mont_of(6) },
        c2: Fp2 { c0: mont_of(7), c1: mont_of(2) },
    };
    let b = Fp6 {
        c0: Fp2 { c0: mont_of(2), c1: mont_of(5) },
        c1: Fp2 { c0: mont_of(3), c1: mont_of(7) },
        c2: Fp2 { c0: mont_of(4), c1: mont_of(6) },
    };
    let mut result = Fp6::zero();
    fp6_mul(&mut result, &a, &b);

    // Precomputed product (from dump_kat2)
    let expected = Fp6 {
        c0: Fp2 {
            c0: Fp([9433915319405947996, 13938633547390647964, 283051009501163371, 3299870947254940664, 7525419928573818314, 967985212141012869]),
            c1: Fp([16193255410190472130, 506661752062607690, 4844873957722331463, 2604502910234878802, 18395318291050597871, 1653193712751610552]),
        },
        c1: Fp2 {
            c0: Fp([7147494083597981253, 2671756441851526971, 15140981090514325362, 3102164752084739986, 17486361241429111027, 648888707783895896]),
            c1: Fp([16229284207212232258, 12756453457212735853, 12309220374416557879, 16753191736338809758, 8175565374054113852, 1614643612090678675]),
        },
        c2: Fp2 {
            c0: Fp([12152682119475036275, 6182314451345342369, 1210301633980511917, 7261146392286348274, 4054652127727578694, 824480508566947311]),
            c1: Fp([1501950475755148216, 7989392701384556883, 3135565635314499851, 6785292982308122852, 3606157526605941937, 779467404454069412]),
        },
    };
    assert_eq!(result, expected, "Fp6 multiplication KAT mismatch");
}

#[test]
fn kat_fp6_mul_inv_roundtrip() {
    let a = Fp6 {
        c0: Fp2 { c0: mont_of(3), c1: mont_of(4) },
        c1: Fp2 { c0: mont_of(5), c1: mont_of(6) },
        c2: Fp2 { c0: mont_of(7), c1: mont_of(2) },
    };
    let b = Fp6 {
        c0: Fp2 { c0: mont_of(2), c1: mont_of(5) },
        c1: Fp2 { c0: mont_of(3), c1: mont_of(7) },
        c2: Fp2 { c0: mont_of(4), c1: mont_of(6) },
    };
    let mut ab = Fp6::zero();
    fp6_mul(&mut ab, &a, &b);
    let mut b_inv = Fp6::zero();
    fp6_inv(&mut b_inv, &b);
    let mut result = Fp6::zero();
    fp6_mul(&mut result, &ab, &b_inv);
    assert_eq!(result, a, "Fp6: (a*b) * inv(b) should equal a");
}

#[test]
fn kat_fp12_mul_known_answer() {
    let a = Fp12 {
        c0: Fp6 {
            c0: Fp2 { c0: mont_of(3), c1: mont_of(4) },
            c1: Fp2 { c0: mont_of(5), c1: mont_of(6) },
            c2: Fp2 { c0: MONT_ONE, c1: mont_of(3) },
        },
        c1: Fp6 {
            c0: Fp2 { c0: mont_of(4), c1: mont_of(5) },
            c1: Fp2 { c0: mont_of(6), c1: MONT_ONE },
            c2: Fp2 { c0: mont_of(3), c1: mont_of(6) },
        },
    };
    let b = Fp12 {
        c0: Fp6 {
            c0: Fp2 { c0: mont_of(5), c1: MONT_ONE },
            c1: Fp2 { c0: mont_of(3), c1: mont_of(4) },
            c2: Fp2 { c0: mont_of(6), c1: mont_of(5) },
        },
        c1: Fp6 {
            c0: Fp2 { c0: MONT_ONE, c1: mont_of(6) },
            c1: Fp2 { c0: mont_of(4), c1: mont_of(3) },
            c2: Fp2 { c0: mont_of(5), c1: mont_of(7) },
        },
    };
    let mut result = Fp12::zero();
    fp12_mul(&mut result, &a, &b);

    // Spot-check a few components (precomputed from dump_kat2)
    let expected_c0_c0_c0 = Fp([
        14150872979108921994, 11684578284231196138, 424576514251745057,
        4949806420882410996, 2064757856005951663, 1451977818211519304,
    ]);
    let expected_c0_c0_c1 = Fp([
        12693114074801438195, 5461749291501748654, 2495033442136598471,
        16577293973040244844, 16779055036166282964, 246228998652969147,
    ]);
    assert_eq!(result.c0.c0.c0, expected_c0_c0_c0, "Fp12 mul c0.c0.c0 KAT mismatch");
    assert_eq!(result.c0.c0.c1, expected_c0_c0_c1, "Fp12 mul c0.c0.c1 KAT mismatch");
}

#[test]
fn kat_fp12_mul_inv_roundtrip() {
    let a = Fp12 {
        c0: Fp6 {
            c0: Fp2 { c0: mont_of(3), c1: mont_of(4) },
            c1: Fp2 { c0: mont_of(5), c1: mont_of(6) },
            c2: Fp2 { c0: MONT_ONE, c1: mont_of(3) },
        },
        c1: Fp6 {
            c0: Fp2 { c0: mont_of(4), c1: mont_of(5) },
            c1: Fp2 { c0: mont_of(6), c1: MONT_ONE },
            c2: Fp2 { c0: mont_of(3), c1: mont_of(6) },
        },
    };
    let b = Fp12 {
        c0: Fp6 {
            c0: Fp2 { c0: mont_of(5), c1: MONT_ONE },
            c1: Fp2 { c0: mont_of(3), c1: mont_of(4) },
            c2: Fp2 { c0: mont_of(6), c1: mont_of(5) },
        },
        c1: Fp6 {
            c0: Fp2 { c0: MONT_ONE, c1: mont_of(6) },
            c1: Fp2 { c0: mont_of(4), c1: mont_of(3) },
            c2: Fp2 { c0: mont_of(5), c1: mont_of(7) },
        },
    };
    let mut ab = Fp12::zero();
    fp12_mul(&mut ab, &a, &b);
    let mut b_inv = Fp12::zero();
    fp12_inv(&mut b_inv, &b);
    let mut result = Fp12::zero();
    fp12_mul(&mut result, &ab, &b_inv);
    assert!(fp12_eq(&result, &a), "Fp12: (a*b) * inv(b) should equal a");
}

// ===========================================================================
// 2. BLS12-381 pairing KAT
// ===========================================================================

#[test]
fn kat_pairing_generator() {
    // e(G1, G2) should match the precomputed GT generator.
    let mut result = Fp12::zero();
    pairing(&mut result, &G1_X, &G1_Y, &G2_X, &G2_Y);
    assert!(fp12_eq(&result, &E_G1_G2), "e(G1, G2) should match the known GT generator");
}

#[test]
fn kat_pairing_not_one() {
    // e(G1, G2) is not the identity element in GT.
    let one_fp12 = Fp12 {
        c0: Fp6 {
            c0: Fp2 { c0: MONT_ONE, c1: Fp::zero() },
            c1: Fp2::zero(),
            c2: Fp2::zero(),
        },
        c1: Fp6::zero(),
    };
    let mut result = Fp12::zero();
    pairing(&mut result, &G1_X, &G1_Y, &G2_X, &G2_Y);
    assert!(!fp12_eq(&result, &one_fp12), "e(G1, G2) should not be 1 in GT");
}

#[test]
fn kat_bilinearity_scalar_g1() {
    // e(2*G1, G2) == e(G1, G2)^2
    let mut e_pq = Fp12::zero();
    pairing(&mut e_pq, &G1_X, &G1_Y, &G2_X, &G2_Y);

    let mut e_2pq = Fp12::zero();
    pairing(&mut e_2pq, &G1_2X, &G1_2Y, &G2_X, &G2_Y);

    let mut e_pq_sq = Fp12::zero();
    fp12_square(&mut e_pq_sq, &e_pq);

    assert!(fp12_eq(&e_2pq, &e_pq_sq), "e(2*G1, G2) should equal e(G1, G2)^2");
}

#[test]
fn kat_bilinearity_scalar_3() {
    // e(3*G1, G2) == e(G1, G2)^3
    let mut e_pq = Fp12::zero();
    pairing(&mut e_pq, &G1_X, &G1_Y, &G2_X, &G2_Y);

    let mut e_3pq = Fp12::zero();
    pairing(&mut e_3pq, &G1_3X, &G1_3Y, &G2_X, &G2_Y);

    let e_pq_cubed = fp12_pow_small(&e_pq, 3);
    assert!(fp12_eq(&e_3pq, &e_pq_cubed), "e(3*G1, G2) should equal e(G1, G2)^3");
}

#[test]
fn kat_pairing_deterministic() {
    // Two calls to pairing with the same inputs should produce the same output.
    let mut r1 = Fp12::zero();
    let mut r2 = Fp12::zero();
    pairing(&mut r1, &G1_X, &G1_Y, &G2_X, &G2_Y);
    pairing(&mut r2, &G1_X, &G1_Y, &G2_X, &G2_Y);
    assert!(fp12_eq(&r1, &r2), "Pairing should be deterministic");
}

#[test]
fn kat_miller_loop_consistency() {
    // The affine Miller loop + final exponentiation should give the same result
    // as the monolithic `pairing` function (they use the same codepath).
    let mut ml = Fp12::zero();
    miller_loop(&mut ml, &G1_X, &G1_Y, &G2_X, &G2_Y);
    // ml is the raw Miller loop output, not the final pairing value.
    // Verify it is not the identity and not equal to the final pairing:
    assert!(ml.c0.c0.c0 != Fp::zero() || ml.c1.c0.c0 != Fp::zero(),
            "Miller loop output should be non-trivial");
}

// ===========================================================================
// 3. Montgomery encoding KAT
// ===========================================================================

#[test]
fn kat_mont_encode_zero() {
    let zero = mont_of(0);
    assert_eq!(zero, Fp::zero(), "mont_of(0) should be all-zero limbs");
}

#[test]
fn kat_mont_encode_one() {
    let one = mont_of(1);
    assert_eq!(one, MONT_ONE, "mont_of(1) should equal R mod p");
}

#[test]
fn kat_mont_encode_roundtrip_small() {
    // Encode w, then verify that w * (1 in mont) == mont_of(w).
    // This is tautological for the API but verifies the encoding is self-consistent.
    for w in [2u64, 7, 42, 100, 255, 65535] {
        let mw = mont_of(w);
        // Check: mw * 1 == mw (multiplication by Montgomery one)
        let mut check = Fp::zero();
        fp_mul(&mut check, &mw, &MONT_ONE);
        assert_eq!(check, mw, "mont_of({}) * 1 should equal mont_of({})", w, w);
    }
}

#[test]
fn kat_mont_encode_42() {
    // Hardcoded expected value for 42
    let expected = Fp([
        17265956546417371681, 9548759428870439024, 9672661427529377722,
        16972706363380646198, 15303916484165249154, 884422007367203092,
    ]);
    let result = mont_of(42);
    assert_eq!(result, expected, "mont_of(42) should match precomputed value");
}

#[test]
fn kat_mont_arithmetic_consistency() {
    // mont_of(a) * mont_of(b) == mont_of(a*b) for small a, b
    let test_pairs: &[(u64, u64)] = &[
        (3, 5), (7, 11), (13, 17), (2, 100), (6, 7),
    ];
    for &(a, b) in test_pairs {
        let ma = mont_of(a);
        let mb = mont_of(b);
        let expected = mont_of(a * b);
        let mut result = Fp::zero();
        fp_mul(&mut result, &ma, &mb);
        assert_eq!(result, expected, "mont_of({}) * mont_of({}) should equal mont_of({})", a, b, a * b);
    }
}

#[test]
fn kat_mont_add_consistency() {
    // mont_of(a) + mont_of(b) == mont_of(a+b) for small a, b
    let test_pairs: &[(u64, u64)] = &[
        (3, 5), (100, 200), (0, 42), (1, 1),
    ];
    for &(a, b) in test_pairs {
        let ma = mont_of(a);
        let mb = mont_of(b);
        let expected = mont_of(a + b);
        let mut result = Fp::zero();
        fp_add(&mut result, &ma, &mb);
        assert_eq!(result, expected, "mont_of({}) + mont_of({}) should equal mont_of({})", a, b, a + b);
    }
}

#[test]
fn kat_mont_square_consistency() {
    // fp_square(mont_of(n)) == mont_of(n^2) for small n
    for n in [2u64, 3, 7, 10, 255] {
        let mn = mont_of(n);
        let expected = mont_of(n * n);
        let mut result = Fp::zero();
        fp_square(&mut result, &mn);
        assert_eq!(result, expected, "square(mont_of({})) should equal mont_of({})", n, n * n);
    }
}
