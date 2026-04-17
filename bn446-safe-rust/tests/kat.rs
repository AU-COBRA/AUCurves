//! Basic known-answer tests for BN446 (mirrors bn256-safe-rust/tests/kat.rs).

use bn446::*;

fn fp_zero() -> Fp { Fp([0; 7]) }
fn fp_one() -> Fp {
    let mut o = fp_zero();
    fp_from_word(&mut o, 1);
    o
}

#[test]
fn from_word_zero_is_zero() {
    let mut z = fp_one();
    fp_from_word(&mut z, 0);
    assert_eq!(z.0, [0u64; 7]);
}

#[test]
fn add_zero_identity() {
    let one = fp_one();
    let zero = fp_zero();
    let mut sum = fp_zero();
    fp_add(&mut sum, &one, &zero);
    assert_eq!(sum, one);
}

#[test]
fn sub_self_is_zero() {
    let one = fp_one();
    let mut zero = fp_one();
    fp_sub(&mut zero, &one, &one);
    assert_eq!(zero.0, [0u64; 7]);
}

#[test]
fn mul_one_identity() {
    let one = fp_one();
    let mut x = fp_zero();
    fp_from_word(&mut x, 12345);
    let mut prod = fp_zero();
    fp_mul(&mut prod, &x, &one);
    assert_eq!(prod, x);
}

#[test]
fn opp_involutive() {
    let mut x = fp_zero();
    fp_from_word(&mut x, 99);
    let mut y = fp_zero();
    fp_opp(&mut y, &x);
    let mut z = fp_zero();
    fp_opp(&mut z, &y);
    assert_eq!(z, x);
}

#[test]
fn opp_add_is_zero() {
    let mut x = fp_zero();
    fp_from_word(&mut x, 7);
    let mut y = fp_zero();
    fp_opp(&mut y, &x);
    let mut sum = fp_zero();
    fp_add(&mut sum, &x, &y);
    assert_eq!(sum.0, [0u64; 7]);
}

#[test]
fn inv_one_is_one() {
    let one = fp_one();
    let mut inv = fp_zero();
    fp_inv(&mut inv, &one);
    assert_eq!(inv, one);
}

#[test]
fn inv_round_trip() {
    let mut x = fp_zero();
    fp_from_word(&mut x, 42);
    let mut inv_x = fp_zero();
    fp_inv(&mut inv_x, &x);
    let mut prod = fp_zero();
    fp_mul(&mut prod, &x, &inv_x);
    let one = fp_one();
    assert_eq!(prod, one);
}

#[test]
fn square_eq_self_mul() {
    let mut x = fp_zero();
    fp_from_word(&mut x, 31337);
    let mut sq = fp_zero();
    fp_square(&mut sq, &x);
    let mut mul = fp_zero();
    fp_mul(&mut mul, &x, &x);
    assert_eq!(sq, mul);
}

#[test]
fn fp2_add_componentwise() {
    let mut a = Fp2 { c0: fp_zero(), c1: fp_zero() };
    fp_from_word(&mut a.c0, 3);
    fp_from_word(&mut a.c1, 5);
    let mut b = Fp2 { c0: fp_zero(), c1: fp_zero() };
    fp_from_word(&mut b.c0, 7);
    fp_from_word(&mut b.c1, 11);
    let mut sum = Fp2 { c0: fp_zero(), c1: fp_zero() };
    fp2_add(&mut sum, &a, &b);
    let mut want_c0 = fp_zero();
    fp_add(&mut want_c0, &a.c0, &b.c0);
    let mut want_c1 = fp_zero();
    fp_add(&mut want_c1, &a.c1, &b.c1);
    assert_eq!(sum.c0, want_c0);
    assert_eq!(sum.c1, want_c1);
}

#[test]
fn fp2_square_eq_self_mul() {
    let mut a = Fp2 { c0: fp_zero(), c1: fp_zero() };
    fp_from_word(&mut a.c0, 13);
    fp_from_word(&mut a.c1, 17);
    let mut sq = Fp2 { c0: fp_zero(), c1: fp_zero() };
    fp2_square(&mut sq, &a);
    let mut mul = Fp2 { c0: fp_zero(), c1: fp_zero() };
    fp2_mul(&mut mul, &a, &a);
    assert_eq!(sq, mul);
}
