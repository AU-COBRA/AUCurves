//! Cross-check that fiat-rust wrappers obey field axioms.
use super::*;

fn zero() -> Fp { Fp([0u64; 6]) }

fn one_mont() -> Fp {
    // R mod p; obtained via to_montgomery(1).
    let raw = FpRaw({
        let mut a = [0u64; 6];
        a[0] = 1;
        a
    });
    let mut out = zero();
    fp_to_montgomery(&mut out, &raw);
    out
}

#[test]
fn add_zero_identity() {
    let a = one_mont();
    let mut out = zero();
    fp_add(&mut out, &a, &zero());
    assert_eq!(out.0, a.0);
}

#[test]
fn sub_self_is_zero() {
    let a = one_mont();
    let mut out = a;
    fp_sub(&mut out, &a, &a);
    assert_eq!(out.0, [0u64; 6]);
}

#[test]
fn mul_one_identity() {
    let a = one_mont();
    let mut out = zero();
    fp_mul(&mut out, &a, &a);  // 1 * 1 = 1
    assert_eq!(out.0, a.0);
}
