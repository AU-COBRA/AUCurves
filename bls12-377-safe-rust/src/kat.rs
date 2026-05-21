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

fn nontrivial_raw() -> FpRaw {
    let mut a = [0u64; 6];
    a[0] = 0x0123_4567_89ab_cdef;
    a[1] = 0xfedc_ba98_7654_3210;
    a[2] = 0x0011_2233_4455_6677;
    a[3] = 0x7766_5544_3322_1100;
    a[4] = 0xdead_beef_cafe_babe;
    a[5] = 0x1357_9bdf_2468_ace0;
    // Mask top to ensure < p (most-significant limb cleared in top bits).
    a[5] &= 0x0fff_ffff_ffff_ffff;
    FpRaw(a)
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

#[test]
fn invert_roundtrip() {
    let mut a = zero();
    fp_to_montgomery(&mut a, &nontrivial_raw());
    let mut a_inv = zero();
    fp_inv(&mut a_inv, &a);
    let mut prod = zero();
    fp_mul(&mut prod, &a, &a_inv);
    assert_eq!(prod.0, one_mont().0, "a * a^-1 should equal 1 in Montgomery form");
}

#[test]
fn tower_link_smoke_fp2_add() {
    // Exercises the typed-Fp2 tower entry point + extern_shim leaf.
    // bls377_Fp2_add is two parallel Fp adds on offsets 0 / 48.  The
    // tower body calls bls377_add(...) which resolves to the C-ABI
    // _bls377_add symbol exported by extern_shim, so a green test
    // proves the typed-signature wrapper links through to fiat-rust.
    use tower::{bls377_Fp2_add, Fp as TFp, Fp2 as TFp2};
    let one = one_mont().0;
    let a  = TFp2 { c0: TFp(one),      c1: TFp([0u64; 6]) };
    let z  = TFp2 { c0: TFp([0u64; 6]), c1: TFp([0u64; 6]) };
    let mut out = TFp2 { c0: TFp([0u64; 6]), c1: TFp([0u64; 6]) };
    bls377_Fp2_add(&mut out, &a, &z);
    assert_eq!(out.c0.0, one, "Fp2_add(a, 0) c0 should equal a.c0");
    assert_eq!(out.c1.0, [0u64; 6], "Fp2_add(a, 0) c1 should equal a.c1 (zero)");
}

#[test]
fn tower_link_smoke_fp2_mul() {
    // Exercises bls377_Fp2_mul: (a + b·u) * (c + d·u) with b = d = 0
    // collapses to a·c in Fp, providing a direct cross-check between
    // the typed tower entry and the fiat-rust leaf via extern_shim.
    use tower::{bls377_Fp2_mul, Fp as TFp, Fp2 as TFp2};
    let one = one_mont().0;
    let a = TFp2 { c0: TFp(one), c1: TFp([0u64; 6]) };
    let mut out = TFp2 { c0: TFp([0u64; 6]), c1: TFp([0u64; 6]) };
    bls377_Fp2_mul(&mut out, &a, &a);  // 1 * 1 = 1
    assert_eq!(out.c0.0, one, "Fp2_mul(1, 1) c0 should equal 1");
    assert_eq!(out.c1.0, [0u64; 6], "Fp2_mul(1, 1) c1 should be zero");
}
