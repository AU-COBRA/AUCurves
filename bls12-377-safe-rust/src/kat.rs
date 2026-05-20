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
fn tower_link_smoke() {
    // Calls a tower function from the Coq-extracted module to prove the
    // `_bls377_*` C-ABI extern_shim is invoked at runtime.
    // bls377_Fp2_add is two parallel Fp adds on offsets 0 and 48.
    // Tower's untyped Fp emission lets us pass the c0 half (Fp[u64;6])
    // and check (a + 0) reproduces a.
    //
    // This implicitly exercises the extern_shim: the tower's
    // bls377_Fp2_add body calls `bls377_add` which resolves to the
    // `_bls377_add` C-ABI symbol from extern_shim.
    use tower::{bls377_Fp2_add, Fp as TFp};
    let one = one_mont().0;
    // Tower's Fp2 = struct { c0: Fp, c1: Fp }; pass Fp pointers as
    // if they're Fp2 (untyped emission means it's the same byte size,
    // 48 bytes per half, total 96 bytes for an Fp2).  Read only the
    // c0 half (first Fp[u64;6]).
    let a = TFp(one);
    let zero = TFp([0u64; 6]);
    let mut out = TFp([0u64; 6]);
    // bls377_Fp2_add: out = a + 0; the c0 component is one Fp add.
    bls377_Fp2_add(&mut out, &a, &zero);
    assert_eq!(out.0, one, "Fp2_add(a, 0) c0 should equal a.c0");
}
