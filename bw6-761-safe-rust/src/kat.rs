//! Cross-check that fiat-rust wrappers obey field axioms.
use super::*;

fn zero() -> Fp { Fp([0u64; 12]) }

fn one_mont() -> Fp {
    // R mod p; obtained via to_montgomery(1).
    let raw = FpRaw({
        let mut a = [0u64; 12];
        a[0] = 1;
        a
    });
    let mut out = zero();
    fp_to_montgomery(&mut out, &raw);
    out
}

fn nontrivial_raw() -> FpRaw {
    let mut a = [0u64; 12];
    a[0] = 0x0123_4567_89ab_cdef;
    a[1] = 0xfedc_ba98_7654_3210;
    a[2] = 0x0011_2233_4455_6677;
    a[3] = 0x7766_5544_3322_1100;
    a[4] = 0xdead_beef_cafe_babe;
    a[5] = 0x1357_9bdf_2468_ace0;
    a[6] = 0x0246_8ace_1357_9bdf;
    a[7] = 0xface_b00c_d00d_feed;
    a[8] = 0xaaaa_bbbb_cccc_dddd;
    a[9] = 0x1111_2222_3333_4444;
    a[10] = 0x5555_6666_7777_8888;
    a[11] = 0x0099_aabb_ccdd_eeff;
    // Mask the most-significant limb conservatively: BW6-761 prime
    // begins with 0x122e..., so any 12-limb value whose top byte is
    // ≤ 0x11 is safely < p.  Cleared to 0x00xx... here.
    a[11] &= 0x00ff_ffff_ffff_ffff;
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
    assert_eq!(out.0, [0u64; 12]);
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
