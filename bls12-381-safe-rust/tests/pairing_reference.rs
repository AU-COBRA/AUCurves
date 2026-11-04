//! The pairing against plain exponentiation and two independent
//! implementations (blst, arkworks), on canonical (non-Montgomery) F_q^12
//! coefficients.
//!
//! * `final_exp(ml)` must equal `ml^((p^12-1)/r)` computed by square-and-
//!   multiply over the 4314-bit exponent: the final exponentiation is exact.
//!   The tower shipped before this change computed `ml^(3 (p^12-1)/r)`.
//! * blst 0.3 and arkworks 0.5 both return `f_{x,Q}(P)^(3 (p^12-1)/r)`
//!   (their hard part is the Hayashida-Hayasaka-Teruya chain, exponent
//!   3 h3, as gnark documents), with x = -|x| < 0, whereas `pairing` raises
//!   `f_{|x|,Q}(P)` (no conjugation for the sign of x) to `(p^12-1)/r`.
//!   For elements of order r that gives `blst = conj(pairing)^3`, which is
//!   checked on (G1, G2) and (2 G1, 3 G2).  Equality with blst is not
//!   possible without changing the Miller loop and the final exponent.
//! * `final_exp(ml)` differs from its cube.

use bls12_381::*;

/// Montgomery form -> canonical little-endian limbs: montmul(x, 1) = x R^{-1}.
fn canon(x: &Fp) -> [u64; 6] {
    let raw_one = Fp([1, 0, 0, 0, 0, 0]);
    let mut c = Fp::zero();
    fp_mul(&mut c, x, &raw_one);
    c.0
}

fn canon12(f: &Fp12) -> [[u64; 6]; 12] {
    let fp2s = [&f.c0.c0, &f.c0.c1, &f.c0.c2, &f.c1.c0, &f.c1.c1, &f.c1.c2];
    let mut out = [[0u64; 6]; 12];
    for (i, z) in fp2s.iter().enumerate() {
        out[2 * i] = canon(&z.c0);
        out[2 * i + 1] = canon(&z.c1);
    }
    out
}

fn fp12_eq(a: &Fp12, b: &Fp12) -> bool {
    canon12(a) == canon12(b)
}

// ---------------------------------------------------------------------------
// blst: points and pairing.  blst keeps F_q in Montgomery form with the same
// R = 2^384, so its limbs are our limbs.
// ---------------------------------------------------------------------------

fn blst_g1_mul(k: u8) -> blst::blst_p1_affine {
    unsafe {
        let mut p = blst::blst_p1::default();
        let s = [k];
        blst::blst_p1_mult(&mut p, blst::blst_p1_generator(), s.as_ptr(), 8);
        let mut a = blst::blst_p1_affine::default();
        blst::blst_p1_to_affine(&mut a, &p);
        a
    }
}

fn blst_g2_mul(k: u8) -> blst::blst_p2_affine {
    unsafe {
        let mut p = blst::blst_p2::default();
        let s = [k];
        blst::blst_p2_mult(&mut p, blst::blst_p2_generator(), s.as_ptr(), 8);
        let mut a = blst::blst_p2_affine::default();
        blst::blst_p2_to_affine(&mut a, &p);
        a
    }
}

fn blst_pairing_canon(p: &blst::blst_p1_affine, q: &blst::blst_p2_affine) -> [[u64; 6]; 12] {
    let mut ml = blst::blst_fp12::default();
    let mut e = blst::blst_fp12::default();
    let mut out = [[0u64; 6]; 12];
    unsafe {
        blst::blst_miller_loop(&mut ml, q, p);
        blst::blst_final_exp(&mut e, &ml);
        for i in 0..2 {
            for j in 0..3 {
                for k in 0..2 {
                    blst::blst_uint64_from_fp(out[6 * i + 2 * j + k].as_mut_ptr(), &e.fp6[i].fp2[j].fp[k]);
                }
            }
        }
    }
    out
}

fn ours_pairing(p: &blst::blst_p1_affine, q: &blst::blst_p2_affine) -> Fp12 {
    let px = Fp(p.x.l);
    let py = Fp(p.y.l);
    let qx = Fp2 { c0: Fp(q.x.fp[0].l), c1: Fp(q.x.fp[1].l) };
    let qy = Fp2 { c0: Fp(q.y.fp[0].l), c1: Fp(q.y.fp[1].l) };
    let mut out = Fp12::zero();
    pairing(&mut out, &px, &py, &qx, &qy);
    out
}

// ---------------------------------------------------------------------------
// arkworks pairing, canonical limbs
// ---------------------------------------------------------------------------

fn ark_pairing_canon(a: u64, b: u64) -> [[u64; 6]; 12] {
    use ark_bls12_381::{Bls12_381, Fr, G1Projective, G2Projective};
    use ark_ec::{pairing::Pairing, CurveGroup, PrimeGroup};
    use ark_ff::PrimeField;
    let p = (G1Projective::generator() * Fr::from(a)).into_affine();
    let q = (G2Projective::generator() * Fr::from(b)).into_affine();
    let e = Bls12_381::pairing(p, q).0;
    let fq6s = [&e.c0, &e.c1];
    let mut out = [[0u64; 6]; 12];
    for (i, f6) in fq6s.iter().enumerate() {
        let fq2s = [&f6.c0, &f6.c1, &f6.c2];
        for (j, f2) in fq2s.iter().enumerate() {
            out[6 * i + 2 * j] = f2.c0.into_bigint().0;
            out[6 * i + 2 * j + 1] = f2.c1.into_bigint().0;
        }
    }
    out
}

fn conj(f: &Fp12) -> Fp12 {
    let mut g = f.clone();
    for z in [&mut g.c1.c0, &mut g.c1.c1, &mut g.c1.c2] {
        let (a, b) = (z.c0, z.c1);
        fp_opp(&mut z.c0, &a);
        fp_opp(&mut z.c1, &b);
    }
    g
}

fn cube(f: &Fp12) -> Fp12 {
    let mut f2 = Fp12::zero();
    fp12_mul(&mut f2, f, f);
    let mut f3 = Fp12::zero();
    fp12_mul(&mut f3, &f2, f);
    f3
}

fn check(a: u8, b: u8) {
    let p = blst_g1_mul(a);
    let q = blst_g2_mul(b);
    let ours = ours_pairing(&p, &q);
    let via_blst = blst_pairing_canon(&p, &q);
    let via_ark = ark_pairing_canon(a as u64, b as u64);
    assert_eq!(via_blst, via_ark, "blst and arkworks disagree on e({a} G1, {b} G2)");
    assert_eq!(canon12(&cube(&conj(&ours))), via_blst,
               "conj(pairing({a} G1, {b} G2))^3 differs from blst and arkworks");
    assert_ne!(canon12(&conj(&ours)), via_blst,
               "pairing({a} G1, {b} G2) is still the cube of the exact value");
}

/// (p^12 - 1) / r, 68 little-endian u64 limbs.
const FINAL_EXP: [u64; 68] = [0xc0bcb9b55df57510,0x25f98630e68bfb24,0x4406fbc8fbd5f489,0x8e2f8491d12191a0,0x3e9d71650a6f8069,0x226c2f011d4cab80,0x67f67c4717489119,0xaf3f881bd88592d7,0x1a67e49eeed2161d,0xe5b78c7869aeb218,0xf6539314043f7bbc,0x73f62537f2701aae,0xaff1c910e9622d2a,0x6283313492caa9d4,0x2e2f3ec2bea83d19,0xa4c7e79fb02faa73,0x6c49637fd7961be1,0x8e88adce8817745,0x35de3f7a36399917,0x9c1d9f7c31759c36,0xfa9e13c24ea820b0,0x3fc56947a403577d,0xa4c1b6dcfc5cceb7,0x1bbd81367066bca6,0x418a3ef0bc62775,0x49bf9b71a9f9e010,0x511291097db60b17,0x498345c6e5308f1c,0x6d8823b19dadd7c2,0x92004cedd556952c,0x4c6bec3ec03ef195,0xa1fad20044ce6ad,0xc55d3109cd15948d,0x334f46c02c3f0bd0,0x3b5a62eb34c05739,0x724538411d1676a5,0x127a1b5ad0463434,0x61a474c5c85b0129,0x8dfc8e2886ef965e,0x96532fef459f1243,0x40ee7169cdc10412,0x9c40a68eb74bb22a,0x25118790f4684d0b,0x596bc293c8d4c01f,0x1064837f27611212,0x77ffb10bf24dde4,0xc49f570bcd2b01f3,0x1a0c5bf24c374693,0x350da5359bc73ab6,0xd2670d93e4d7acdd,0xd39099b86e1ab656,0x19328148978e2b0d,0xb113f414386b0e88,0x7a0dce2630d9aa4,0xa927e7bb93753318,0xe347aa68ad49466f,0x1c0ad0d6106feaf4,0xc872ee83ff3a0f0f,0x74e43b9a660835c,0xc0aadff5e9cfee9a,0x30698e8cc7deada9,0xd1073776ab353f2c,0x17848517badc3a43,0x7363baa13f8d14a9,0xd4977b3f7d4507d0,0x496a1c0a89ee0193,0xdcc825b7e1bda9c0,0x2ee1db5];

fn fp12_one() -> Fp12 {
    let mut one = Fp12::zero();
    fp_from_word(&mut one.c0.c0.c0, 1);
    one
}

fn pow_final(f: &Fp12) -> Fp12 {
    let mut acc = fp12_one();
    for i in (0..68 * 64).rev() {
        let mut t = Fp12::zero();
        fp12_square(&mut t, &acc);
        acc = t;
        if (FINAL_EXP[i / 64] >> (i % 64)) & 1 == 1 {
            let mut t = Fp12::zero();
            fp12_mul(&mut t, &acc, f);
            acc = t;
        }
    }
    acc
}

fn miller_and_final(a: u8, b: u8) -> (Fp12, Fp12) {
    let p = blst_g1_mul(a);
    let q = blst_g2_mul(b);
    let px = Fp(p.x.l);
    let py = Fp(p.y.l);
    let qx = Fp2 { c0: Fp(q.x.fp[0].l), c1: Fp(q.x.fp[1].l) };
    let qy = Fp2 { c0: Fp(q.y.fp[0].l), c1: Fp(q.y.fp[1].l) };
    let mut ml = Fp12::zero();
    miller_loop(&mut ml, &px, &py, &qx, &qy);
    let mut e = Fp12::zero();
    final_exp(&mut e, &ml);
    (ml, e)
}

#[test]
fn final_exp_is_exact_power() {
    for (a, b) in [(1u8, 1u8), (2, 3)] {
        let (ml, e) = miller_and_final(a, b);
        assert!(fp12_eq(&e, &pow_final(&ml)),
                "final_exp(ml) differs from ml^((p^12-1)/r) for ({a} G1, {b} G2)");
    }
}

#[test]
fn pairing_generators_vs_blst_and_arkworks() {
    check(1, 1);
}

#[test]
fn pairing_2g1_3g2_vs_blst_and_arkworks() {
    check(2, 3);
}

#[test]
fn final_exp_of_miller_loop_is_not_its_cube() {
    let (ml, e) = miller_and_final(1, 1);
    let _ = ml;
    assert!(!fp12_eq(&e, &cube(&e)), "final_exp(ml) equals its cube");
    // and final_exp agrees with pairing on the same input
    let p = blst_g1_mul(1);
    let q = blst_g2_mul(1);
    assert!(fp12_eq(&e, &ours_pairing(&p, &q)), "final_exp(miller_loop) differs from pairing");
}
