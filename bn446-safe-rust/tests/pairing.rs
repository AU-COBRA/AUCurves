//! BN446 optimal-ate pairing: generators, known answer, bilinearity, non-degeneracy, e^r = 1.
//!
//! Curve (AUCurves Curves/BN446_params.v): y^2 = x^3 + 257, xi = 1 + 9u, D-twist
//! y^2 = x^3 + 257/xi.  G1 = (-1, 16), G2 and the known answer e(G1, G2) come from the
//! Python reference (scripts/bn446/bnref.py, gen_rust_consts.py), which
//! equals the model of the Gallina spec (bn446/py/spec446.py).

use bn446::consts::*;
use bn446::*;

fn fp(w: u64) -> Fp { let mut o = Fp::zero(); fp_from_word(&mut o, w); o }
fn canon(x: &Fp) -> [u64; 7] {
    let mut one = Fp::zero();
    one.0[0] = 1;
    let mut c = Fp::zero();
    fp_mul(&mut c, x, &one);
    c.0
}
fn canon12(f: &Fp12) -> [[u64; 7]; 12] {
    let z = [&f.c0.c0, &f.c0.c1, &f.c0.c2, &f.c1.c0, &f.c1.c1, &f.c1.c2];
    let mut o = [[0u64; 7]; 12];
    for (i, a) in z.iter().enumerate() {
        o[2 * i] = canon(&a.c0);
        o[2 * i + 1] = canon(&a.c1);
    }
    o
}
fn one12() -> Fp12 { let mut o = Fp12::zero(); fp_from_word(&mut o.c0.c0.c0, 1); o }
fn mul12(a: &Fp12, b: &Fp12) -> Fp12 { let mut o = Fp12::zero(); fp12_mul(&mut o, a, b); o }
fn sqr12(a: &Fp12) -> Fp12 { let mut o = Fp12::zero(); fp12_square(&mut o, a); o }
fn pow12(a: &Fp12, e: &[u64; 7]) -> Fp12 {
    let mut acc = one12();
    for i in (0..7 * 64).rev() {
        acc = sqr12(&acc);
        if (e[i / 64] >> (i % 64)) & 1 == 1 { acc = mul12(&acc, a); }
    }
    acc
}
type Pairing = fn(&mut Fp12, &Fp, &Fp, &Fp2, &Fp2);
fn pair(f: Pairing, px: &Fp, py: &Fp, qx: &Fp2, qy: &Fp2) -> Fp12 {
    let mut o = Fp12::zero();
    f(&mut o, px, py, qx, qy);
    o
}
fn neg(x: &Fp) -> Fp { let mut o = Fp::zero(); fp_opp(&mut o, x); o }

#[test]
fn generators_on_curves() {
    // y^2 = x^3 + 257
    let (mut y2, mut x2, mut x3, mut rhs) = (Fp::zero(), Fp::zero(), Fp::zero(), Fp::zero());
    fp_square(&mut y2, &G1_Y);
    fp_square(&mut x2, &G1_X);
    fp_mul(&mut x3, &x2, &G1_X);
    fp_add(&mut rhs, &x3, &fp(257));
    assert_eq!(y2, rhs, "G1 on E");
    assert_eq!(canon(&G1_X), canon(&neg(&fp(1))), "G1.x = -1");
    assert_eq!(canon(&G1_Y), canon(&fp(16)), "G1.y = 16");
    // xi y^2 = xi x^3 + 257 on Fp2, xi = 1 + 9u
    let xi = Fp2 { c0: fp(1), c1: fp(9) };
    let (mut y2, mut x2, mut x3, mut a, mut b, mut rhs) =
        (Fp2::zero(), Fp2::zero(), Fp2::zero(), Fp2::zero(), Fp2::zero(), Fp2::zero());
    fp2_square(&mut y2, &G2_Y);
    fp2_square(&mut x2, &G2_X);
    fp2_mul(&mut x3, &x2, &G2_X);
    fp2_mul(&mut a, &xi, &y2);
    fp2_mul(&mut b, &xi, &x3);
    fp2_add(&mut rhs, &b, &Fp2 { c0: fp(257), c1: Fp::zero() });
    assert_eq!(a, rhs, "G2 on the D-twist");
}

#[test]
fn pairing_known_answer() {
    let e = pair(pairing, &G1_X, &G1_Y, &G2_X, &G2_Y);
    assert_eq!(canon12(&e), E_G1_G2, "e(G1, G2) = reference");
}

#[test]
fn pairing_bilinear_nondegenerate_order_r() {
    let e = pair(pairing, &G1_X, &G1_Y, &G2_X, &G2_Y);
    let e6 = pair(pairing, &G1_2X, &G1_2Y, &G2_3X, &G2_3Y);
    let e2 = sqr12(&e);
    let e3 = mul12(&e2, &e);
    assert_eq!(canon12(&e6), canon12(&sqr12(&e3)), "e(2 G1, 3 G2) = e(G1, G2)^6");
    assert_ne!(canon12(&e), canon12(&one12()), "e(G1, G2) != 1");
    assert_eq!(canon12(&pow12(&e, &R_LIMBS)), canon12(&one12()), "e(G1, G2)^r = 1");
    let en = pair(pairing, &G1_X, &neg(&G1_Y), &G2_X, &G2_Y);
    assert_eq!(canon12(&mul12(&e, &en)), canon12(&one12()), "e(G1, G2) e(-G1, G2) = 1");
}

#[test]
fn emitted_uncorrected_pairing_is_not_bilinear() {
    // tower::bn446_pairing_dsd: wrong line layout, no correction lines.
    let e = pair(pairing_dsd_uncorrected, &G1_X, &G1_Y, &G2_X, &G2_Y);
    let e6 = pair(pairing_dsd_uncorrected, &G1_2X, &G1_2Y, &G2_3X, &G2_3Y);
    let e3 = mul12(&sqr12(&e), &e);
    assert_ne!(canon12(&e6), canon12(&sqr12(&e3)));
}
