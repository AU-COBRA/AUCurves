//! BN254: bilinearity, non-degeneracy and agreement with reference implementations, for every
//! executable pairing of this crate.
//!
//! Implementations under test (all share the verified Fp2/Fp6/Fp12 tower and final_exp_dsd):
//!   * `pairing_optimal` = tower::bn254_pairing_dsd_optimal: Miller loop over 6u+2, then the
//!                          lines through Q1 = pi(Q) = (conj(Qx) g1, conj(Qy) gy) and
//!                          -Q2 = -pi^2(Q) = (Qx g1p2, Qy) [no sign change on Qy: the
//!                          gamma_{1,p^2} x-coordinate with Qy is already -pi^2(Q)].
//!   * `pairing`         = `pairing_optimal`.
//!   * `projective::pairing_projective_hand` (hand-written, unverified, benchmark-only): projective
//!                          Miller loop over 6u+2 plus the same two correction lines.
//!   * tower::bn254_pairing_dsd (reported, not asserted): the Miller loop over 6u+2 with no
//!                          correction lines.  It is in G_T and satisfies e(P,Q) e(-P,Q) = 1, but it
//!                          is NOT bilinear (0/60 here).
//!
//! Points come from arkworks (ark-bn254 0.5): P = s G1, Q = t G2 for random s, t (or the
//! generators), so every point is in G1 x G2.  Values are compared on canonical (non-Montgomery)
//! coefficients; ark-bn254 uses the same tower Fp2 = Fp[u]/(u^2+1), Fp6 = Fp2[v]/(v^3-(9+u)),
//! Fp12 = Fp6[w]/(w^2-v), so coefficients compare one to one.
//!
//! Relations checked:
//!   * e(aP, bQ) = e(P, Q)^(ab), e(aP, Q) = e(P, Q)^a, e(P, bQ) = e(P, Q)^b, e(P,Q) e(-P,Q) = 1.
//!   * e(G1, G2) != 1 and e(G1, G2)^r = 1.
//!   * e(P, Q) = ml(P, Q)^((p^12-1)/r) with ml = miller_loop_optimal: the final exponentiation is
//!     exact (its hard part computes x^((p^4-p^2+1)/r)).
//!   * e(P, Q) = ark_ml(P, Q)^((p^12-1)/r): equal to the exactly reduced arkworks Miller loop.
//!   * arkworks' pairing = e(P, Q)^m with m = 2u(6u^2+3u+1): arkworks' hard part (Fuentes-
//!     Castaneda et al.) raises to m (p^4-p^2+1)/r.  So ark = ours^m, not ours.
//!   py_ecc's bn128 pairing (exact exponent) equals `pairing_optimal` itself; with BN254_PAIRING_DUMP set,
//!   `dump_for_py_ecc` writes values for an external py_ecc comparison.

use bn254::*;
use ark_bn254::{Bn254, Fq, Fq12, Fr, G1Affine, G2Affine};
use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup};
use ark_ff::{Field, PrimeField, UniformRand};
use ark_std::rand::{rngs::StdRng, SeedableRng};

const FINAL_EXP: [u64; 44] = [
    0x86964b64ca86f120, 0x40a4efb7e54523a4, 0x837fa97896e84abb, 0x361102b6b9b2b918,
    0xc0de81def35692da, 0xbe04c7e8a6c3c760, 0xd766f9c9d570bb7f, 0xc230974d83561841,
    0x5bba1668c3be69a3, 0x7f3811c410526294, 0x29baee7ddadda71c, 0xbf813b8d145da900,
    0x641bbadf423f9a2c, 0xa80bb4ea44eacc5e, 0xcd65664814fde37c, 0x4a0364b9580291d2,
    0xee93dfb10826f0dd, 0x6b42db8dc5514724, 0xbb10cf430b0f3785, 0x40494e406f804216,
    0x55cfe107acf3aafb, 0x2088ec80e0ebae87, 0x846a3ed011a337a0, 0x48a45a4a1e3a5195,
    0xe5664568dfc50e16, 0xab6a41294c0cc4eb, 0x82d0d602d268c7da, 0x6668449aed3cc48a,
    0x5062cd0fb2015dfc, 0x7f2940a8b1ddb3d1, 0x77f5b63a2a226448, 0xfef0781361e443ae,
    0xf977870e88d5c6c8, 0x790364a61f676baa, 0x5887e72eceaddea3, 0x1377e563a09a1b70,
    0x0c54efee1bd8c3b2, 0x3ec3d15ad524d8f7, 0xdaf15466b2383a5d, 0xe1e30a73bb94fec0,
    0x6a1c71015f3f7be2, 0x842d43bf6369b1ff, 0x20fddadf107d20bc, 0x0000002f4b6dc970,
];
const ARK_M: [u64; 3] = [
    0x2e5d4e223ddedaf4, 0x1ea96b02d9d9e38d, 0x3bec47df15e307c8,
];
const R_ORDER: [u64; 4] = [
    0x43e1f593f0000001, 0x2833e84879b97091, 0xb85045b68181585d, 0x30644e72e131a029,
];

/// R^2 mod p (R = 2^256): montmul(c, R^2) = c R, the Montgomery form of canonical c.
const R2: Fp = Fp([0xf32cfc5b538afa89, 0xb5e71911d44501fb, 0x47ab1eff0a417ff6, 0x06d89f71cab8351f]);

/// u = 4965661367192848881, 6u+2 and r are in tower / R_ORDER; number of random cases per test.
const CASES: usize = 60;

type PairFn = fn(&mut Fp12, &Fp, &Fp, &Fp2, &Fp2);

fn impls() -> Vec<(&'static str, PairFn)> {
    vec![
        ("pairing", pairing as PairFn),
        ("pairing_optimal (bn254_pairing_dsd_optimal)", pairing_optimal as PairFn),
        ("projective::pairing_projective_hand (unverified)", projective::pairing_projective_hand as PairFn),
    ]
}

/// Reported only: the Miller loop over 6u+2 without correction lines.
fn uncorrected(o: &mut Fp12, px: &Fp, py: &Fp, qx: &Fp2, qy: &Fp2) {
    bn254::tower::bn254_pairing_dsd(o, px, py, qx, qy)
}

fn all_impls() -> Vec<(&'static str, PairFn)> {
    let mut v = impls();
    v.push(("tower::bn254_pairing_dsd (no correction lines)", uncorrected as PairFn));
    v
}

fn mont(x: &Fq) -> Fp {
    let c = Fp(x.into_bigint().0);
    let mut o = Fp::zero();
    fp_mul(&mut o, &c, &R2);
    o
}

fn canon(x: &Fp) -> [u64; 4] {
    let mut c = Fp::zero();
    fp_mul(&mut c, x, &Fp([1, 0, 0, 0]));
    c.0
}

type C12 = [[u64; 4]; 12];

fn canon12(f: &Fp12) -> C12 {
    let z = [&f.c0.c0, &f.c0.c1, &f.c0.c2, &f.c1.c0, &f.c1.c1, &f.c1.c2];
    let mut o = [[0u64; 4]; 12];
    for (i, a) in z.iter().enumerate() {
        o[2 * i] = canon(&a.c0);
        o[2 * i + 1] = canon(&a.c1);
    }
    o
}

fn ark_canon12(f: &Fq12) -> C12 {
    let z = [&f.c0.c0, &f.c0.c1, &f.c0.c2, &f.c1.c0, &f.c1.c1, &f.c1.c2];
    let mut o = [[0u64; 4]; 12];
    for (i, a) in z.iter().enumerate() {
        o[2 * i] = a.c0.into_bigint().0;
        o[2 * i + 1] = a.c1.into_bigint().0;
    }
    o
}

fn one12() -> Fp12 {
    let mut o = Fp12::zero();
    fp_from_word(&mut o.c0.c0.c0, 1);
    o
}

/// base^e, e as little-endian u64 limbs, left-to-right square-and-multiply in the crate's tower.
fn pow12(base: &Fp12, e: &[u64]) -> Fp12 {
    let mut acc = one12();
    for i in (0..e.len() * 64).rev() {
        let t = acc;
        fp12_square(&mut acc, &t);
        if (e[i / 64] >> (i % 64)) & 1 == 1 {
            let t = acc;
            fp12_mul(&mut acc, &t, base);
        }
    }
    acc
}

struct Pt {
    px: Fp,
    py: Fp,
    qx: Fp2,
    qy: Fp2,
}

fn pt(p: &G1Affine, q: &G2Affine) -> Pt {
    let (x, y) = p.xy().unwrap();
    let (qx, qy) = q.xy().unwrap();
    Pt {
        px: mont(&x),
        py: mont(&y),
        qx: Fp2 { c0: mont(&qx.c0), c1: mont(&qx.c1) },
        qy: Fp2 { c0: mont(&qy.c0), c1: mont(&qy.c1) },
    }
}

fn run(f: PairFn, a: &Pt) -> Fp12 {
    let mut o = Fp12::zero();
    f(&mut o, &a.px, &a.py, &a.qx, &a.qy);
    o
}

fn fr_limbs(x: &Fr) -> [u64; 4] {
    x.into_bigint().0
}

fn g1(s: &Fr) -> G1Affine {
    (G1Affine::generator() * s).into_affine()
}
fn g2(s: &Fr) -> G2Affine {
    (G2Affine::generator() * s).into_affine()
}

/// Random cases: (P, Q, a, b).  P is G1 for i % 3 == 0, Q is G2 for i % 2 == 0; otherwise random
/// multiples of the generators.
fn cases(seed: u64) -> Vec<(G1Affine, G2Affine, Fr, Fr)> {
    let mut rng = StdRng::seed_from_u64(seed);
    (0..CASES)
        .map(|i| {
            let p = if i % 3 == 0 { G1Affine::generator() } else { g1(&Fr::rand(&mut rng)) };
            let q = if i % 2 == 0 { G2Affine::generator() } else { g2(&Fr::rand(&mut rng)) };
            (p, q, Fr::rand(&mut rng), Fr::rand(&mut rng))
        })
        .collect()
}

#[derive(Default, Debug)]
struct Counts {
    both: usize,
    left: usize,
    right: usize,
    neg: usize,
    total: usize,
}

/// Per implementation: how many of the CASES satisfy e(aP,bQ) = e(P,Q)^(ab), e(aP,Q) = e(P,Q)^a,
/// e(P,bQ) = e(P,Q)^b, and e(P,Q) e(-P,Q) = 1.
fn bilinearity_counts(f: PairFn) -> Counts {
    let mut c = Counts::default();
    for (p, q, a, b) in cases(0x00b2_5400_0000_0001) {
        let e = run(f, &pt(&p, &q));
        let eab = run(f, &pt(&g1_mul(&p, &a), &g2_mul(&q, &b)));
        let ea = run(f, &pt(&g1_mul(&p, &a), &q));
        let eb = run(f, &pt(&p, &g2_mul(&q, &b)));
        let en = run(f, &pt(&(-p), &q));
        c.total += 1;
        if canon12(&eab) == canon12(&pow12(&e, &fr_limbs(&(a * b)))) { c.both += 1; }
        if canon12(&ea) == canon12(&pow12(&e, &fr_limbs(&a))) { c.left += 1; }
        if canon12(&eb) == canon12(&pow12(&e, &fr_limbs(&b))) { c.right += 1; }
        let mut prod = Fp12::zero();
        fp12_mul(&mut prod, &e, &en);
        if canon12(&prod) == canon12(&one12()) { c.neg += 1; }
    }
    c
}

fn g1_mul(p: &G1Affine, s: &Fr) -> G1Affine {
    (*p * s).into_affine()
}
fn g2_mul(q: &G2Affine, s: &Fr) -> G2Affine {
    (*q * s).into_affine()
}

#[test]
fn bilinearity_report_all_impls() {
    for (name, f) in all_impls() {
        let c = bilinearity_counts(f);
        println!(
            "BILINEARITY {name}: e(aP,bQ)=e^(ab) {}/{}  e(aP,Q)=e^a {}/{}  e(P,bQ)=e^b {}/{}  e(P,Q)e(-P,Q)=1 {}/{}",
            c.both, c.total, c.left, c.total, c.right, c.total, c.neg, c.total
        );
    }
}

#[test]
fn pairings_are_bilinear() {
    for (name, f) in impls() {
        let c = bilinearity_counts(f);
        assert_eq!((c.both, c.left, c.right, c.neg), (CASES, CASES, CASES, CASES), "{name}: {c:?}");
    }
}

#[test]
fn non_degenerate_report_all_impls() {
    let gen = pt(&G1Affine::generator(), &G2Affine::generator());
    for (name, f) in all_impls() {
        let e = run(f, &gen);
        let one = canon12(&e) == canon12(&one12());
        let ord_r = canon12(&pow12(&e, &R_ORDER)) == canon12(&one12());
        println!("NONDEGENERATE {name}: e(G1,G2) != 1: {}  e(G1,G2)^r = 1: {}", !one, ord_r);
    }
}

#[test]
fn pairings_non_degenerate() {
    for (name, f) in impls() {
        let e = run(f, &pt(&G1Affine::generator(), &G2Affine::generator()));
        assert_ne!(canon12(&e), canon12(&one12()), "{name}");
        assert_eq!(canon12(&pow12(&e, &R_ORDER)), canon12(&one12()), "{name}");
    }
}

/// pairing_optimal = miller_loop_optimal^((p^12-1)/r) = ark_ml^((p^12-1)/r), and
/// ark pairing = pairing_optimal^m.  Also reports how the other implementations relate.
#[test]
fn reference_relations() {
    let mut rng = StdRng::seed_from_u64(0x00b2_5400_0000_0002);
    let mut pts: Vec<(G1Affine, G2Affine)> = vec![
        (G1Affine::generator(), G2Affine::generator()),
        (g1(&Fr::from(2u64)), g2(&Fr::from(3u64))),
    ];
    for _ in 0..8 {
        pts.push((g1(&Fr::rand(&mut rng)), g2(&Fr::rand(&mut rng))));
    }
    let n = pts.len();
    let (mut exact_own, mut exact_ark, mut ark_m, mut eq_ark) = (0, 0, 0, 0);
    let mut other = vec![(0usize, 0usize, 0usize, 0usize); all_impls().len()];
    for (p, q) in &pts {
        let a = pt(p, q);
        let ours = canon12(&run(pairing_optimal, &a));
        let mut ml = Fp12::zero();
        miller_loop_optimal(&mut ml, &a.px, &a.py, &a.qx, &a.qy);
        if canon12(&pow12(&ml, &FINAL_EXP)) == ours { exact_own += 1; }
        let ark_ml = Bn254::multi_miller_loop([*p], [*q]).0;
        if ark_canon12(&ark_ml.pow(FINAL_EXP)) == ours { exact_ark += 1; }
        let ark = Bn254::pairing(*p, *q).0;
        if ark_canon12(&ark) == ours { eq_ark += 1; }
        let ours12 = run(pairing_optimal, &a);
        if ark_canon12(&ark) == canon12(&pow12(&ours12, &ARK_M)) { ark_m += 1; }
        let plain = canon12(&run(uncorrected, &a));
        for (k, (_, f)) in all_impls().iter().enumerate() {
            let v = canon12(&run(*f, &a));
            if v == ours { other[k].0 += 1; }
            if v == plain { other[k].3 += 1; }
            if v == ark_canon12(&ark) { other[k].1 += 1; }
            if v == ark_canon12(&ark_ml.pow(FINAL_EXP)) { other[k].2 += 1; }
        }
    }
    println!("REFERENCE pairing_optimal = miller_loop_optimal^((p^12-1)/r): {exact_own}/{n}");
    println!("REFERENCE pairing_optimal = ark_ml^((p^12-1)/r): {exact_ark}/{n}");
    println!("REFERENCE pairing_optimal = ark pairing: {eq_ark}/{n}");
    println!("REFERENCE ark pairing = pairing_optimal^(2u(6u^2+3u+1)): {ark_m}/{n}");
    for (k, (name, _)) in all_impls().iter().enumerate() {
        println!(
            "REFERENCE {name}: = pairing_optimal {}/{n}, = bn254_pairing_dsd {}/{n}, = ark pairing {}/{n}, = ark_ml^((p^12-1)/r) {}/{n}",
            other[k].0, other[k].3, other[k].1, other[k].2
        );
    }
    assert_eq!((exact_own, exact_ark, ark_m), (n, n, n));
    for k in 0..impls().len() {
        assert_eq!(other[k].0, n, "{} != pairing_optimal", impls()[k].0);
    }
}

/// With BN254_PAIRING_DUMP=<file>: write "a b c_0 .. c_11" lines (P = a G1, Q = b G2, canonical
/// coefficients of pairing_optimal(P, Q) and pairing(P, Q) in the tower basis) for
/// a comparison with py_ecc outside this crate.
#[test]
fn dump_for_py_ecc() {
    let Ok(path) = std::env::var("BN254_PAIRING_DUMP") else { return };
    let mut rng = StdRng::seed_from_u64(0x00b2_5400_0000_0003);
    let mut sc: Vec<(Fr, Fr)> = vec![(Fr::from(1u64), Fr::from(1u64)), (Fr::from(2u64), Fr::from(3u64))];
    for _ in 0..6 {
        sc.push((Fr::rand(&mut rng), Fr::rand(&mut rng)));
    }
    let mut out = String::new();
    for (s, t) in &sc {
        let a = pt(&g1(s), &g2(t));
        for (name, f) in [("pairing_optimal", pairing_optimal as PairFn), ("pairing", pairing as PairFn),
                          ("bn254_pairing_dsd", uncorrected as PairFn)] {
            let v = canon12(&run(f, &a));
            let big = |l: &[u64; 4]| format!("{:016x}{:016x}{:016x}{:016x}", l[3], l[2], l[1], l[0]);
            out += &format!(
                "{name} {} {} {}\n",
                s.into_bigint(),
                t.into_bigint(),
                v.iter().map(big).collect::<Vec<_>>().join(" ")
            );
        }
    }
    std::fs::write(path, out).unwrap();
}
