//! Known-answer tests for the P-224 (secp224r1) group operations.
//!
//! Zero external dependencies: everything needed to check the crate is in
//! this file.
//!
//! Field encoding.  The crate stores field elements in Montgomery form with
//! R = 2^256 modulo
//!   p = 0xffffffffffffffffffffffffffffffff000000000000000000000001
//!     = 2^224 - 2^96 + 1
//! (`fiat-crypto/fiat-rust/src/p224_64.rs`, header line `m = ...`).  The
//! group API of this crate takes and returns *canonical* (non-Montgomery)
//! affine limbs, which is also how the vectors below are written: canonical
//! big-endian hex.
//!
//! # Provenance of the vectors
//!
//! * The curve parameters `p`, `a = -3`, `b`, `G = (Gx, Gy)` and the group
//!   order `n` are hardcoded from the published FIPS 186-4 / SEC 2 v2.0
//!   secp224r1 parameters — external inputs, not outputs of this crate.
//!   `curve_constants_match_crate` checks the crate's own copies against
//!   them.
//!
//! * The `2G` *x*-coordinate was transcribed from the republished NIST
//!   P-224 "k*G" table before being computed here and is reproduced exactly
//!   by the reference implementation below; that single coordinate is an
//!   independent KAT.
//!
//! * Every other multiple — the `2G` *y*-coordinate, `3G`, `5G`, `10G` and
//!   the large-scalar vector — is **not** externally
//!   sourced.  They were produced by the independent reference
//!   implementation in this file (module `refimpl`: textbook affine
//!   chord-and-tangent formulas over schoolbook non-Montgomery big-integer
//!   arithmetic with a binary extended GCD inverse) and cross-checked
//!   against the crate, which uses homogeneous projective
//!   Renes-Costello-Batina complete addition over fiat-crypto's
//!   word-by-word Montgomery leaves and a Bernstein-Yang inverse.  They are
//!   regression anchors that are additionally agreed on by two unrelated
//!   implementations of the group law over two unrelated field
//!   representations — not published KATs.

#![allow(clippy::needless_range_loop)]

use p224::group::*;

// ===========================================================================
// Published curve parameters (FIPS 186-4 D.1.2.2 / SEC 2 v2.0 section 2.2.2)
// ===========================================================================

const P_HEX: &str = "ffffffffffffffffffffffffffffffff000000000000000000000001";
const B_HEX: &str = "b4050a850c04b3abf54132565044b0b7d7bfd8ba270b39432355ffb4";
const GX_HEX: &str = "b70e0cbd6bb4bf7f321390b94a03c1d356c21122343280d6115c1d21";
const GY_HEX: &str = "bd376388b5f723fb4c22dfe6cd4375a05a07476444d5819985007e34";
const N_HEX: &str = "ffffffffffffffffffffffffffff16a2e0b8f03e13dd29455c5c2a3d";

// ===========================================================================
// KAT vectors: affine coordinates of k*G, canonical (non-Montgomery) hex.
// See the provenance note in the module header.
// ===========================================================================

const K2_X: &str = "706a46dc76dcb76798e60e6d89474788d16dc18032d268fd1a704fa6";
const K2_Y: &str = "1c2b76a7bc25e7702a704fa986892849fca629487acf3709d2e4e8bb";

const K3_X: &str = "df1b1d66a551d0d31eff822558b9d2cc75c2180279fe0d08fd896d04";
const K3_Y: &str = "a3f7f03cadd0be444c0aa56830130ddf77d317344e1af3591981a925";

const K5_X: &str = "31c49ae75bce7807cdff22055d94ee9021fedbb5ab51c57526f011aa";
const K5_Y: &str = "27e8bff1745635ec5ba0c9f1c2ede15414c6507d29ffe37e790a079b";

const K10_X: &str = "aea9e17a306517eb89152aa7096d2c381ec813c51aa880e7bee2c0fd";
const K10_Y: &str = "39bb30eab337e0a521b6cba1abe4b2b3a3e524c14a3fe3eb116b655f";

/// A fixed 224-bit scalar below n, used for the large-scalar KAT.
const KBIG_HEX: &str = "1a2b3c4d5e6f708192a3b4c5d6e7f8090f1e2d3c4b5a697887960123";
const KBIG_X: &str = "f4f13ddb1f559e4d52107bba3c0fe35198d837f2e5e4d0ca03306492";
const KBIG_Y: &str = "e57867d7166d496a5228fea6687ac51246cfb2957f6d14376ad15c76";

// ===========================================================================
// Independent reference implementation
// ===========================================================================

/// Working width in 64-bit limbs.  The modulus needs 4; the reference uses
/// 8 so that a full 4x4 schoolbook product and the `x + p` step of the
/// binary extended GCD both fit without a separate carry word.
const LN: usize = 8;

/// Number of limbs in the crate's field representation.
const FL: usize = 4;

/// Little-endian limb vector.
type Big = [u64; LN];

mod refimpl {
    use super::{Big, LN};
    use core::cmp::Ordering;

    pub fn zero() -> Big {
        [0u64; LN]
    }

    pub fn one() -> Big {
        let mut o = [0u64; LN];
        o[0] = 1;
        o
    }

    pub fn is_zero(a: &Big) -> bool {
        a.iter().all(|&w| w == 0)
    }

    pub fn is_one(a: &Big) -> bool {
        a[0] == 1 && a[1..].iter().all(|&w| w == 0)
    }

    pub fn cmp(a: &Big, b: &Big) -> Ordering {
        for i in (0..LN).rev() {
            match a[i].cmp(&b[i]) {
                Ordering::Equal => continue,
                other => return other,
            }
        }
        Ordering::Equal
    }

    /// Schoolbook add with carry-out.
    pub fn add_raw(a: &Big, b: &Big) -> (Big, u64) {
        let mut out = [0u64; LN];
        let mut carry = 0u128;
        for i in 0..LN {
            let t = a[i] as u128 + b[i] as u128 + carry;
            out[i] = t as u64;
            carry = t >> 64;
        }
        (out, carry as u64)
    }

    /// Schoolbook subtract with borrow-out.
    pub fn sub_raw(a: &Big, b: &Big) -> (Big, u64) {
        let mut out = [0u64; LN];
        let mut borrow = 0i128;
        for i in 0..LN {
            let t = a[i] as i128 - b[i] as i128 - borrow;
            out[i] = t as u64;
            borrow = if t < 0 { 1 } else { 0 };
        }
        (out, borrow as u64)
    }

    /// `a << 1`, injecting `bit` at the bottom.  The top bit is discarded;
    /// callers keep values below 2^(64*LN - 1).
    pub fn shl1(a: &Big, bit: u64) -> Big {
        let mut out = [0u64; LN];
        let mut carry = bit;
        for i in 0..LN {
            out[i] = (a[i] << 1) | carry;
            carry = a[i] >> 63;
        }
        out
    }

    /// `a >> 1`, injecting `top` at the most significant bit.
    pub fn shr1(a: &Big, top: u64) -> Big {
        let mut out = [0u64; LN];
        let mut carry = top;
        for i in (0..LN).rev() {
            out[i] = (a[i] >> 1) | (carry << 63);
            carry = a[i] & 1;
        }
        out
    }

    pub fn add_mod(a: &Big, b: &Big, p: &Big) -> Big {
        let (s, c) = add_raw(a, b);
        if c != 0 || cmp(&s, p) != Ordering::Less {
            sub_raw(&s, p).0
        } else {
            s
        }
    }

    pub fn sub_mod(a: &Big, b: &Big, p: &Big) -> Big {
        let (d, brw) = sub_raw(a, b);
        if brw != 0 {
            add_raw(&d, p).0
        } else {
            d
        }
    }

    /// Full 2*LN-limb schoolbook product reduced modulo `p` by MSB-first
    /// shift-and-subtract.  Deliberately naive: this is reference code.
    pub fn mul_mod(a: &Big, b: &Big, p: &Big) -> Big {
        let mut prod = [0u64; 2 * LN];
        for i in 0..LN {
            let mut carry = 0u64;
            for j in 0..LN {
                let t = (a[i] as u128) * (b[j] as u128)
                    + (prod[i + j] as u128)
                    + (carry as u128);
                prod[i + j] = t as u64;
                carry = (t >> 64) as u64;
            }
            prod[i + LN] = carry;
        }
        // index one past the most significant set bit
        let mut top = 2 * LN * 64;
        while top > 0 {
            let i = (top - 1) / 64;
            let s = (top - 1) % 64;
            if (prod[i] >> s) & 1 == 1 {
                break;
            }
            top -= 1;
        }
        let mut r = [0u64; LN];
        let mut bit = top;
        while bit > 0 {
            bit -= 1;
            let b = (prod[bit / 64] >> (bit % 64)) & 1;
            r = shl1(&r, b);
            if cmp(&r, p) != Ordering::Less {
                r = sub_raw(&r, p).0;
            }
        }
        r
    }

    pub fn sqr_mod(a: &Big, p: &Big) -> Big {
        mul_mod(a, a, p)
    }

    /// `x / 2 mod p` for odd `p`.
    fn half_mod(x: &Big, p: &Big) -> Big {
        if x[0] & 1 == 0 {
            shr1(x, 0)
        } else {
            let (s, c) = add_raw(x, p);
            shr1(&s, c)
        }
    }

    /// Modular inverse by the binary extended Euclidean algorithm
    /// (HAC 14.61).  `p` must be odd and `a` must be nonzero mod `p`.
    pub fn inv_mod(a: &Big, p: &Big) -> Big {
        assert!(!is_zero(a), "inverse of zero");
        let mut u = *a;
        let mut v = *p;
        let mut x1 = one();
        let mut x2 = zero();
        while !is_one(&u) && !is_one(&v) {
            while u[0] & 1 == 0 {
                u = shr1(&u, 0);
                x1 = half_mod(&x1, p);
            }
            while v[0] & 1 == 0 {
                v = shr1(&v, 0);
                x2 = half_mod(&x2, p);
            }
            if cmp(&u, &v) != Ordering::Less {
                u = sub_raw(&u, &v).0;
                x1 = sub_mod(&x1, &x2, p);
            } else {
                v = sub_raw(&v, &u).0;
                x2 = sub_mod(&x2, &x1, p);
            }
        }
        if is_one(&u) {
            x1
        } else {
            x2
        }
    }

    /// Affine point; `None` is the point at infinity.
    pub type Aff = Option<(Big, Big)>;

    /// Textbook chord-and-tangent addition on y^2 = x^3 + a x + b.
    pub fn add(pp: &Aff, qq: &Aff, a: &Big, p: &Big) -> Aff {
        let (x1, y1) = match pp {
            None => return *qq,
            Some(v) => *v,
        };
        let (x2, y2) = match qq {
            None => return *pp,
            Some(v) => *v,
        };
        let lam = if x1 == x2 {
            if y1 != y2 || is_zero(&y1) {
                return None; // P + (-P)
            }
            // tangent: (3 x^2 + a) / (2 y)
            let xx = sqr_mod(&x1, p);
            let three_xx = add_mod(&add_mod(&xx, &xx, p), &xx, p);
            let num = add_mod(&three_xx, a, p);
            let den = add_mod(&y1, &y1, p);
            mul_mod(&num, &inv_mod(&den, p), p)
        } else {
            // chord: (y2 - y1) / (x2 - x1)
            let num = sub_mod(&y2, &y1, p);
            let den = sub_mod(&x2, &x1, p);
            mul_mod(&num, &inv_mod(&den, p), p)
        };
        let x3 = sub_mod(&sub_mod(&sqr_mod(&lam, p), &x1, p), &x2, p);
        let y3 = sub_mod(&mul_mod(&lam, &sub_mod(&x1, &x3, p), p), &y1, p);
        Some((x3, y3))
    }

    pub fn neg(pp: &Aff, p: &Big) -> Aff {
        pp.map(|(x, y)| (x, sub_mod(&zero(), &y, p)))
    }

    /// MSB-first double-and-add over all LN*64 scalar bits.
    pub fn mul(k: &Big, pt: &Aff, a: &Big, p: &Big) -> Aff {
        let mut acc: Aff = None;
        let mut i = LN * 64;
        while i > 0 {
            i -= 1;
            acc = add(&acc, &acc, a, p);
            if (k[i / 64] >> (i % 64)) & 1 == 1 {
                acc = add(&acc, pt, a, p);
            }
        }
        acc
    }

    /// y^2 == x^3 + a x + b.
    pub fn on_curve(x: &Big, y: &Big, a: &Big, b: &Big, p: &Big) -> bool {
        let lhs = sqr_mod(y, p);
        let x3 = mul_mod(&sqr_mod(x, p), x, p);
        let rhs = add_mod(&add_mod(&x3, &mul_mod(a, x, p), p), b, p);
        lhs == rhs
    }
}

// ===========================================================================
// Hex helpers
// ===========================================================================

fn hex_to_big(s: &str) -> Big {
    assert!(s.len() % 2 == 0, "odd-length hex");
    assert!(s.len() <= 2 * 8 * LN, "hex too wide");
    let mut out = [0u64; LN];
    let nbytes = s.len() / 2;
    for k in 0..nbytes {
        let byte = u8::from_str_radix(&s[2 * k..2 * k + 2], 16).expect("bad hex");
        let pos = nbytes - 1 - k; // s is big-endian
        out[pos / 8] |= (byte as u64) << (8 * (pos % 8));
    }
    out
}

fn big_to_hex(a: &Big, nbytes: usize) -> String {
    let mut s = String::with_capacity(2 * nbytes);
    for k in (0..nbytes).rev() {
        let byte = (a[k / 8] >> (8 * (k % 8))) as u8;
        s.push_str(&format!("{:02x}", byte));
    }
    s
}

// ===========================================================================
// Crate <-> reference conversions
// ===========================================================================

fn p() -> Big {
    hex_to_big(P_HEX)
}

fn a_canon() -> Big {
    // a = -3 mod p
    refimpl::sub_mod(&refimpl::zero(), &hex_to_big("03"), &p())
}

fn b_canon() -> Big {
    hex_to_big(B_HEX)
}

/// Reference limb vector -> the crate's 4-limb canonical form.
fn narrow(a: &Big) -> [u64; FL] {
    assert!(a[FL..].iter().all(|&w| w == 0), "value exceeds 256 bits");
    let mut out = [0u64; FL];
    out.copy_from_slice(&a[..FL]);
    out
}

/// The crate's 4-limb canonical form -> reference limb vector.
fn widen(a: &[u64; FL]) -> Big {
    let mut out = [0u64; LN];
    out[..FL].copy_from_slice(a);
    out
}

/// Crate projective point -> canonical affine coordinates.
fn crate_affine(pt: &G1) -> refimpl::Aff {
    g1_to_affine(pt).map(|(x, y)| (widen(&x), widen(&y)))
}

fn small_scalar(v: u64) -> Big {
    let mut k = [0u64; LN];
    k[0] = v;
    k
}

fn generator_aff() -> refimpl::Aff {
    Some((hex_to_big(GX_HEX), hex_to_big(GY_HEX)))
}

/// The table of (k, x, y) KAT vectors.
fn kat_table() -> Vec<(u64, Big, Big)> {
    vec![
        (2, hex_to_big(K2_X), hex_to_big(K2_Y)),
        (3, hex_to_big(K3_X), hex_to_big(K3_Y)),
        (5, hex_to_big(K5_X), hex_to_big(K5_Y)),
        (10, hex_to_big(K10_X), hex_to_big(K10_Y)),
    ]
}

// ===========================================================================
// (a) Generator and curve constants
// ===========================================================================

#[test]
fn curve_constants_match_crate() {
    let expect = |hex: &str, limbs: &[u64; FL]| {
        assert_eq!(
            hex_to_big(hex),
            widen(limbs),
            "crate constant disagrees with published hex"
        );
    };
    expect(B_HEX, &P224_B);
    expect(GX_HEX, &P224_GX);
    expect(GY_HEX, &P224_GY);
    expect(N_HEX, &P224_N);
    assert_eq!(a_canon(), widen(&P224_A), "crate P224_A is not -3 mod p");
}

#[test]
fn generator_on_curve_both_paths() {
    let gx = hex_to_big(GX_HEX);
    let gy = hex_to_big(GY_HEX);
    assert!(
        refimpl::on_curve(&gx, &gy, &a_canon(), &b_canon(), &p()),
        "G fails the reference on-curve check"
    );
    assert!(
        is_on_curve_affine(&narrow(&gx), &narrow(&gy)),
        "G fails the crate on-curve check"
    );
    let g = g1_generator();
    assert_eq!(crate_affine(&g), Some((gx, gy)));
}

// ===========================================================================
// (b) 2G, 3G, 5G, 10G by g1_double / g1_add against the hardcoded vectors
// ===========================================================================

#[test]
fn reference_reproduces_hardcoded_multiples() {
    let (a, pp) = (a_canon(), p());
    let g = generator_aff();
    for (k, x, y) in kat_table() {
        let r = refimpl::mul(&small_scalar(k), &g, &a, &pp);
        assert_eq!(
            r,
            Some((x, y)),
            "reference {}G disagrees with the hardcoded vector",
            k
        );
        assert!(refimpl::on_curve(&x, &y, &a, &b_canon(), &pp));
    }
}

#[test]
fn crate_matches_hardcoded_multiples_via_add_and_double() {
    let g = g1_generator();
    let g2 = g1_double(&g);
    let g3 = g1_add(&g2, &g);
    let g4 = g1_double(&g2);
    let g5 = g1_add(&g4, &g);
    let g10 = g1_double(&g5);

    let table = kat_table();
    let pts = [(2u64, g2), (3, g3), (5, g5), (10, g10)];
    for (k, pt) in pts.iter() {
        let (_, x, y) = table.iter().find(|(kk, _, _)| kk == k).unwrap();
        assert_eq!(
            crate_affine(pt),
            Some((*x, *y)),
            "crate {}G (add/double chain) disagrees with the KAT",
            k
        );
    }
}

// ===========================================================================
// (c) Scalar multiplication against the same points
// ===========================================================================

#[test]
fn crate_scalar_mul_matches_hardcoded_multiples() {
    let g = g1_generator();
    for (k, x, y) in kat_table() {
        let pt = g1_scalar_mul(&narrow(&small_scalar(k)), &g);
        assert_eq!(
            crate_affine(&pt),
            Some((x, y)),
            "crate g1_scalar_mul({}) disagrees with the KAT",
            k
        );
    }
}

#[test]
fn large_scalar_kat() {
    let k = hex_to_big(KBIG_HEX);
    let want = Some((hex_to_big(KBIG_X), hex_to_big(KBIG_Y)));
    let r = refimpl::mul(&k, &generator_aff(), &a_canon(), &p());
    assert_eq!(r, want, "reference large-scalar result disagrees with KAT");
    let pt = g1_scalar_mul(&narrow(&k), &g1_generator());
    assert_eq!(
        crate_affine(&pt),
        want,
        "crate large-scalar result disagrees with KAT"
    );
}

// ---------------------------------------------------------------------------
// The same KATs through the fixed-base (precomputed table) path
// ---------------------------------------------------------------------------

#[test]
fn base_mul_matches_hardcoded_multiples() {
    for (k, x, y) in kat_table() {
        let pt = g1_scalar_mul_base(&narrow(&small_scalar(k)));
        assert_eq!(
            crate_affine(&pt),
            Some((x, y)),
            "g1_scalar_mul_base({}) disagrees with the KAT",
            k
        );
    }
}

#[test]
fn base_mul_large_scalar_kat() {
    let k = hex_to_big(KBIG_HEX);
    let want = Some((hex_to_big(KBIG_X), hex_to_big(KBIG_Y)));
    assert_eq!(
        crate_affine(&g1_scalar_mul_base(&narrow(&k))),
        want,
        "fixed-base large-scalar result disagrees with the KAT"
    );
    assert!(
        g1_is_identity(&g1_scalar_mul_base(&narrow(&hex_to_big(N_HEX)))),
        "fixed-base n * G != O"
    );
}

#[test]
fn base_mul_agrees_with_reference_on_random_scalars() {
    let mut state: u64 = 0x1357_9bdf_2468_ace0;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let gaff = generator_aff();
    let (a, pp) = (a_canon(), p());
    for _ in 0..4 {
        let mut k = [0u64; LN];
        for i in 0..FL {
            k[i] = next();
        }
        k[FL - 1] &= 0x0000_0000_03ff_ffff; // < 2^218 < n
        let want = refimpl::mul(&k, &gaff, &a, &pp);
        let got = crate_affine(&g1_scalar_mul_base(&narrow(&k)));
        assert_eq!(
            got,
            want,
            "fixed-base and reference disagree on k = {}",
            big_to_hex(&k, 28)
        );
    }
}

#[test]
fn scalar_mul_agrees_with_reference_on_random_scalars() {
    // Deterministic xorshift-generated scalars, masked to 218 bits so they
    // stay below n without needing a modular reduction.
    let mut state: u64 = 0x243f_6a88_85a3_08d3;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let g = g1_generator();
    let gaff = generator_aff();
    let (a, pp) = (a_canon(), p());
    for _ in 0..4 {
        let mut k = [0u64; LN];
        for i in 0..FL {
            k[i] = next();
        }
        k[FL - 1] &= 0x0000_0000_03ff_ffff; // < 2^218 < n
        let want = refimpl::mul(&k, &gaff, &a, &pp);
        let got = crate_affine(&g1_scalar_mul(&narrow(&k), &g));
        assert_eq!(
            got,
            want,
            "crate and reference disagree on k = {}",
            big_to_hex(&k, 28)
        );
    }
}

// ===========================================================================
// (d) Group-law spot checks
// ===========================================================================

#[test]
fn group_law_spot_checks() {
    let g = g1_generator();
    let p2 = g1_scalar_mul(&narrow(&small_scalar(2)), &g);
    let p3 = g1_scalar_mul(&narrow(&small_scalar(3)), &g);
    let p5 = g1_scalar_mul(&narrow(&small_scalar(5)), &g);
    let o = g1_identity();

    for pt in [&g, &p2, &p3, &p5] {
        assert!(g1_is_identity(&g1_add(pt, &g1_neg(pt))), "P + (-P) != O");
    }
    for pt in [&g, &p2, &p3] {
        assert!(g1_eq(&g1_add(pt, &o), pt), "P + O != P");
        assert!(g1_eq(&g1_add(&o, pt), pt), "O + P != P");
    }
    assert!(g1_is_identity(&g1_add(&o, &o)));
    assert!(g1_eq(&g1_add(&p2, &p3), &g1_add(&p3, &p2)));
    let lhs = g1_add(&g1_add(&p2, &p3), &p5);
    let rhs = g1_add(&p2, &g1_add(&p3, &p5));
    assert!(g1_eq(&lhs, &rhs), "addition is not associative on (2G, 3G, 5G)");
    for pt in [&g, &p2, &p3, &p5, &o] {
        assert!(g1_eq(&g1_double(pt), &g1_add(pt, pt)), "2P != P + P");
    }
    assert!(g1_eq(&g1_add(&p2, &p3), &p5), "2G + 3G != 5G");
    let (ax, ay) = g1_to_affine(&p5).expect("5G is not the identity");
    assert!(is_on_curve_affine(&ax, &ay));
    assert!(g1_eq(&g1_from_affine(&ax, &ay), &p5));
}

// ===========================================================================
// (e) Order-related checks
// ===========================================================================

#[test]
fn order_checks() {
    let n = hex_to_big(N_HEX);
    let g = g1_generator();

    let ng = g1_scalar_mul(&narrow(&n), &g);
    assert!(g1_is_identity(&ng), "n * G != O");

    let n1 = refimpl::sub_raw(&n, &small_scalar(1)).0;
    let want = refimpl::neg(&generator_aff(), &p());
    assert_eq!(
        crate_affine(&g1_scalar_mul(&narrow(&n1), &g)),
        want,
        "crate (n-1)G != -G"
    );
    assert_eq!(
        refimpl::mul(&n1, &generator_aff(), &a_canon(), &p()),
        want,
        "reference (n-1)G != -G"
    );

    let gm1 = g1_scalar_mul(&narrow(&n1), &g);
    assert!(g1_is_identity(&g1_add(&gm1, &g)), "(n-1)G + G != O");
}

// ===========================================================================
// (f) The same KATs through the Rocq-emitted addition
// ===========================================================================

/// `tests/extracted_diff.rs` checks the emitted body against the
/// hand-written one on a fixed point set.  This checks it against the KAT
/// vectors themselves, so a shared bug in both Rust paths would still have
/// to survive the reference implementation above.
#[cfg(feature = "extracted")]
mod extracted {
    use super::*;
    use p224::g1_extracted::p224_g1_add_extracted;
    use p224::Fp;

    const PB: usize = 96;

    fn ser(pt: &G1) -> [u8; PB] {
        let mut out = [0u8; PB];
        for (i, w) in pt.x.0.iter().enumerate() {
            out[8 * i..8 * i + 8].copy_from_slice(&w.to_le_bytes());
        }
        for (i, w) in pt.y.0.iter().enumerate() {
            out[32 + 8 * i..32 + 8 * i + 8].copy_from_slice(&w.to_le_bytes());
        }
        for (i, w) in pt.z.0.iter().enumerate() {
            out[64 + 8 * i..64 + 8 * i + 8].copy_from_slice(&w.to_le_bytes());
        }
        out
    }

    fn de(b: &[u8; PB]) -> G1 {
        let rd = |off: usize| {
            let mut limbs = [0u64; FL];
            for (i, l) in limbs.iter_mut().enumerate() {
                let mut w = [0u8; 8];
                w.copy_from_slice(&b[off + 8 * i..off + 8 * i + 8]);
                *l = u64::from_le_bytes(w);
            }
            Fp(limbs)
        };
        G1 {
            x: rd(0),
            y: rd(32),
            z: rd(64),
        }
    }

    fn eadd(a: &G1, b: &G1) -> G1 {
        let mut x = ser(a);
        let mut y = ser(b);
        let mut o = [0u8; PB];
        p224_g1_add_extracted(&mut o, &mut x, &mut y);
        assert_eq!(x, ser(a), "extracted add clobbered its first input");
        assert_eq!(y, ser(b), "extracted add clobbered its second input");
        de(&o)
    }

    #[test]
    fn extracted_add_matches_hardcoded_multiples() {
        let g = g1_generator();
        let g2 = eadd(&g, &g);
        let g3 = eadd(&g2, &g);
        let g4 = eadd(&g2, &g2);
        let g5 = eadd(&g4, &g);
        let g10 = eadd(&g5, &g5);

        let table = kat_table();
        for (k, pt) in [(2u64, g2), (3, g3), (5, g5), (10, g10)].iter() {
            let (_, x, y) = table.iter().find(|(kk, _, _)| kk == k).unwrap();
            assert_eq!(
                crate_affine(pt),
                Some((*x, *y)),
                "extracted {}G disagrees with the KAT",
                k
            );
        }
    }

    #[test]
    fn extracted_group_law_spot_checks() {
        let g = g1_generator();
        let o = g1_identity();
        assert!(g1_is_identity(&eadd(&g, &g1_neg(&g))), "P + (-P) != O");
        assert!(g1_eq(&eadd(&g, &o), &g), "P + O != P");
        assert!(g1_eq(&eadd(&o, &g), &g), "O + P != P");
        assert!(g1_is_identity(&eadd(&o, &o)), "O + O != O");
        let g2 = eadd(&g, &g);
        let g3 = eadd(&g2, &g);
        let g5 = eadd(&g2, &g3);
        assert!(g1_eq(&eadd(&g3, &g2), &g5), "extracted add is not commutative");
        assert!(
            g1_eq(&eadd(&eadd(&g2, &g3), &g5), &eadd(&g2, &eadd(&g3, &g5))),
            "extracted add is not associative"
        );
    }
}
