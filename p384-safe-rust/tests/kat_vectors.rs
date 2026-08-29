//! Known-answer tests for the P-384 (secp384r1) group operations.
//!
//! Zero external dependencies: everything needed to check the crate is in
//! this file.
//!
//! Field encoding.  The crate stores field elements in Montgomery form with
//! R = 2^384 modulo
//!   p = 2^384 - 2^128 - 2^96 + 2^32 - 1
//! (`fiat-crypto/fiat-rust/src/p384_64.rs`, header line `m = ...`).  The
//! vectors below are canonical big-endian hex, i.e. *not* Montgomery form;
//! conversion happens inside the test.
//!
//! # Provenance of the vectors
//!
//! * The curve parameters `p`, `a = -3`, `b`, `G = (Gx, Gy)` and the group
//!   order `n` are hardcoded from the published FIPS 186-4 / SEC 2 v2.0
//!   secp384r1 parameters — external inputs, not outputs of this crate.
//!   `curve_constants_match_crate` checks the crate's own copies against
//!   them.
//!
//! * `2G` and `3G` were transcribed from the republished NIST P-384 "k*G"
//!   table before being computed here, and the reference implementation in
//!   this file reproduces them exactly.  Those two are independent KATs.
//!
//! * `5G`, `10G` and the large-scalar vector are **not** externally sourced.
//!   They were produced by the independent reference implementation in this
//!   file (module `refimpl`: textbook affine chord-and-tangent formulas over
//!   schoolbook non-Montgomery big-integer arithmetic with a binary extended
//!   GCD inverse) and cross-checked against the crate, which uses
//!   homogeneous projective Renes-Costello-Batina complete addition over
//!   fiat-crypto's word-by-word Montgomery leaves and a Bernstein-Yang
//!   inverse.  They are regression anchors that are additionally agreed on
//!   by two unrelated implementations of the group law over two unrelated
//!   field representations — not published KATs.

#![allow(clippy::needless_range_loop)]

use p384::group::*;
use p384::{fp_from_montgomery, fp_mul, fp_to_montgomery, Fp, FpRaw};

// ===========================================================================
// Published curve parameters (FIPS 186-4 D.1.2.4 / SEC 2 v2.0 section 2.5.1)
// ===========================================================================

const P_HEX: &str = concat!(
    "ffffffffffffffffffffffffffffffffffffffffffffffff",
    "fffffffffffffffeffffffff0000000000000000ffffffff"
);
const B_HEX: &str = concat!(
    "b3312fa7e23ee7e4988e056be3f82d19181d9c6efe814112",
    "0314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef"
);
const GX_HEX: &str = concat!(
    "aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b98",
    "59f741e082542a385502f25dbf55296c3a545e3872760ab7"
);
const GY_HEX: &str = concat!(
    "3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147c",
    "e9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f"
);
const N_HEX: &str = concat!(
    "ffffffffffffffffffffffffffffffffffffffffffffffff",
    "c7634d81f4372ddf581a0db248b0a77aecec196accc52973"
);

// ===========================================================================
// KAT vectors: affine coordinates of k*G, canonical (non-Montgomery) hex.
// Reference-derived; see the provenance note in the module header.
// ===========================================================================

const K2_X: &str = concat!(
    "08d999057ba3d2d969260045c55b97f089025959a6f434d6",
    "51d207d19fb96e9e4fe0e86ebe0e64f85b96a9c75295df61"
);
const K2_Y: &str = concat!(
    "8e80f1fa5b1b3cedb7bfe8dffd6dba74b275d875bc6cc43e",
    "904e505f256ab4255ffd43e94d39e22d61501e700a940e80"
);
const K3_X: &str = concat!(
    "077a41d4606ffa1464793c7e5fdc7d98cb9d3910202dcd06",
    "bea4f240d3566da6b408bbae5026580d02d7e5c70500c831"
);
const K3_Y: &str = concat!(
    "c995f7ca0b0c42837d0bbe9602a9fc998520b41c85115aa5",
    "f7684c0edc111eacc24abd6be4b5d298b65f28600a2f1df1"
);
const K5_X: &str = concat!(
    "11de24a2c251c777573cac5ea025e467f208e51dbff98fc5",
    "4f6661cbe56583b037882f4a1ca297e60abcdbc3836d84bc"
);
const K5_Y: &str = concat!(
    "8fa696c77440f92d0f5837e90a00e7c5284b447754d5dee8",
    "8c986533b6901aeb3177686d0ae8fb33184414abe6c1713a"
);
const K10_X: &str = concat!(
    "a669c5563bd67eec678d29d6ef4fde864f372d90b79b9e88",
    "931d5c29291238cced8e85ab507bf91aa9cb2d13186658fb"
);
const K10_Y: &str = concat!(
    "a988b72ae7c1279f22d9083db5f0ecddf70119550c183c31",
    "c502df78c3b705a8296d8195248288d997784f6ab73a21dd"
);

/// A fixed 384-bit scalar below n, used for the large-scalar KAT.
const KBIG_HEX: &str = concat!(
    "1a2b3c4d5e6f708192a3b4c5d6e7f8091a2b3c4d5e6f7081",
    "92a3b4c5d6e7f8090f1e2d3c4b5a69788796a5b4c3d2e1f0"
);
const KBIG_X: &str = concat!(
    "f9fae7bc08bc185e6b0625a463728a897ad782a47561b3ca",
    "829d416f538d3877d8d9971f5af7a2b478eca52f1633f8fc"
);
const KBIG_Y: &str = concat!(
    "e8e1edad08b055fdb44f080330243362d7eccc2a3be92d07",
    "c047a76bc909bd158ddb43481eeb91f3d277ee1a748bc355"
);

// ===========================================================================
// Independent reference implementation
// ===========================================================================

/// Working width in 64-bit limbs.  The modulus needs 6; the reference uses
/// 12 so that a full 6x6 schoolbook product and the `x + p` step of the
/// binary extended GCD both fit without a separate carry word.
const LN: usize = 12;

/// Number of limbs in the crate's field representation.
const FL: usize = 6;

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

/// Canonical limbs -> crate Montgomery `Fp`.
fn to_fp(a: &Big) -> Fp {
    assert!(a[FL..].iter().all(|&w| w == 0), "value exceeds 384 bits");
    let mut raw = FpRaw([0u64; FL]);
    raw.0.copy_from_slice(&a[..FL]);
    let mut out = Fp([0u64; FL]);
    fp_to_montgomery(&mut out, &raw);
    out
}

/// Crate Montgomery `Fp` -> canonical limbs.
fn from_fp(x: &Fp) -> Big {
    let mut raw = FpRaw([0u64; FL]);
    fp_from_montgomery(&mut raw, x);
    let mut out = [0u64; LN];
    out[..FL].copy_from_slice(&raw.0);
    out
}

/// Crate projective point -> canonical affine coordinates.
fn crate_affine(pt: &G1) -> refimpl::Aff {
    g1_to_affine(pt).map(|(x, y)| (from_fp(&x), from_fp(&y)))
}

/// Projective equality by cross-multiplication (test-local; the crate keeps
/// its own copy private).
fn g1_eq(pt: &G1, q: &G1) -> bool {
    let (pi, qi) = (g1_is_identity(pt), g1_is_identity(q));
    if pi || qi {
        return pi == qi;
    }
    let mut l = Fp([0u64; FL]);
    let mut r = Fp([0u64; FL]);
    fp_mul(&mut l, &pt.x, &q.z);
    fp_mul(&mut r, &q.x, &pt.z);
    if l.0 != r.0 {
        return false;
    }
    fp_mul(&mut l, &pt.y, &q.z);
    fp_mul(&mut r, &q.y, &pt.z);
    l.0 == r.0
}

/// 6 little-endian u64 limbs (the crate's `g1_scalar_mul` input format).
fn scalar_limbs(k: &Big) -> [u64; FL] {
    assert!(k[FL..].iter().all(|&w| w == 0), "scalar exceeds 384 bits");
    let mut out = [0u64; FL];
    out.copy_from_slice(&k[..FL]);
    out
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
        let want = hex_to_big(hex);
        let mut got = [0u64; LN];
        got[..FL].copy_from_slice(limbs);
        assert_eq!(want, got, "crate constant disagrees with published hex");
    };
    expect(B_HEX, &B_CANON);
    expect(GX_HEX, &GX_CANON);
    expect(GY_HEX, &GY_CANON);
    expect(N_HEX, &N_CANON);
    // a = -3 mod p, computed from the published p
    let mut a_from_crate = [0u64; LN];
    a_from_crate[..FL].copy_from_slice(&A_CANON);
    assert_eq!(a_canon(), a_from_crate, "crate A_CANON is not -3 mod p");
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
        g1_is_on_curve_affine(&to_fp(&gx), &to_fp(&gy)),
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
        let pt = g1_scalar_mul(&scalar_limbs(&small_scalar(k)), &g);
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
    let pt = g1_scalar_mul(&scalar_limbs(&k), &g1_generator());
    assert_eq!(
        crate_affine(&pt),
        want,
        "crate large-scalar result disagrees with KAT"
    );
}

#[test]
fn base_mul_matches_hardcoded_multiples() {
    for (k, x, y) in kat_table() {
        let pt = g1_scalar_mul_base(&scalar_limbs(&small_scalar(k)));
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
        crate_affine(&g1_scalar_mul_base(&scalar_limbs(&k))),
        want,
        "fixed-base large-scalar result disagrees with the KAT"
    );
    assert!(
        g1_is_identity(&g1_scalar_mul_base(&scalar_limbs(&hex_to_big(N_HEX)))),
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
        k[FL - 1] &= 0x03ff_ffff_ffff_ffff; // < 2^378 < n
        let want = refimpl::mul(&k, &gaff, &a, &pp);
        let got = crate_affine(&g1_scalar_mul_base(&scalar_limbs(&k)));
        assert_eq!(
            got,
            want,
            "fixed-base and reference disagree on k = {}",
            big_to_hex(&k, 48)
        );
    }
}

#[test]
fn scalar_mul_agrees_with_reference_on_random_scalars() {
    // Deterministic xorshift-generated scalars, masked to 378 bits so they
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
        k[FL - 1] &= 0x03ff_ffff_ffff_ffff; // < 2^378 < n
        let want = refimpl::mul(&k, &gaff, &a, &pp);
        let got = crate_affine(&g1_scalar_mul(&scalar_limbs(&k), &g));
        assert_eq!(
            got,
            want,
            "crate and reference disagree on k = {}",
            big_to_hex(&k, 48)
        );
    }
}

// ===========================================================================
// (d) Group-law spot checks
// ===========================================================================

#[test]
fn group_law_spot_checks() {
    let g = g1_generator();
    let p2 = g1_scalar_mul(&scalar_limbs(&small_scalar(2)), &g);
    let p3 = g1_scalar_mul(&scalar_limbs(&small_scalar(3)), &g);
    let p5 = g1_scalar_mul(&scalar_limbs(&small_scalar(5)), &g);
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
    assert!(g1_is_on_curve_affine(&ax, &ay));
    assert!(g1_eq(&g1_from_affine(&ax, &ay), &p5));
}

// ===========================================================================
// (e) Order-related checks
// ===========================================================================

#[test]
fn order_checks() {
    let n = hex_to_big(N_HEX);
    let g = g1_generator();

    let ng = g1_scalar_mul(&scalar_limbs(&n), &g);
    assert!(g1_is_identity(&ng), "n * G != O");

    let n1 = refimpl::sub_raw(&n, &small_scalar(1)).0;
    let want = refimpl::neg(&generator_aff(), &p());
    assert_eq!(
        crate_affine(&g1_scalar_mul(&scalar_limbs(&n1), &g)),
        want,
        "crate (n-1)G != -G"
    );
    assert_eq!(
        refimpl::mul(&n1, &generator_aff(), &a_canon(), &p()),
        want,
        "reference (n-1)G != -G"
    );

    let gm1 = g1_scalar_mul(&scalar_limbs(&n1), &g);
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
    use p384::g1_extracted::p384_g1_add_extracted;

    const PB: usize = 144;
    const CB: usize = 48; // bytes per coordinate

    fn ser(pt: &G1) -> [u8; PB] {
        let mut out = [0u8; PB];
        for (i, w) in pt.x.0.iter().enumerate() {
            out[8 * i..8 * i + 8].copy_from_slice(&w.to_le_bytes());
        }
        for (i, w) in pt.y.0.iter().enumerate() {
            out[CB + 8 * i..CB + 8 * i + 8].copy_from_slice(&w.to_le_bytes());
        }
        for (i, w) in pt.z.0.iter().enumerate() {
            out[2 * CB + 8 * i..2 * CB + 8 * i + 8].copy_from_slice(&w.to_le_bytes());
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
            y: rd(CB),
            z: rd(2 * CB),
        }
    }

    fn eadd(a: &G1, b: &G1) -> G1 {
        let mut x = ser(a);
        let mut y = ser(b);
        let mut o = [0u8; PB];
        p384_g1_add_extracted(&mut o, &mut x, &mut y);
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
