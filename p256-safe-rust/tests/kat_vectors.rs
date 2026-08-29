//! Known-answer tests for the P-256 (secp256r1) group operations.
//!
//! Zero external dependencies: everything needed to check the crate is in
//! this file.
//!
//! Field encoding.  The crate stores field elements in Montgomery form with
//! R = 2^256 modulo
//!   p = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
//!     = 2^256 - 2^224 + 2^192 + 2^96 - 1
//! (`fiat-crypto/fiat-rust/src/p256_64.rs`, header line `m = ...`).  The
//! vectors below are written as canonical big-endian hex, i.e. *not* in
//! Montgomery form; conversion happens inside the test.
//!
//! # Provenance of the vectors
//!
//! Two facts must be separated.
//!
//! * The curve parameters `p`, `a = -3`, `b`, `G = (Gx, Gy)` and the group
//!   order `n` are hardcoded here from the published FIPS 186-4 / SEC 2 v2.0
//!   secp256r1 parameters.  They are external inputs, not outputs of this
//!   crate.  The test `curve_constants_match_crate` checks that the crate's
//!   own copies (`group::B_CANON`, `GX_CANON`, `GY_CANON`, `N_CANON`) agree
//!   with them.
//!
//! * `2G`, `3G`, `5G`, `10G` are the values from the widely republished
//!   NIST P-256 "k*G" table (k = 1..20).  They were transcribed here before
//!   being computed, and they are additionally *recomputed inside this file*
//!   by an independent reference implementation: textbook affine
//!   chord-and-tangent formulas over schoolbook non-Montgomery big-integer
//!   arithmetic with a binary extended GCD inverse (module `refimpl`
//!   below).  That reference shares no code with the crate under test,
//!   which uses homogeneous projective Renes-Costello-Batina complete
//!   addition over fiat-crypto's word-by-word Montgomery leaves and a
//!   Bernstein-Yang inverse.  These four vectors are therefore independent
//!   KATs, confirmed by two unrelated implementations.
//!
//! * The large-scalar vector (`KBIG_*`) has no published counterpart known
//!   to us.  It was produced by the reference implementation in this file
//!   and agrees with the crate, so it is an independent cross-implementation
//!   check but not an externally sourced KAT; treat it as a regression
//!   anchor plus a reference-agreement check.
//!
//! Every vector is checked twice: `reference_reproduces_hardcoded_multiples`
//! fails if the hex and the reference disagree, and the `crate_*` tests fail
//! if the hex and the crate disagree.

#![allow(clippy::needless_range_loop)]

use p256::group::*;
use p256::{fp_from_montgomery, fp_mul, fp_to_montgomery, Fp, FpRaw};

// ===========================================================================
// Published curve parameters (FIPS 186-4 D.1.2.3 / SEC 2 v2.0 section 2.4.2)
// ===========================================================================

const P_HEX: &str = "ffffffff00000001000000000000000000000000ffffffffffffffffffffffff";
const B_HEX: &str = "5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b";
const GX_HEX: &str = "6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296";
const GY_HEX: &str = "4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5";
const N_HEX: &str = "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551";

// ===========================================================================
// KAT vectors: affine coordinates of k*G, canonical (non-Montgomery) hex.
// Cross-checked by the reference implementation in `refimpl` and by the
// crate; see the provenance note in the module header.
// ===========================================================================

const K2_X: &str = "7cf27b188d034f7e8a52380304b51ac3c08969e277f21b35a60b48fc47669978";
const K2_Y: &str = "07775510db8ed040293d9ac69f7430dbba7dade63ce982299e04b79d227873d1";

const K3_X: &str = "5ecbe4d1a6330a44c8f7ef951d4bf165e6c6b721efada985fb41661bc6e7fd6c";
const K3_Y: &str = "8734640c4998ff7e374b06ce1a64a2ecd82ab036384fb83d9a79b127a27d5032";

const K5_X: &str = "51590b7a515140d2d784c85608668fdfef8c82fd1f5be52421554a0dc3d033ed";
const K5_Y: &str = "e0c17da8904a727d8ae1bf36bf8a79260d012f00d4d80888d1d0bb44fda16da4";

const K10_X: &str = "cef66d6b2a3a993e591214d1ea223fb545ca6c471c48306e4c36069404c5723f";
const K10_Y: &str = "878662a229aaae906e123cdd9d3b4c10590ded29fe751eeeca34bbaa44af0773";

/// A fixed 256-bit scalar below n, used for the large-scalar KAT.
const KBIG_HEX: &str = "1a2b3c4d5e6f708192a3b4c5d6e7f8091a2b3c4d5e6f708192a3b4c5d6e7f809";
const KBIG_X: &str = "b5a104b6caadfa15a6fb9eb3939237284d404e9d9486b706411457a16f12e84a";
const KBIG_Y: &str = "18bbebd97e525867075442bd530ea4d29ee7ad873a82a62e804be3c08e34c9d6";

// ===========================================================================
// Independent reference implementation
// ===========================================================================

/// Working width in 64-bit limbs.  The modulus needs 4; the reference uses
/// 8 so that a full 4x4 schoolbook product and the `x + p` step of the
/// binary extended GCD both fit without a separate carry word.
const LN: usize = 8;

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
        // s is big-endian: byte k has weight 8*(nbytes-1-k)
        let pos = nbytes - 1 - k;
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
    assert!(a[4..].iter().all(|&w| w == 0), "value exceeds 256 bits");
    let mut raw = FpRaw([0u64; 4]);
    raw.0.copy_from_slice(&a[..4]);
    let mut out = Fp([0u64; 4]);
    fp_to_montgomery(&mut out, &raw);
    out
}

/// Crate Montgomery `Fp` -> canonical limbs.
fn from_fp(x: &Fp) -> Big {
    let mut raw = FpRaw([0u64; 4]);
    fp_from_montgomery(&mut raw, x);
    let mut out = [0u64; LN];
    out[..4].copy_from_slice(&raw.0);
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
    let mut l = Fp([0u64; 4]);
    let mut r = Fp([0u64; 4]);
    fp_mul(&mut l, &pt.x, &q.z);
    fp_mul(&mut r, &q.x, &pt.z);
    if l.0 != r.0 {
        return false;
    }
    fp_mul(&mut l, &pt.y, &q.z);
    fp_mul(&mut r, &q.y, &pt.z);
    l.0 == r.0
}

/// 32-byte big-endian scalar (the crate's `g1_scalar_mul` input format).
fn scalar_be(k: &Big) -> [u8; 32] {
    assert!(k[4..].iter().all(|&w| w == 0), "scalar exceeds 256 bits");
    let mut out = [0u8; 32];
    for i in 0..32 {
        out[31 - i] = (k[i / 8] >> (8 * (i % 8))) as u8;
    }
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
    let expect = |hex: &str, limbs: &[u64; 4]| {
        let want = hex_to_big(hex);
        let mut got = [0u64; LN];
        got[..4].copy_from_slice(limbs);
        assert_eq!(want, got, "crate constant disagrees with published hex");
    };
    expect(B_HEX, &B_CANON);
    expect(GX_HEX, &GX_CANON);
    expect(GY_HEX, &GY_CANON);
    expect(N_HEX, &N_CANON);
}

#[test]
fn generator_on_curve_both_paths() {
    let gx = hex_to_big(GX_HEX);
    let gy = hex_to_big(GY_HEX);
    // reference
    assert!(
        refimpl::on_curve(&gx, &gy, &a_canon(), &b_canon(), &p()),
        "G fails the reference on-curve check"
    );
    // crate
    assert!(
        g1_affine_on_curve(&to_fp(&gx), &to_fp(&gy)),
        "G fails the crate on-curve check"
    );
    // and the crate's own generator is exactly (Gx : Gy : 1)
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
        let pt = g1_scalar_mul(&scalar_be(&small_scalar(k)), &g);
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
    // reference
    let r = refimpl::mul(&k, &generator_aff(), &a_canon(), &p());
    assert_eq!(r, want, "reference large-scalar result disagrees with KAT");
    // crate
    let pt = g1_scalar_mul(&scalar_be(&k), &g1_generator());
    assert_eq!(crate_affine(&pt), want, "crate large-scalar result disagrees with KAT");
}

#[test]
fn scalar_mul_agrees_with_reference_on_random_scalars() {
    // Deterministic xorshift-generated scalars, reduced to 250 bits so they
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
        for i in 0..4 {
            k[i] = next();
        }
        k[3] &= 0x03ff_ffff_ffff_ffff; // < 2^250 < n
        let want = refimpl::mul(&k, &gaff, &a, &pp);
        let got = crate_affine(&g1_scalar_mul(&scalar_be(&k), &g));
        assert_eq!(got, want, "crate and reference disagree on k = {}", big_to_hex(&k, 32));
    }
}

// ===========================================================================
// (d) Group-law spot checks
// ===========================================================================

#[test]
fn group_law_spot_checks() {
    let g = g1_generator();
    let p2 = g1_scalar_mul(&scalar_be(&small_scalar(2)), &g);
    let p3 = g1_scalar_mul(&scalar_be(&small_scalar(3)), &g);
    let p5 = g1_scalar_mul(&scalar_be(&small_scalar(5)), &g);
    let o = g1_identity();

    // P + (-P) = O
    for pt in [&g, &p2, &p3, &p5] {
        assert!(g1_is_identity(&g1_add(pt, &g1_neg(pt))), "P + (-P) != O");
    }
    // P + O = O + P = P
    for pt in [&g, &p2, &p3] {
        assert!(g1_eq(&g1_add(pt, &o), pt), "P + O != P");
        assert!(g1_eq(&g1_add(&o, pt), pt), "O + P != P");
    }
    // O + O = O
    assert!(g1_is_identity(&g1_add(&o, &o)));
    // commutativity
    assert!(g1_eq(&g1_add(&p2, &p3), &g1_add(&p3, &p2)));
    // associativity on three distinct points
    let lhs = g1_add(&g1_add(&p2, &p3), &p5);
    let rhs = g1_add(&p2, &g1_add(&p3, &p5));
    assert!(g1_eq(&lhs, &rhs), "addition is not associative on (2G, 3G, 5G)");
    // doubling agrees with self-addition
    for pt in [&g, &p2, &p3, &p5, &o] {
        assert!(g1_eq(&g1_double(pt), &g1_add(pt, pt)), "2P != P + P");
    }
    // 2G + 3G = 5G
    assert!(g1_eq(&g1_add(&p2, &p3), &p5), "2G + 3G != 5G");
    // affine round trip
    let (ax, ay) = g1_to_affine(&p5).expect("5G is not the identity");
    assert!(g1_affine_on_curve(&ax, &ay));
    assert!(g1_eq(&g1_from_affine(&ax, &ay), &p5));
}

// ===========================================================================
// (e) Order-related checks
// ===========================================================================

#[test]
fn order_checks() {
    let n = hex_to_big(N_HEX);
    let g = g1_generator();

    // n * G = O
    let ng = g1_scalar_mul(&scalar_be(&n), &g);
    assert!(g1_is_identity(&ng), "n * G != O");

    // (n-1) * G = -G, both in the crate and in the reference
    let n1 = refimpl::sub_raw(&n, &small_scalar(1)).0;
    let want = refimpl::neg(&generator_aff(), &p());
    assert_eq!(
        crate_affine(&g1_scalar_mul(&scalar_be(&n1), &g)),
        want,
        "crate (n-1)G != -G"
    );
    assert_eq!(
        refimpl::mul(&n1, &generator_aff(), &a_canon(), &p()),
        want,
        "reference (n-1)G != -G"
    );

    // (n-1)G + G = O
    let gm1 = g1_scalar_mul(&scalar_be(&n1), &g);
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
    use p256::g1_extracted::p256_g1_add_extracted;

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
            let mut limbs = [0u64; 4];
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
        p256_g1_add_extracted(&mut o, &mut x, &mut y);
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
