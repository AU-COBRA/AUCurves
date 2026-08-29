//! Differential test: the CryptOpt assembly leaves against the fiat-rust
//! leaves they replace.
//!
//! `p384::fp_mul` / `p384::fp_square` are the CryptOpt assembly when
//! `build.rs` linked it and the fiat functions otherwise;
//! `p384::fp_mul_fiat` / `p384::fp_square_fiat` are always the fiat
//! functions.  Every case below asserts bit-for-bit equality of the two,
//! so on a build with the assembly this is a real differential test and on
//! a build without it the assertions are trivially true.
//!
//! The correctness argument for the assembly is CryptOpt's own equivalence
//! check against the fiat-crypto reference (recorded as `validated in ...`
//! in the footer of each `.asm`); this test is the independent numerical
//! corroboration of that claim on the machine the code will run on.

use p384::{fp_mul, fp_mul_fiat, fp_square, fp_square_fiat, fp_to_montgomery, Fp, FpRaw};

/// p = 2^384 - 2^128 - 2^96 + 2^32 - 1, little-endian 64-bit limbs.
const P: [u64; 6] = [
    0x0000_0000_ffff_ffff,
    0xffff_ffff_0000_0000,
    0xffff_ffff_ffff_fffe,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
];

/// `w - d`, for `d` small enough that the result stays non-negative.
fn sub_small(w: &[u64; 6], d: u64) -> [u64; 6] {
    let mut o = *w;
    let (v, mut borrow) = o[0].overflowing_sub(d);
    o[0] = v;
    for i in 1..6 {
        if !borrow {
            break;
        }
        let (v, b) = o[i].overflowing_sub(1);
        o[i] = v;
        borrow = b;
    }
    o
}

/// Field elements are Montgomery-domain representatives in `[0, p)`; any
/// such limb vector is a legitimate input to both leaves.
fn edges() -> Vec<Fp> {
    // R mod p -- one in the Montgomery domain.
    let mut one = Fp([0; 6]);
    fp_to_montgomery(&mut one, &FpRaw([1, 0, 0, 0, 0, 0]));
    vec![
        Fp([0; 6]),
        Fp([1, 0, 0, 0, 0, 0]),
        Fp(sub_small(&P, 1)),
        Fp(sub_small(&P, 2)),
        one,
        // Saturated low half, zero high half.
        Fp([!0, !0, !0, 0, 0, 0]),
        // Only the high limb set.
        Fp([0, 0, 0, 0, 0, !0]),
        // Straddles the two structured low limbs of p.
        Fp([0x0000_0000_ffff_fffe, 0xffff_ffff_0000_0000, 0, 0, 0, 0]),
        Fp([!0, 0, !0, 0, !0, 0]),
        Fp([0, !0, 0, !0, 0, !0]),
        Fp([
            0x0123_4567_89ab_cdef,
            0xfedc_ba98_7654_3210,
            !0,
            1,
            0x8000_0000_0000_0000,
            0x7fff_ffff_ffff_ffff,
        ]),
    ]
}

/// Below p? Only used to keep the random generator inside the input domain.
fn lt_p(w: &[u64; 6]) -> bool {
    for i in (0..6).rev() {
        if w[i] != P[i] {
            return w[i] < P[i];
        }
    }
    false
}

struct Rng(u64);
impl Rng {
    fn word(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    /// A uniform-ish element of `[0, p)`.  Half the draws are placed within
    /// 4096 of p on purpose -- that is where the final conditional
    /// subtraction of the Montgomery reduction is exercised.
    fn fe(&mut self) -> Fp {
        loop {
            let mut w = [0u64; 6];
            for i in 0..6 {
                w[i] = self.word();
            }
            if w[0] & 1 == 0 {
                w = sub_small(&P, (self.word() % 4096) + 1);
            }
            if lt_p(&w) {
                return Fp(w);
            }
        }
    }
}

fn check_mul(a: &Fp, b: &Fp) {
    let mut got = Fp([0; 6]);
    let mut want = Fp([0; 6]);
    fp_mul(&mut got, a, b);
    fp_mul_fiat(&mut want, a, b);
    assert_eq!(
        got.0, want.0,
        "mul mismatch\n  a = {:016x?}\n  b = {:016x?}",
        a.0, b.0
    );
    // The result must itself be a valid input, i.e. fully reduced.
    assert!(lt_p(&got.0), "mul result not reduced: {:016x?}", got.0);
}

fn check_square(a: &Fp) {
    let mut got = Fp([0; 6]);
    let mut want = Fp([0; 6]);
    fp_square(&mut got, a);
    fp_square_fiat(&mut want, a);
    assert_eq!(got.0, want.0, "square mismatch\n  a = {:016x?}", a.0);
    assert!(lt_p(&got.0), "square result not reduced: {:016x?}", got.0);
    // Squaring and self-multiplication must agree.
    let mut via_mul = Fp([0; 6]);
    fp_mul(&mut via_mul, a, a);
    assert_eq!(got.0, via_mul.0, "square != mul(x,x)\n  a = {:016x?}", a.0);
}

#[test]
fn which_backend() {
    // Not an assertion about which path is taken -- just a record in the
    // test log, so a run that silently fell back to fiat is visible.
    println!(
        "P-384 field leaves: {}",
        if p384::CRYPTOPT_ASM {
            "CryptOpt assembly (differential test is live)"
        } else {
            "fiat-rust (no assembly linked; differential test is vacuous)"
        }
    );
}

#[test]
fn mul_matches_fiat_on_edges() {
    let e = edges();
    for a in &e {
        for b in &e {
            check_mul(a, b);
        }
    }
}

#[test]
fn square_matches_fiat_on_edges() {
    for a in &edges() {
        check_square(a);
    }
}

#[test]
fn mul_matches_fiat_on_random() {
    let mut rng = Rng(0x2545_f491_4f6c_dd1d);
    for _ in 0..200_000 {
        let (a, b) = (rng.fe(), rng.fe());
        check_mul(&a, &b);
    }
}

#[test]
fn square_matches_fiat_on_random() {
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    for _ in 0..200_000 {
        let a = rng.fe();
        check_square(&a);
    }
}

#[test]
fn mul_matches_fiat_on_edge_times_random() {
    let mut rng = Rng(0x0123_4567_89ab_cdef);
    let e = edges();
    for _ in 0..20_000 {
        let r = rng.fe();
        for a in &e {
            check_mul(a, &r);
            check_mul(&r, a);
        }
    }
}

/// Montgomery multiplication is commutative and distributes over addition;
/// a wrong reduction would break the second identity even where it happens
/// to agree with fiat on the first.
#[test]
fn algebraic_identities() {
    use p384::{fp_add, fp_sub};
    let mut rng = Rng(0xdead_beef_cafe_babe);
    for _ in 0..100_000 {
        let (a, b, c) = (rng.fe(), rng.fe(), rng.fe());

        let (mut ab, mut ba) = (Fp([0; 6]), Fp([0; 6]));
        fp_mul(&mut ab, &a, &b);
        fp_mul(&mut ba, &b, &a);
        assert_eq!(ab.0, ba.0, "mul not commutative");

        // a * (b + c) == a*b + a*c
        let mut bc = Fp([0; 6]);
        fp_add(&mut bc, &b, &c);
        let mut lhs = Fp([0; 6]);
        fp_mul(&mut lhs, &a, &bc);
        let mut ac = Fp([0; 6]);
        fp_mul(&mut ac, &a, &c);
        let mut rhs = Fp([0; 6]);
        fp_add(&mut rhs, &ab, &ac);
        assert_eq!(lhs.0, rhs.0, "mul does not distribute over add");

        // (a - b) * a == a*a - b*a
        let mut amb = Fp([0; 6]);
        fp_sub(&mut amb, &a, &b);
        let mut l2 = Fp([0; 6]);
        fp_mul(&mut l2, &amb, &a);
        let mut aa = Fp([0; 6]);
        fp_square(&mut aa, &a);
        let mut r2 = Fp([0; 6]);
        fp_sub(&mut r2, &aa, &ba);
        assert_eq!(l2.0, r2.0, "mul does not distribute over sub");
    }
}
