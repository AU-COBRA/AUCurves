//! Differential test: the s2n-bignum field kernels against the fiat-rust
//! leaves they replace.
//!
//! Built with `P384_S2N_FIELD=<path>` (see `build.rs`), `p384::fp_mul` and
//! `p384::fp_square` call s2n-bignum's `bignum_montmul_p384` /
//! `bignum_montsqr_p384`, or, for a `.s` path, the re-encoded
//! `bignum_montmul_p384_encoded` for both.  `p384::fp_mul_fiat` /
//! `p384::fp_square_fiat` are always `fiat_p384_mul` / `fiat_p384_square`.
//! Every case asserts bit-for-bit equality of the two and full reduction of
//! the result.  In any other configuration the tests print that they did not
//! run and return.
//!
//!   P384_S2N_FIELD=/path/to/libs2nbignum.a cargo test --offline --release \
//!       -p p384-safe-rust --test s2n_field_diff -- --nocapture

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

const RANDOM_PAIRS: usize = 200_000;
const RANDOM_SQUARES: usize = 200_000;

fn live() -> bool {
    if !p384::S2N_FIELD {
        println!(
            "field configuration is `{}`, not s2n; this test did not run",
            p384::FIELD_CONFIG
        );
    }
    p384::S2N_FIELD
}

fn lt_p(w: &[u64; 6]) -> bool {
    for i in (0..6).rev() {
        if w[i] != P[i] {
            return w[i] < P[i];
        }
    }
    false
}

/// `w - d` for `d <= w`.
fn sub_small(w: &[u64; 6], d: u64) -> [u64; 6] {
    let mut o = *w;
    let (v, mut borrow) = o[0].overflowing_sub(d);
    o[0] = v;
    for limb in o.iter_mut().skip(1) {
        if !borrow {
            break;
        }
        let (v, b) = limb.overflowing_sub(1);
        *limb = v;
        borrow = b;
    }
    o
}

/// Canonical representatives in `[0, p)` at the boundaries of the input
/// domain and of the limb structure of `p`.
fn edges() -> Vec<Fp> {
    let mut one_mont = Fp([0; 6]);
    fp_to_montgomery(&mut one_mont, &FpRaw([1, 0, 0, 0, 0, 0]));
    let all = !0u64;
    let v = vec![
        [0, 0, 0, 0, 0, 0],                                     // 0
        [1, 0, 0, 0, 0, 0],                                     // 1
        [2, 0, 0, 0, 0, 0],
        one_mont.0,                                             // R mod p
        sub_small(&P, 1),                                       // p - 1
        sub_small(&P, 2),                                       // p - 2
        sub_small(&P, 0x1_0000_0000),                           // borrow across limb 0
        [0, 0, 0, 0, 0, 0x8000_0000_0000_0000],                 // 2^383
        [all, all, all, all, all, 0x7fff_ffff_ffff_ffff],       // 2^383 - 1
        [1, 0, 0, 0, 0, 0x8000_0000_0000_0000],                 // 2^383 + 1
        [all, all, all, all, all, 0],                           // 2^320 - 1
        [all, all, all, all, all, 0xffff_ffff_ffff_fffe],       // all-ones but the top bit 0
        [all, all, 0xffff_ffff_ffff_fffd, all, all, all],       // all-ones but limb 2
        [0, 0, 0xffff_ffff_ffff_fffe, all, all, all],           // high half of p
        [all, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, all],
        [all, 0, all, 0, all, 0],
        [0, all, 0, all, 0, all],
        [0xffff_ffff, 0xffff_ffff_0000_0000, 0, 0, 0, 0],       // low two limbs of p
        [0, 0, 0, 1, 0, 0],                                     // 2^192
        [
            0x0123_4567_89ab_cdef,
            0xfedc_ba98_7654_3210,
            all,
            1,
            0x8000_0000_0000_0000,
            0x7fff_ffff_ffff_ffff,
        ],
    ];
    for w in &v {
        assert!(lt_p(w), "edge case not below p: {w:016x?}");
    }
    v.into_iter().map(Fp).collect()
}

/// xorshift64.
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
    /// An element of `[0, p)`, drawn in four shapes: uniform 384-bit words
    /// below `p`; within 2^32 of `p` (the final conditional subtraction);
    /// few-limb values; and words with random limbs forced to all-ones or 0.
    fn fe(&mut self) -> Fp {
        loop {
            let mut w = [0u64; 6];
            for limb in w.iter_mut() {
                *limb = self.word();
            }
            match self.word() % 4 {
                0 => {}
                1 => w = sub_small(&P, (self.word() >> 32) + 1),
                2 => {
                    let keep = (self.word() % 6) as usize + 1;
                    for limb in w.iter_mut().skip(keep) {
                        *limb = 0;
                    }
                }
                _ => {
                    let mask = self.word();
                    for (i, limb) in w.iter_mut().enumerate() {
                        match (mask >> (2 * i)) & 3 {
                            0 => *limb = !0,
                            1 => *limb = 0,
                            _ => {}
                        }
                    }
                }
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
        "mul mismatch ({})\n  a = {:016x?}\n  b = {:016x?}",
        p384::FIELD_CONFIG, a.0, b.0
    );
    assert!(lt_p(&got.0), "mul result not reduced: {:016x?}", got.0);
}

fn check_square(a: &Fp) {
    let mut got = Fp([0; 6]);
    let mut want = Fp([0; 6]);
    fp_square(&mut got, a);
    fp_square_fiat(&mut want, a);
    assert_eq!(
        got.0, want.0,
        "square mismatch ({})\n  a = {:016x?}",
        p384::FIELD_CONFIG, a.0
    );
    assert!(lt_p(&got.0), "square result not reduced: {:016x?}", got.0);
    let mut via_mul = Fp([0; 6]);
    fp_mul(&mut via_mul, a, a);
    assert_eq!(got.0, via_mul.0, "square != mul(x, x)\n  a = {:016x?}", a.0);
}

#[test]
fn configuration() {
    println!("P-384 field configuration: {}", p384::FIELD_CONFIG);
}

#[test]
fn mul_matches_fiat_on_edge_pairs() {
    if !live() {
        return;
    }
    let e = edges();
    for a in &e {
        for b in &e {
            check_mul(a, b);
        }
    }
    println!("mul: {} edge pairs agree", e.len() * e.len());
}

#[test]
fn square_matches_fiat_on_edges() {
    if !live() {
        return;
    }
    let e = edges();
    for a in &e {
        check_square(a);
    }
    println!("square: {} edge inputs agree", e.len());
}

#[test]
fn mul_matches_fiat_on_random() {
    if !live() {
        return;
    }
    let mut rng = Rng(0x2545_f491_4f6c_dd1d);
    for _ in 0..RANDOM_PAIRS {
        let (a, b) = (rng.fe(), rng.fe());
        check_mul(&a, &b);
    }
    println!("mul: {RANDOM_PAIRS} random pairs agree");
}

#[test]
fn square_matches_fiat_on_random() {
    if !live() {
        return;
    }
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    for _ in 0..RANDOM_SQUARES {
        check_square(&rng.fe());
    }
    println!("square: {RANDOM_SQUARES} random inputs agree");
}

#[test]
fn mul_matches_fiat_on_edge_times_random() {
    if !live() {
        return;
    }
    let mut rng = Rng(0x0123_4567_89ab_cdef);
    let e = edges();
    let rounds = 10_000;
    for _ in 0..rounds {
        let r = rng.fe();
        for a in &e {
            check_mul(a, &r);
            check_mul(&r, a);
        }
    }
    println!("mul: {} edge x random pairs agree", 2 * rounds * e.len());
}

/// A chain of products feeds each output back as an input, so the kernels
/// are exercised on their own outputs as well as on generated values.
#[test]
fn chained_products_match_fiat() {
    if !live() {
        return;
    }
    let mut rng = Rng(0xdead_beef_cafe_babe);
    let (mut x, mut xf) = (rng.fe(), Fp([0; 6]));
    xf.0 = x.0;
    let steps = 100_000;
    for i in 0..steps {
        let y = rng.fe();
        let (mut nx, mut nxf) = (Fp([0; 6]), Fp([0; 6]));
        if i % 2 == 0 {
            fp_mul(&mut nx, &x, &y);
            fp_mul_fiat(&mut nxf, &xf, &y);
        } else {
            fp_square(&mut nx, &x);
            fp_square_fiat(&mut nxf, &xf);
        }
        assert_eq!(nx.0, nxf.0, "chain diverged at step {i}");
        x = nx;
        xf = nxf;
    }
    println!("chain: {steps} alternating mul/square steps agree");
}
