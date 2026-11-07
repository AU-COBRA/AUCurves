//! dudect-style timing check (Reparaz, Balasch, Verbauwhede 2017) of the G1 and
//! G2 scalar multiplications: class 0 = a fixed scalar (k = 2^255, Hamming
//! weight 1, or a fixed dense k), class 1 = random scalars, plus a random vs
//! random control; measurements interleaved in random
//! order; Welch's t statistic on the cycle-free wall-clock times (Instant,
//! ns), with the upper 10 % of each class cropped.  |t| > 4.5 is the usual
//! "leak detected" threshold.
//!
//!   cargo run --release --example ct_timing [N]
//!
//! The variable-time g1_scalar_mul is the positive control (it does 1 vs
//! ~128 additions).  With `--features jasmin` the Jasmin-path ladders are measured
//! too.  This is an empirical test on one machine and compiler,
//! not a proof.

use std::hint::black_box;
use std::time::Instant;

use bls12_381::group::*;

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }
}

fn welch(a: &mut Vec<f64>, b: &mut Vec<f64>) -> f64 {
    for v in [&mut *a, &mut *b] {
        v.sort_by(|x, y| x.partial_cmp(y).unwrap());
        let keep = v.len() * 9 / 10;
        v.truncate(keep);
    }
    let stats = |v: &Vec<f64>| {
        let n = v.len() as f64;
        let m = v.iter().sum::<f64>() / n;
        let s2 = v.iter().map(|x| (x - m) * (x - m)).sum::<f64>() / (n - 1.0);
        (n, m, s2)
    };
    let (na, ma, sa) = stats(a);
    let (nb, mb, sb) = stats(b);
    (ma - mb) / (sa / na + sb / nb).sqrt()
}

fn run(name: &str, n: usize, fixed: Option<[u64; 4]>, f: fn(&mut G1Projective, &[u64; 4], &G1Projective)) {
    let mut rng = Rng(5);
    let p = G1Projective::from_affine(&g1_generator());
    let (mut c0, mut c1) = (Vec::new(), Vec::new());
    for _ in 0..n {
        let class = rng.next() & 1;
        let k = if class == 0 && fixed.is_some() { fixed.unwrap() } else { [rng.next(), rng.next(), rng.next(), rng.next()] };
        let mut r = G1Projective::identity();
        let t = Instant::now();
        f(&mut r, black_box(&k), black_box(&p));
        let dt = t.elapsed().as_nanos() as f64;
        black_box(r);
        if class == 0 { c0.push(dt) } else { c1.push(dt) }
    }
    let m0 = c0.iter().sum::<f64>() / c0.len() as f64;
    let m1 = c1.iter().sum::<f64>() / c1.len() as f64;
    let t = welch(&mut c0, &mut c1);
    println!("{:<22} n = {:6}  mean(fixed) = {:9.1} us  mean(random) = {:9.1} us  t = {:8.2}  {}",
             name, n, m0 / 1e3, m1 / 1e3, t, if t.abs() > 4.5 { "LEAK" } else { "no leak detected" });
}

fn run2(name: &str, n: usize, fixed: Option<[u64; 4]>, f: fn(&mut G2Projective, &[u64; 4], &G2Projective)) {
    let mut rng = Rng(5);
    let p = G2Projective::from_affine(&g2_generator());
    let (mut c0, mut c1) = (Vec::new(), Vec::new());
    for _ in 0..n {
        let class = rng.next() & 1;
        let k = if class == 0 && fixed.is_some() { fixed.unwrap() } else { [rng.next(), rng.next(), rng.next(), rng.next()] };
        let mut r = G2Projective::identity();
        let t = Instant::now();
        f(&mut r, black_box(&k), black_box(&p));
        let dt = t.elapsed().as_nanos() as f64;
        black_box(r);
        if class == 0 { c0.push(dt) } else { c1.push(dt) }
    }
    let m0 = c0.iter().sum::<f64>() / c0.len() as f64;
    let m1 = c1.iter().sum::<f64>() / c1.len() as f64;
    let t = welch(&mut c0, &mut c1);
    println!("{:<22} n = {:6}  mean(fixed) = {:9.1} us  mean(random) = {:9.1} us  t = {:8.2}  {}",
             name, n, m0 / 1e3, m1 / 1e3, t, if t.abs() > 4.5 { "LEAK" } else { "no leak detected" });
}

fn main() {
    let n: usize = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(4000);
    // Fixed class: k = 2^255 (Hamming weight 1), then a fixed dense scalar.
    let sparse = [0u64, 0, 0, 1 << 63];
    let dense = [0x9e37_79b9_7f4a_7c15, 0xbf58_476d_1ce4_e5b9, 0x94d0_49bb_1331_11eb, 0xd6e8_feb8_6659_fd93];
    println!("fixed k = 2^255:");
    run("g1_scalar_mul (vt)", n, Some(sparse), g1_scalar_mul);
    run("g1_scalar_mul_ct", n, Some(sparse), g1_scalar_mul_ct);
    println!("fixed dense k:");
    run("g1_scalar_mul (vt)", n, Some(dense), g1_scalar_mul);
    run("g1_scalar_mul_ct", n, Some(dense), g1_scalar_mul_ct);
    println!("control, random vs random:");
    run("g1_scalar_mul (vt)", n, None, g1_scalar_mul);
    run("g1_scalar_mul_ct", n, None, g1_scalar_mul_ct);
    let n2 = n / 3;
    println!("G2, fixed k = 2^255 / fixed dense k / random vs random:");
    run2("g2_scalar_mul (vt)", n2, Some(sparse), g2_scalar_mul);
    run2("g2_scalar_mul_ct", n2, Some(sparse), g2_scalar_mul_ct);
    run2("g2_scalar_mul_ct", n2, Some(dense), g2_scalar_mul_ct);
    run2("g2_scalar_mul_ct", n2, None, g2_scalar_mul_ct);
    // feature `jasmin`: the same ladders compiled by jasminc (bls12_381::jasmin; local leaves of the
    // group module).  In this build the safe-Rust ladders above run over the leaves of
    // generated/bls12_leaves_live.jazz (the dispatcher's _bls12_mul / _bls12_square).
    #[cfg(feature = "jasmin")]
    {
        use bls12_381::jasmin;
        println!("Jasmin path (bls12_381::jasmin):");
        run("jasmin g1_smul_ct", n, Some(sparse), jasmin::g1_scalar_mul_ct);
        run("jasmin g1_smul_ct", n, Some(dense), jasmin::g1_scalar_mul_ct);
        run("jasmin g1_smul_ct", n, None, jasmin::g1_scalar_mul_ct);
        run("jasmin g1_smul (vt)", n, Some(sparse), jasmin::g1_scalar_mul);
        run2("jasmin g2_smul_ct", n2, Some(sparse), jasmin::g2_scalar_mul_ct);
        run2("jasmin g2_smul_ct", n2, Some(dense), jasmin::g2_scalar_mul_ct);
        run2("jasmin g2_smul_ct", n2, None, jasmin::g2_scalar_mul_ct);
    }
}
