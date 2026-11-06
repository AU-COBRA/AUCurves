//! Benchmark of the three paths on the same inputs: safe Rust (the Rocq-emitted
//! tower / group code over the crate's leaves), Jasmin (feature `jasmin`: the
//! same bedrock2 functions compiled by jasminc, over CryptOpt mul/square and
//! safegcd), and blst.
//!
//!   cargo run --release --features jasmin --example bench_jasmin -- OP PATH [REPS]
//!
//! OP: pairing | g1_smul | g1_msm4096 | g2_smul ; PATH: safe | jasmin | blst.
//! One measurement per process, so that the operations run one at a time.
//! Each repetition times a batch of calls (at least ~0.3 s, at least one call)
//! and reports the time per call; the output is the median and the minimum
//! over REPS (default 11) repetitions, after one warm-up batch.  Operands and
//! results go through `black_box`.

use std::hint::black_box;
use std::time::Instant;

use blst::*;
use bls12_381::group::*;
use bls12_381::{Fp, Fp12, Fp2};

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }
    fn scalar(&mut self) -> [u64; 4] { [self.next(), self.next(), self.next(), self.next()] }
}

fn le_bytes(k: &[u64; 4]) -> [u8; 32] {
    let mut b = [0u8; 32];
    for (i, w) in k.iter().enumerate() {
        b[8 * i..8 * i + 8].copy_from_slice(&w.to_le_bytes());
    }
    b
}

fn g1_blst(k: &[u64; 4]) -> blst_p1_affine {
    let mut p = blst_p1::default();
    let mut a = blst_p1_affine::default();
    unsafe {
        blst_p1_mult(&mut p, blst_p1_generator(), le_bytes(k).as_ptr(), 256);
        blst_p1_to_affine(&mut a, &p);
    }
    a
}
fn g2_blst(k: &[u64; 4]) -> blst_p2_affine {
    let mut p = blst_p2::default();
    let mut a = blst_p2_affine::default();
    unsafe {
        blst_p2_mult(&mut p, blst_p2_generator(), le_bytes(k).as_ptr(), 256);
        blst_p2_to_affine(&mut a, &p);
    }
    a
}
fn g1_ours(a: &blst_p1_affine) -> G1Projective {
    G1Projective::from_affine(&G1Affine { x: Fp(a.x.l), y: Fp(a.y.l) })
}
fn fp2_of(x: &blst_fp2) -> Fp2 { Fp2 { c0: Fp(x.fp[0].l), c1: Fp(x.fp[1].l) } }
fn g2_ours(a: &blst_p2_affine) -> G2Projective {
    G2Projective::from_affine(&G2Affine { x: fp2_of(&a.x), y: fp2_of(&a.y) })
}

fn measure<F: FnMut()>(reps: usize, mut f: F) -> (f64, f64, usize) {
    // calibrate the batch size on one call
    let t = Instant::now();
    f();
    let one = t.elapsed().as_secs_f64();
    let batch = ((0.3 / one.max(1e-9)) as usize).max(1);
    for _ in 0..batch { f(); } // warm-up batch
    let mut v = Vec::with_capacity(reps);
    for _ in 0..reps {
        let t = Instant::now();
        for _ in 0..batch { f(); }
        v.push(t.elapsed().as_secs_f64() / batch as f64);
    }
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    (v[v.len() / 2], v[0], batch)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let op = args.get(1).map(String::as_str).unwrap_or("pairing");
    let path = args.get(2).map(String::as_str).unwrap_or("safe");
    let reps: usize = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(11);
    let mut rng = Rng(0x5eed);

    let (med, min, batch) = match (op, path) {
        ("pairing", _) => {
            let p = g1_blst(&rng.scalar());
            let q = g2_blst(&rng.scalar());
            let (px, py) = (Fp(p.x.l), Fp(p.y.l));
            let (qx, qy) = (fp2_of(&q.x), fp2_of(&q.y));
            let mut out = Fp12::zero();
            match path {
                "safe" => measure(reps, || {
                    bls12_381::pairing(&mut out, black_box(&px), black_box(&py), black_box(&qx), black_box(&qy));
                    black_box(&out);
                }),
                #[cfg(feature = "jasmin")]
                "jasmin" => measure(reps, || {
                    bls12_381::jasmin::pairing(&mut out, black_box(&px), black_box(&py), black_box(&qx), black_box(&qy));
                    black_box(&out);
                }),
                "blst" => {
                    let mut f = blst_fp12::default();
                    let mut r = blst_fp12::default();
                    measure(reps, || unsafe {
                        blst_miller_loop(&mut f, black_box(&q), black_box(&p));
                        blst_final_exp(&mut r, &f);
                        black_box(&r);
                    })
                }
                _ => panic!("unknown path {path}"),
            }
        }
        ("g1_smul", _) => {
            let a = g1_blst(&rng.scalar());
            let k = rng.scalar();
            let p = g1_ours(&a);
            let mut r = G1Projective::identity();
            match path {
                "safe" => measure(reps, || { g1_scalar_mul(&mut r, black_box(&k), black_box(&p)); black_box(&r); }),
                #[cfg(feature = "jasmin")]
                "jasmin" => measure(reps, || {
                    bls12_381::jasmin::g1_scalar_mul(&mut r, black_box(&k), black_box(&p)); black_box(&r);
                }),
                "blst" => {
                    let mut pp = blst_p1::default();
                    unsafe { blst_p1_from_affine(&mut pp, &a) };
                    let kb = le_bytes(&k);
                    let mut o = blst_p1::default();
                    measure(reps, || unsafe {
                        blst_p1_mult(&mut o, black_box(&pp), black_box(kb.as_ptr()), 256);
                        black_box(&o);
                    })
                }
                _ => panic!("unknown path {path}"),
            }
        }
        ("g2_smul", _) => {
            let a = g2_blst(&rng.scalar());
            let k = rng.scalar();
            let p = g2_ours(&a);
            let mut r = G2Projective::identity();
            match path {
                "safe" => measure(reps, || { g2_scalar_mul(&mut r, black_box(&k), black_box(&p)); black_box(&r); }),
                #[cfg(feature = "jasmin")]
                "jasmin" => measure(reps, || {
                    bls12_381::jasmin::g2_scalar_mul(&mut r, black_box(&k), black_box(&p)); black_box(&r);
                }),
                "blst" => {
                    let mut pp = blst_p2::default();
                    unsafe { blst_p2_from_affine(&mut pp, &a) };
                    let kb = le_bytes(&k);
                    let mut o = blst_p2::default();
                    measure(reps, || unsafe {
                        blst_p2_mult(&mut o, black_box(&pp), black_box(kb.as_ptr()), 256);
                        black_box(&o);
                    })
                }
                _ => panic!("unknown path {path}"),
            }
        }
        ("g1_msm4096", _) => {
            let n = 4096;
            // n distinct points: multiples of one random point (blst is slow to
            // generate 4096 independent ones; the MSM does not care).
            let a = g1_blst(&rng.scalar());
            let mut pts_blst = Vec::with_capacity(n);
            let mut acc = blst_p1::default();
            unsafe { blst_p1_from_affine(&mut acc, &a) };
            for _ in 0..n {
                let mut aff = blst_p1_affine::default();
                unsafe { blst_p1_to_affine(&mut aff, &acc) };
                pts_blst.push(aff);
                let mut nx = blst_p1::default();
                unsafe { blst_p1_add_or_double_affine(&mut nx, &acc, &a) };
                acc = nx;
            }
            let scalars: Vec<[u64; 4]> = (0..n).map(|_| rng.scalar()).collect();
            let pts: Vec<G1Projective> = pts_blst.iter().map(g1_ours).collect();
            let mut r = G1Projective::identity();
            match path {
                "safe" => measure(reps, || { g1_msm(&mut r, black_box(&pts), black_box(&scalars)); black_box(&r); }),
                #[cfg(feature = "jasmin")]
                "jasmin" => measure(reps, || {
                    bls12_381::jasmin::g1_msm(&mut r, black_box(&pts), black_box(&scalars)); black_box(&r);
                }),
                "blst" => {
                    let sb: Vec<[u8; 32]> = scalars.iter().map(le_bytes).collect();
                    let pptr: [*const blst_p1_affine; 2] = [pts_blst.as_ptr(), std::ptr::null()];
                    let sptr: [*const u8; 2] = [sb.as_ptr() as *const u8, std::ptr::null()];
                    let sz = unsafe { blst_p1s_mult_pippenger_scratch_sizeof(n) };
                    let mut scratch = vec![0 as limb_t; sz / std::mem::size_of::<limb_t>() + 1];
                    let mut o = blst_p1::default();
                    measure(reps, || unsafe {
                        blst_p1s_mult_pippenger(&mut o, black_box(pptr.as_ptr()), n, black_box(sptr.as_ptr()), 256,
                                                scratch.as_mut_ptr());
                        black_box(&o);
                    })
                }
                _ => panic!("unknown path {path}"),
            }
        }
        _ => panic!("unknown op {op}"),
    };
    println!("{op}\t{path}\tmedian_us={:.1}\tmin_us={:.1}\treps={reps}\tbatch={batch}", med * 1e6, min * 1e6);
}
