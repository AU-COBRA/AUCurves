//! Test easy part of final exponentiation in isolation.
//! Easy part: f → f^{(p^6-1)(p^2+1)}
//! If this matches between ours and arkworks (on same input),
//! the bug is in the hard part.

use bn254::*;
use ark_bn254::{Bn254, G1Affine, G2Affine, Fq12};
use ark_ec::{pairing::Pairing, AffineRepr};
use ark_ff::{Field, PrimeField, BigInteger};

fn ark_fq_to_limbs(x: &ark_bn254::Fq) -> [u64; 4] {
    let bi = x.into_bigint();
    [bi.0[0], bi.0[1], bi.0[2], bi.0[3]]
}

fn ark_fp12_to_ours(f: &Fq12) -> Fp12 {
    Fp12 {
        c0: Fp6 {
            c0: Fp2 { c0: Fp(ark_fq_to_limbs(&f.c0.c0.c0)), c1: Fp(ark_fq_to_limbs(&f.c0.c0.c1)) },
            c1: Fp2 { c0: Fp(ark_fq_to_limbs(&f.c0.c1.c0)), c1: Fp(ark_fq_to_limbs(&f.c0.c1.c1)) },
            c2: Fp2 { c0: Fp(ark_fq_to_limbs(&f.c0.c2.c0)), c1: Fp(ark_fq_to_limbs(&f.c0.c2.c1)) },
        },
        c1: Fp6 {
            c0: Fp2 { c0: Fp(ark_fq_to_limbs(&f.c1.c0.c0)), c1: Fp(ark_fq_to_limbs(&f.c1.c0.c1)) },
            c1: Fp2 { c0: Fp(ark_fq_to_limbs(&f.c1.c1.c0)), c1: Fp(ark_fq_to_limbs(&f.c1.c1.c1)) },
            c2: Fp2 { c0: Fp(ark_fq_to_limbs(&f.c1.c2.c0)), c1: Fp(ark_fq_to_limbs(&f.c1.c2.c1)) },
        },
    }
}

fn ours_to_ark_fq(x: &Fp) -> ark_bn254::Fq {
    ark_bn254::Fq::from_bigint(ark_ff::BigInt::new(x.0)).unwrap()
}

fn ours_fp12_to_ark(f: &Fp12) -> Fq12 {
    use ark_bn254::{Fq2 as AFq2, Fq6 as AFq6, Fq12 as AFq12};
    AFq12::new(
        AFq6::new(
            AFq2::new(ours_to_ark_fq(&f.c0.c0.c0), ours_to_ark_fq(&f.c0.c0.c1)),
            AFq2::new(ours_to_ark_fq(&f.c0.c1.c0), ours_to_ark_fq(&f.c0.c1.c1)),
            AFq2::new(ours_to_ark_fq(&f.c0.c2.c0), ours_to_ark_fq(&f.c0.c2.c1)),
        ),
        AFq6::new(
            AFq2::new(ours_to_ark_fq(&f.c1.c0.c0), ours_to_ark_fq(&f.c1.c0.c1)),
            AFq2::new(ours_to_ark_fq(&f.c1.c1.c0), ours_to_ark_fq(&f.c1.c1.c1)),
            AFq2::new(ours_to_ark_fq(&f.c1.c2.c0), ours_to_ark_fq(&f.c1.c2.c1)),
        ),
    )
}

fn main() {
    println!("=== Easy-part final exp isolation ===\n");

    let ark_p = G1Affine::generator();
    let ark_q = G2Affine::generator();
    let ark_ml: Fq12 = Bn254::multi_miller_loop([ark_p], [ark_q]).0;

    // Convert to our representation
    let f_ours = ark_fp12_to_ours(&ark_ml);

    // OUR easy part: conj(f) * inv(f) then frob_p2 * self
    let mut result = Fp12::zero();
    let mut tmp = Fp12::zero();
    bn254::tower::bn254_Fp12_conjugate(&mut result, &f_ours);
    bn254::tower::bn254_Fp12_inv(&mut tmp, &f_ours);
    let r2 = result.clone();
    bn254::tower::bn254_Fp12_mul(&mut result, &r2, &tmp);
    // Easy part 1 done: result = f^{p^6-1}

    let mut g1p2 = Fp2::zero();
    let mut g2p2 = Fp2::zero();
    let mut wp2  = Fp2::zero();
    bn254::tower::bn254_load_gamma1_p2(&mut g1p2);
    bn254::tower::bn254_load_gamma2_p2(&mut g2p2);
    bn254::tower::bn254_load_w_frob_p2_c1(&mut wp2);
    bn254::tower::bn254_Fp12_frobenius_p2(&mut tmp, &result, &g1p2, &g2p2, &wp2);
    let r3 = result.clone();
    bn254::tower::bn254_Fp12_mul(&mut result, &tmp, &r3);
    // Easy part 2 done: result = f^{(p^6-1)(p^2+1)}

    // ARKWORKS easy part: same ops in arkworks Fp12 arithmetic
    let mut ark_result = ark_ml;
    // f^{p^6}: for quadratic Fp12 = Fp6 + Fp6*w, conjugation negates c1
    let mut ark_conj = ark_ml;
    ark_conj.conjugate_in_place();
    let ark_inv = ark_ml.inverse().unwrap();
    ark_result = ark_conj * ark_inv;
    // Easy part 1: f^{p^6-1}

    let mut ark_frob_p2 = ark_result;
    ark_frob_p2.frobenius_map_in_place(2);
    ark_result = ark_frob_p2 * ark_result;
    // Easy part 2: f^{(p^6-1)(p^2+1)}

    // Compare
    let our_c0 = result.c0.c0.c0.0;
    let ark_c0 = ark_fq_to_limbs(&ark_result.c0.c0.c0);
    println!("Our easy-part.c0.c0.c0 = {:016x?}", our_c0);
    println!("Ark easy-part.c0.c0.c0 = {:016x?}", ark_c0);

    if our_c0 == ark_c0 {
        println!("\nEasy parts MATCH → bug is in hard part (bn254_final_exp_hard_dsd).");
    } else {
        println!("\nEasy parts DIFFER → bug is in conjugate, inv, or frobenius_p2.");
    }
}
