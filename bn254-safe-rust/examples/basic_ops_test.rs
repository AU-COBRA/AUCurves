//! Test basic Fp12 operations: conjugate, inv, frobenius_p2.
use bn254::*;
use ark_bn254::Fq12;
use ark_ff::{Field, PrimeField, BigInteger};

fn ark_fq_to_limbs(x: &ark_bn254::Fq) -> [u64; 4] {
    let bi = x.into_bigint(); [bi.0[0], bi.0[1], bi.0[2], bi.0[3]]
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

fn main() {
    // Use a specific Fp12 element (arkworks Miller loop output)
    use ark_bn254::{Bn254, G1Affine, G2Affine};
    use ark_ec::{pairing::Pairing, AffineRepr};
    let ark_f: Fq12 = Bn254::multi_miller_loop(
        [G1Affine::generator()], [G2Affine::generator()]
    ).0;
    let f = ark_fp12_to_ours(&ark_f);

    // Test 1: Fp12 conjugate (negate c1)
    let mut our_conj = Fp12::zero();
    bn254::tower::bn254_Fp12_conjugate(&mut our_conj, &f);
    let mut ark_conj = ark_f;
    ark_conj.conjugate_in_place();

    let m = our_conj.c0.c0.c0.0 == ark_fq_to_limbs(&ark_conj.c0.c0.c0);
    println!("Conjugate c0.c0.c0: {}", if m { "MATCH" } else { "DIFFER" });
    let m = our_conj.c1.c0.c0.0 == ark_fq_to_limbs(&ark_conj.c1.c0.c0);
    println!("Conjugate c1.c0.c0: {}", if m { "MATCH" } else { "DIFFER" });

    // Test 2: Fp12 inverse
    let mut our_inv = Fp12::zero();
    bn254::tower::bn254_Fp12_inv(&mut our_inv, &f);
    let ark_inv = ark_f.inverse().unwrap();

    let m = our_inv.c0.c0.c0.0 == ark_fq_to_limbs(&ark_inv.c0.c0.c0);
    println!("Inverse   c0.c0.c0: {}", if m { "MATCH" } else { "DIFFER" });

    // Test 3: Fp12 multiply (conj * inv)
    let mut our_prod = Fp12::zero();
    bn254::tower::bn254_Fp12_mul(&mut our_prod, &our_conj, &our_inv);
    let ark_prod = ark_conj * ark_inv;

    let m = our_prod.c0.c0.c0.0 == ark_fq_to_limbs(&ark_prod.c0.c0.c0);
    println!("Mul(conj,inv) c0.c0.c0: {}", if m { "MATCH" } else { "DIFFER" });

    // Test 4: Fp12 frobenius_p2
    let mut our_frob = Fp12::zero();
    let mut g1p2 = Fp2::zero();
    let mut g2p2 = Fp2::zero();
    let mut wp2  = Fp2::zero();
    bn254::tower::bn254_load_gamma1_p2(&mut g1p2);
    bn254::tower::bn254_load_gamma2_p2(&mut g2p2);
    bn254::tower::bn254_load_w_frob_p2_c1(&mut wp2);
    bn254::tower::bn254_Fp12_frobenius_p2(&mut our_frob, &our_prod, &g1p2, &g2p2, &wp2);
    let mut ark_frob = ark_prod;
    ark_frob.frobenius_map_in_place(2);

    let m = our_frob.c0.c0.c0.0 == ark_fq_to_limbs(&ark_frob.c0.c0.c0);
    println!("Frob_p2   c0.c0.c0: {}", if m { "MATCH" } else { "DIFFER" });
    let m2 = our_frob.c1.c1.c1.0 == ark_fq_to_limbs(&ark_frob.c1.c1.c1);
    println!("Frob_p2   c1.c1.c1: {}", if m2 { "MATCH" } else { "DIFFER" });
}
