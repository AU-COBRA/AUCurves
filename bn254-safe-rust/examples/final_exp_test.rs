//! Test final exponentiation in isolation.
//! Take arkworks' Miller loop output, apply OUR final_exp, compare.
use bn254::*;
use ark_bn254::{Bn254, G1Affine, G2Affine, Fq12};
use ark_ec::{pairing::Pairing, AffineRepr};
use ark_ff::{Field, PrimeField, BigInteger};

fn ark_fq_to_limbs(x: &ark_bn254::Fq) -> [u64; 4] {
    let bi = x.into_bigint();
    [bi.0[0], bi.0[1], bi.0[2], bi.0[3]]
}

fn ark_fp12_to_ours(f: &Fq12) -> Fp12 {
    // Both use same tower: Fp12 = Fp6[w]/(w^2-v), Fp6 = Fp2[v]/(v^3-xi)
    // Both use same Montgomery encoding on Fp.
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
    println!("=== Final exp isolation test ===\n");

    let ark_p = G1Affine::generator();
    let ark_q = G2Affine::generator();

    // arkworks Miller loop output (before final exp)
    let ark_ml = Bn254::multi_miller_loop([ark_p], [ark_q]);
    let ark_ml_fp12: Fq12 = ark_ml.0;

    // arkworks full pairing output
    let ark_full = Bn254::pairing(ark_p, ark_q);
    let ark_full_fp12: Fq12 = ark_full.0;

    // Convert arkworks ML output to our Fp12 representation
    let ark_ml_ours = ark_fp12_to_ours(&ark_ml_fp12);

    // Apply OUR final exp to arkworks' ML output
    let mut our_fe_of_ark_ml = Fp12::zero();
    // final_exp_dsd needs Frobenius p^2 constants
    let mut g1p2 = Fp2::zero();
    let mut g2p2 = Fp2::zero();
    let mut wp2  = Fp2::zero();
    bn254::tower::bn254_load_gamma1_p2(&mut g1p2);
    bn254::tower::bn254_load_gamma2_p2(&mut g2p2);
    bn254::tower::bn254_load_w_frob_p2_c1(&mut wp2);
    bn254::tower::bn254_final_exp_dsd(
        &mut our_fe_of_ark_ml,
        &ark_ml_ours,
        &g1p2, &g2p2, &wp2,
    );

    // Compare: our_fe_of_ark_ml should match ark_full if our final exp is correct
    let ark_full_ours = ark_fp12_to_ours(&ark_full_fp12);

    println!("Our final_exp(ark_ml).c0.c0.c0 = {:016x?}", our_fe_of_ark_ml.c0.c0.c0.0);
    println!("Ark final_exp(ark_ml).c0.c0.c0 = {:016x?}", ark_full_ours.c0.c0.c0.0);

    if our_fe_of_ark_ml.c0.c0.c0.0 == ark_full_ours.c0.c0.c0.0 {
        println!("\nMATCH: Our final_exp produces same result as arkworks when");
        println!("       given arkworks' Miller loop output.");
        println!("       => Bug is in our Miller loop, NOT final exp.");
    } else {
        println!("\nDIFFER: Our final_exp produces different result.");
        println!("        => Bug is (also) in our final_exp.");
    }

    // Also: apply arkworks' final_exp to our ML output
    // (we can do this via Bn254::final_exponentiation)
    let p_x = Fp([0xd35d438dc58f0d9d, 0x0a78eb28f5c70b3d, 0x666ea36f7879462c, 0x0e0a77c19a07df2f]);
    let p_y = Fp([0xa6ba871b8b1e1b3a, 0x14f1d651eb8e167b, 0xccdd46def0f28c58, 0x1c14ef83340fbe5e]);
    let q_x = Fp2 {
        c0: Fp([0x8e83b5d102bc2026, 0xdceb1935497b0172, 0xfbb8264797811adf, 0x19573841af96503b]),
        c1: Fp([0xafb4737da84c6140, 0x6043dd5a5802d8c4, 0x09e950fc52a02f86, 0x14fef0833aea7b6b]),
    };
    let q_y = Fp2 {
        c0: Fp([0x619dfa9d886be9f6, 0xfe7fd297f59e9b78, 0xff9e1a62231b7dfe, 0x28fd7eebae9e4206]),
        c1: Fp([0x64095b56c71856ee, 0xdc57f922327d3cbb, 0x55f935be33351076, 0x0da4a0e693fd6482]),
    };

    let mut our_ml = Fp12::zero();
    miller_loop_optimal(&mut our_ml, &p_x, &p_y, &q_x, &q_y);

    // Apply our final_exp to our ML
    let mut our_full = Fp12::zero();
    bn254::tower::bn254_final_exp_dsd(&mut our_full, &our_ml, &g1p2, &g2p2, &wp2);
    println!("\nOur full pairing.c0.c0.c0      = {:016x?}", our_full.c0.c0.c0.0);
    println!("Same as pairing_optimal?        = {}", our_full.c0.c0.c0.0 == [0xc556f62b2a98671d, 0x23a59ac167bcf363, 0x5ef208445f5f6f37, 0x12adf27ccb29382a]);
}
