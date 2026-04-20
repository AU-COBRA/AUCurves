//! Narrow the pairing divergence: compare Miller loop output (before
//! final exp) between our extraction and arkworks.

use bn254::*;
use ark_bn254::{Bn254, G1Affine, G2Affine, Fq12};
use ark_ec::{pairing::Pairing, AffineRepr};
use ark_ff::{Field, PrimeField, BigInteger};

fn ark_fq_to_limbs(x: &ark_bn254::Fq) -> [u64; 4] {
    let bi = x.into_bigint();
    [bi.0[0], bi.0[1], bi.0[2], bi.0[3]]
}

fn main() {
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

    // 1. Our miller loop ONLY (no final exp)
    let mut ml_ours = Fp12::zero();
    miller_loop_optimal(&mut ml_ours, &p_x, &p_y, &q_x, &q_y);

    // 2. arkworks miller loop ONLY
    let ark_p = G1Affine::generator();
    let ark_q = G2Affine::generator();
    let ark_ml = Bn254::multi_miller_loop([ark_p], [ark_q]);

    println!("=== Miller loop output (before final exp) ===\n");
    println!("Ours c0.c0.c0: {:016x?}", ml_ours.c0.c0.c0.0);
    println!("Ark  c0.c0.c0: {:016x?}", ark_fq_to_limbs(&ark_ml.0.c0.c0.c0));

    let our_limbs = ml_ours.c0.c0.c0.0;
    let ark_limbs = ark_fq_to_limbs(&ark_ml.0.c0.c0.c0);
    if our_limbs == ark_limbs {
        println!("\nMiller loop c0.c0.c0 MATCH — divergence is in final exp.\n");
    } else {
        println!("\nMiller loop c0.c0.c0 DIFFER — divergence is in miller loop.\n");
    }

    // Also compare a few more Fp components
    let cmp = |ours: &[u64; 4], ark: &[u64; 4], label: &str| {
        if ours == ark { println!("{}: MATCH", label); }
        else { println!("{}: DIFFER", label); }
    };
    cmp(&ml_ours.c0.c0.c0.0, &ark_fq_to_limbs(&ark_ml.0.c0.c0.c0), "c0.c0.c0");
    cmp(&ml_ours.c0.c0.c1.0, &ark_fq_to_limbs(&ark_ml.0.c0.c0.c1), "c0.c0.c1");
    cmp(&ml_ours.c1.c0.c0.0, &ark_fq_to_limbs(&ark_ml.0.c1.c0.c0), "c1.c0.c0");
    cmp(&ml_ours.c1.c2.c1.0, &ark_fq_to_limbs(&ark_ml.0.c1.c2.c1), "c1.c2.c1");
}
