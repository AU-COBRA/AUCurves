//! Single-step Miller loop debug: compute just the FIRST doubling step
//! and compare line function evaluation between our code and arkworks.
//!
//! Strategy: run our miller_loop_optimal with a modified loop that exits
//! after 1 iteration (can't easily do that without source change), so
//! instead: compute just the line function manually and compare with
//! arkworks' first ell coefficient.

use bn254::*;
use ark_bn254::{G2Affine, Fq, Fq2, Fq12};
use ark_ec::AffineRepr;
use ark_ff::{Field, PrimeField, BigInteger};

fn ark_fq_to_limbs(x: &Fq) -> [u64; 4] {
    let bi = x.into_bigint();
    [bi.0[0], bi.0[1], bi.0[2], bi.0[3]]
}

fn main() {
    println!("=== Single-step line function comparison ===\n");

    // G2 generator Q
    let q_x = Fp2 {
        c0: Fp([0x8e83b5d102bc2026, 0xdceb1935497b0172, 0xfbb8264797811adf, 0x19573841af96503b]),
        c1: Fp([0xafb4737da84c6140, 0x6043dd5a5802d8c4, 0x09e950fc52a02f86, 0x14fef0833aea7b6b]),
    };
    let q_y = Fp2 {
        c0: Fp([0x619dfa9d886be9f6, 0xfe7fd297f59e9b78, 0xff9e1a62231b7dfe, 0x28fd7eebae9e4206]),
        c1: Fp([0x64095b56c71856ee, 0xdc57f922327d3cbb, 0x55f935be33351076, 0x0da4a0e693fd6482]),
    };
    // G1 generator P
    let p_x = Fp([0xd35d438dc58f0d9d, 0x0a78eb28f5c70b3d, 0x666ea36f7879462c, 0x0e0a77c19a07df2f]);
    let p_y = Fp([0xa6ba871b8b1e1b3a, 0x14f1d651eb8e167b, 0xccdd46def0f28c58, 0x1c14ef83340fbe5e]);

    // Compute doubling: lambda = 3*qx^2 / (2*qy)
    let mut qx_sq = Fp2::zero();
    fp2_square(&mut qx_sq, &q_x);
    let mut three_qx_sq = Fp2::zero();
    fp2_add(&mut three_qx_sq, &qx_sq, &qx_sq);
    let tmp = three_qx_sq.clone();
    fp2_add(&mut three_qx_sq, &tmp, &qx_sq);

    let mut two_qy = Fp2::zero();
    fp2_add(&mut two_qy, &q_y, &q_y);
    let mut two_qy_inv = Fp2::zero();
    fp2_inv(&mut two_qy_inv, &two_qy);

    let mut lambda = Fp2::zero();
    fp2_mul(&mut lambda, &three_qx_sq, &two_qy_inv);

    // Line evaluation at P: build Fp12
    let mut line = Fp12::zero();
    // make_line_corrected builds: c0.c0.c0 = yP, c1.c0 = -(lam*xP), c1.c1 = lam*xT - yT
    bn254::tower::bn254_make_line_corrected(&mut line, &lambda, &q_x, &q_y, &p_x, &p_y);

    println!("Our line eval (first doubling):");
    println!("  c0.c0.c0 = {:016x?}", line.c0.c0.c0.0);
    println!("  c0.c0.c1 = {:016x?}", line.c0.c0.c1.0);
    println!("  c1.c0.c0 = {:016x?}", line.c1.c0.c0.0);  // position 3
    println!("  c1.c0.c1 = {:016x?}", line.c1.c0.c1.0);
    println!("  c1.c1.c0 = {:016x?}", line.c1.c1.c0.0);  // position 4
    println!("  c1.c1.c1 = {:016x?}", line.c1.c1.c1.0);

    // arkworks: get the first ell coefficient from G2Prepared
    use ark_bn254::g2::G2Prepared;
    let ark_q = G2Affine::generator();
    let prepared: G2Prepared = ark_q.into();

    // First coefficient is from the first doubling
    let (c0, c1, c2) = &prepared.ell_coeffs[0];

    // For D-twist: ell applies c0 *= yP, c1 *= xP, then mul_by_034
    // So the Fp12 element has:
    //   position 0: c0 * yP
    //   position 3: c1 * xP
    //   position 4: c2

    // arkworks G1 generator in affine: x=1, y=2
    // In Montgomery: already in our p_x, p_y limbs

    // c0 * yP (Fp2 * Fp)
    let mut ark_pos0 = *c0;
    let ark_py = ark_bn254::Fq::from(2u64);  // not Montgomery - this is wrong
    // Actually arkworks G1Affine::generator() gives the generator which has
    // affine coords (1, 2), but internally in Montgomery form.
    let ark_g1 = ark_bn254::G1Affine::generator();

    // The ell_coeffs are PRE-COMPUTED. To compare, we need to check the
    // actual ell result, not the raw coefficients.
    //
    // arkworks computes: c0 *= p.y, c1 *= p.x, then applies mul_by_034
    // We can't easily extract the intermediate Fp12 from a single step.
    //
    // Instead, let's compare the RAW coefficients.
    println!("\nArkworks first ell_coeff (raw, before *P scaling):");
    println!("  c0.c0 = {:016x?}", ark_fq_to_limbs(&c0.c0));
    println!("  c0.c1 = {:016x?}", ark_fq_to_limbs(&c0.c1));
    println!("  c1.c0 = {:016x?}", ark_fq_to_limbs(&c1.c0));
    println!("  c1.c1 = {:016x?}", ark_fq_to_limbs(&c1.c1));
    println!("  c2.c0 = {:016x?}", ark_fq_to_limbs(&c2.c0));
    println!("  c2.c1 = {:016x?}", ark_fq_to_limbs(&c2.c1));

    // Compare: our lambda = 3*qx^2/(2*qy) (AFFINE)
    // arkworks c1 = 3*j = 3*x^2 (PROJECTIVE, z=1 initially so same)
    // arkworks c0 = -h = -2*y*z = -2*y (z=1 initially)
    // arkworks c2 = i = e - b = 3*b_twist*z^2 - y^2 (z=1)
    //
    // Our c0.c0 = yP (Fp) → this is the CONSTANT term after scaling
    // Our c1.c0 = -(lambda * xP) (Fp2)
    // Our c1.c1 = lambda * xT - yT (Fp2)
    //
    // arkworks BEFORE scaling:
    // c0 = -2*qy (projective z=1 → same as -2*qy)
    // c1 = 3*qx^2 (same as 3*qx^2)
    // c2 = 3*b_twist - qy^2 where b_twist = b/xi = 3/(9+u) for BN254
    //
    // After scaling: c0 *= yP, c1 *= xP
    // Position 0: (-2*qy) * yP
    // Position 3: (3*qx^2) * xP
    // Position 4: 3*b_twist - qy^2
    //
    // Our formula AFTER building the Fp12:
    // Position 0: yP (just the Fp element, NOT -2*qy*yP)
    // Position 3: -(lambda * xP) = -(3*qx^2/(2*qy)) * xP
    // Position 4: lambda * qx - qy = (3*qx^2/(2*qy))*qx - qy
    //
    // SCALING DIFFERENCE:
    // arkworks position 0: (-2*qy) * yP
    // ours position 0:     yP
    // Factor: -2*qy
    //
    // arkworks position 3: (3*qx^2) * xP
    // ours position 3:     -(3*qx^2/(2*qy)) * xP
    // Factor: -2*qy (same!)
    //
    // arkworks position 4: 3*b' - qy^2
    // ours position 4:     (3*qx^3/(2*qy)) - qy = (3*qx^3 - 2*qy^2)/(2*qy)
    //                     For E': qy^2 = qx^3 + b', so 3*qx^3 - 2*(qx^3+b') = qx^3 - 2*b'
    //                     = (qx^3 - 2*b')/(2*qy)
    //
    // Hmm: arkworks c2 = 3*b' - qy^2 = 3*b' - qx^3 - b' = 2*b' - qx^3
    // ours c4 = (3*qx^3 - 2*qy^2)/(2*qy) = (3*qx^3 - 2*qx^3 - 2*b')/(2*qy) = (qx^3 - 2*b')/(2*qy)
    // Factor: (-1) * (2*qy) ... wait let me recheck.
    //
    // arkworks c2 = i = e - b = 3*COEFF_B*z^2 - y^2 (z=1)
    //             = 3*(b/xi) - qy^2
    // ours c4     = lambda*qx - qy = (3*qx^2/(2*qy))*qx - qy
    //             = (3*qx^3 - 2*qy^2)/(2*qy)
    //             = (3*qx^3 - 2*(qx^3 + b'))/(2*qy)   [using E': qy^2 = qx^3 + b']
    //             = (qx^3 - 2*b')/(2*qy)
    //
    // arkworks c2 = 3*b' - qy^2 = 3*b' - qx^3 - b' = 2*b' - qx^3 = -(qx^3 - 2*b')
    //
    // So: arkworks c2 = -(qx^3 - 2*b')
    //     ours c4     = (qx^3 - 2*b')/(2*qy)
    // Factor: -(2*qy) ... same scaling factor!
    //
    // So ALL THREE positions have the same overall factor: -(2*qy)
    // (or equivalently, our Fp12 line = arkworks Fp12 line * 1/(-(2*qy)))
    //
    // This factor is an element of Fp2*. It accumulates through the
    // Miller loop (one factor per doubling+addition step). After the
    // full loop, the accumulated factor is some power of Fp2*.
    //
    // Final exponentiation maps x -> x^{(p^12-1)/r}. Since Fp2* has
    // order p^2-1, and (p^12-1)/r = (p^2-1) * (p^10+p^8+...+1)/r,
    // elements of Fp2* are raised to a multiple of (p^2-1), giving 1.
    //
    // So the factor SHOULD cancel in final exp.

    println!("\n=== Conclusion ===");
    println!("Line function formulas differ by a factor of -(2*qy) per step.");
    println!("This is an Fp2* element that accumulates through the loop.");
    println!("It SHOULD cancel in final exponentiation since (p^12-1)/r");
    println!("is divisible by (p^2-1). If it doesn't cancel, the bug is");
    println!("in the final exponentiation, not the Miller loop.");
}
