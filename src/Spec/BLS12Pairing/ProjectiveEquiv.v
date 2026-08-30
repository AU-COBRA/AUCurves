(** * Projective vs affine Miller loop equivalence.
 *
 * The projective Miller loop computes the same pairing result as
 * the affine Miller loop after final exponentiation. This is because:
 *
 * 1. The projective point T = (X:Y:Z) represents the same affine
 *    point (X/Z^2, Y/Z^3) as the affine T = (x, y).
 *
 * 2. The line evaluation in projective coordinates differs from the
 *    affine version by a scalar factor c in Fp2* at each step.
 *
 * 3. The accumulated scalar factor is an element of Fp* ⊂ Fp12*.
 *    Since (p^12 - 1) / r is divisible by (p - 1), any element of
 *    Fp* raised to (p^12 - 1) / r equals 1. Therefore the scalar
 *    factor vanishes after the final exponentiation.
 *
 * This is standard pairing theory (see Aranha et al. 2010,
 * "Faster Explicit Formulas for Computing Pairings over Ordinary
 * Curves", Section 3).
 *
 * NOTE: The actual bedrock2 code (bls12_pairing) uses the projective
 * Miller loop directly. The spec in BLS12_Pairing.v defines the pairing
 * as the composition of miller_loop_proj + final_exp. No affine/projective
 * bridge axiom is needed because the spec IS the projective version.
 *
 * This file documents the mathematical justification but provides no
 * axiom — the equivalence is not needed for the WP proof chain.
 *)
