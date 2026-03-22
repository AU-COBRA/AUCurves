/**
 * Bernstein-Yang modular inversion for BLS12-381 Fp.
 *
 * Uses the divstep algorithm from fiat-crypto's pre-generated bls12_64.c.
 * Replaces the Fermat inversion (~380 sq + 190 mul) with ~1101 divstep
 * iterations, each much cheaper than a field multiplication.
 *
 * Reference: Bernstein, Yang. "Fast constant-time gcd computation and
 * modular inversion." 2019.
 */

#include <stdint.h>
#include <string.h>

/* Typedefs needed by fiat-crypto wrapper functions in bls12_64.c */
typedef uint64_t fiat_bls12_montgomery_domain_field_element[6];
typedef uint64_t fiat_bls12_non_montgomery_domain_field_element[6];

/* Include the fiat-crypto generated divstep functions.
 * Uses fiat_bls12_* prefix — no conflict with bedrock2 bls12_* functions.
 * All internal functions are static, only wrappers are extern. */
#include "../../../fiat-crypto/src/ExtractionOCaml/bls12_64.c"

/* BLS12-381 prime is 381 bits, 6 limbs of 64 bits */
#define BY_LIMBS 6
#define BY_SAT_LIMBS 7
#define BY_LEN_PRIME 381
#define BY_WORDSIZE 64

/* Number of divstep iterations needed for inversion.
 * Formula from Bernstein-Yang: ceil((49*n + 57) / 17) for n >= 46 */
#define BY_ITERATIONS (((49 * BY_LEN_PRIME) + 57) / 17)

/**
 * by_fp_inv: Compute modular inverse using Bernstein-Yang divstep.
 *
 * Input:  x in Montgomery form (6 x uint64_t at pointer x)
 * Output: x^{-1} in Montgomery form (6 x uint64_t at pointer out)
 *
 * Uses the inversion template pattern from fiat-crypto/inversion/c/.
 */
void by_fp_inv(uintptr_t out, uintptr_t x) {
    uint64_t precomp[BY_LIMBS];
    fiat_bls12_divstep_precomp(precomp);

    uint64_t d = 1;
    uint64_t f[BY_SAT_LIMBS];
    uint64_t g[BY_SAT_LIMBS];
    uint64_t v[BY_LIMBS];
    uint64_t r[BY_LIMBS];

    /* Initialize: f = msat(p), g = from_montgomery(input), v = 0, r = 1.
     * The BY algorithm requires g in standard (non-Montgomery) form.
     * See fiat-crypto/inversion/c/inversion_test_template.c:30-33. */
    fiat_bls12_msat(f);

    /* g = from_montgomery(x) in saturated form (7 words, top word 0) */
    uint64_t g_std[BY_LIMBS];
    fiat_bls12_from_montgomery(g_std, (const uint64_t*)(uintptr_t)x);
    memcpy(g, g_std, BY_LIMBS * sizeof(uint64_t));
    g[BY_LIMBS] = 0;

    fiat_bls12_set_one(r);
    memset(v, 0, sizeof(v));

    /* Ping-pong divstep iterations */
    uint64_t out1;
    uint64_t out2[BY_SAT_LIMBS], out3[BY_SAT_LIMBS];
    uint64_t out4[BY_LIMBS], out5[BY_LIMBS];

    for (int i = 0; i < BY_ITERATIONS - (BY_ITERATIONS % 2); i += 2) {
        fiat_bls12_divstep(&out1, out2, out3, out4, out5, d, f, g, v, r);
        fiat_bls12_divstep(&d, f, g, v, r, out1, out2, out3, out4, out5);
    }
    if (BY_ITERATIONS % 2) {
        fiat_bls12_divstep(&out1, out2, out3, out4, out5, d, f, g, v, r);
        memcpy(v, out4, sizeof(v));
        memcpy(f, out2, sizeof(f));
    }

    /* Conditionally negate v based on sign of f, then multiply by precomp.
     * The result of v*precomp (Montgomery mul) gives the Montgomery-form inverse. */
    uint64_t h[BY_LIMBS];
    fiat_bls12_opp(h, v);
    fiat_bls12_selectznz(v, (uint8_t)(f[BY_SAT_LIMBS - 1] >> (BY_WORDSIZE - 1)), v, h);
    internal_fiat_bls12_mul(out, (uintptr_t)v, (uintptr_t)precomp);
}
