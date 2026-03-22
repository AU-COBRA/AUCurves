/**
 * Fp and Fp2 base functions for BLS12-381.
 *
 * These implement Fp2 = Fp[u]/(u^2+1) arithmetic by calling the
 * verified Fp base functions (bls12_add, bls12_sub, bls12_mul, etc.)
 * which are included in bls12_pairing_all.c.
 *
 * Each Fp element is 6 x 64-bit words (48 bytes).
 * Each Fp2 element is 2 x Fp = 12 words (96 bytes).
 * Layout: [real_part (6 words), imag_part (6 words)]
 */

#include <string.h>

#define FP_WORDS 6
#define FP_SZ (FP_WORDS * sizeof(br_word_t))

#define FP2_REAL(p) ((br_word_t)(p))
#define FP2_IMAG(p) ((br_word_t)((char*)(p) + FP_SZ))

/* ================================================================
 * BLS12-381 constants
 * ================================================================ */

/* R mod p = Montgomery form of 1 */
static const uint64_t R_MOD_P[6] = {
    0x760900000002fffdULL, 0xebf4000bc40c0002ULL,
    0x5f48985753c758baULL, 0x77ce585370525745ULL,
    0x5c071a97a256ec6dULL, 0x15f65ec3fa80e493ULL
};

/* R^2 mod p = used for Montgomery encoding: to_mont(x) = montmul(x, R^2) */
static const uint64_t R2_MOD_P[6] = {
    0xf4df1f341c341746ULL, 0x0a76e6a609d104f1ULL,
    0x8de5476c4c95b6d5ULL, 0x67eb88a9939d83c0ULL,
    0x9a793e85b519952dULL, 0x11988fe592cae3aaULL
};

/* p - 2 in binary (381 bits, little-endian bit array).
 * Used for Fermat inversion: a^{-1} = a^{p-2} mod p.
 * p = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf
 *       6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
 * p-2 ends in ...aaa9
 */

/* ================================================================
 * bls12_from_word: convert machine integer to Montgomery form
 *
 * from_word(out, w) sets out = w * R mod p.
 * Method: place w in a 6-word array, then montmul by R^2 mod p.
 *   montmul(w, R^2) = w * R^2 * R^{-1} = w * R mod p.
 * ================================================================ */
void bls12_from_word(br_word_t out, br_word_t w) {
    uint64_t tmp[6] = {0};
    tmp[0] = (uint64_t)w;
    bls12_mul(out, (br_word_t)tmp, (br_word_t)R2_MOD_P);
}

/* ================================================================
 * Fp negation: bls12_opp(out, x) = -x mod p = p - x
 * ================================================================ */
static void fp_opp(br_word_t out, br_word_t x) {
    uint64_t zero[6] = {0};
    bls12_sub(out, (br_word_t)zero, x);
}

void bls12_opp(br_word_t out, br_word_t x) {
    fp_opp(out, x);
}

/* ================================================================
 * Fp inversion via Bernstein-Yang constant-time divstep algorithm.
 *
 * Uses fiat-crypto's synthesized divstep (from bls12_by_inv.c).
 * 1101 iterations of cheap divstep operations, much faster than
 * the previous Fermat approach (~380 sq + 190 mul).
 *
 * Reference: Bernstein, Yang. "Fast constant-time gcd computation
 * and modular inversion." 2019.
 * ================================================================ */
static void fp_inv(br_word_t out, br_word_t x) {
    by_fp_inv(out, x);
}

/* ================================================================
 * Fp2 operations
 * ================================================================ */

void bls12_Fp2_felem_copy(br_word_t out, br_word_t x) {
    bls12_felem_copy(FP2_REAL(out), FP2_REAL(x));
    bls12_felem_copy(FP2_IMAG(out), FP2_IMAG(x));
}

void bls12_Fp2_add(br_word_t out, br_word_t x, br_word_t y) {
    bls12_add(FP2_REAL(out), FP2_REAL(x), FP2_REAL(y));
    bls12_add(FP2_IMAG(out), FP2_IMAG(x), FP2_IMAG(y));
}

void bls12_Fp2_sub(br_word_t out, br_word_t x, br_word_t y) {
    bls12_sub(FP2_REAL(out), FP2_REAL(x), FP2_REAL(y));
    bls12_sub(FP2_IMAG(out), FP2_IMAG(x), FP2_IMAG(y));
}

void bls12_Fp2_opp(br_word_t out, br_word_t x) {
    fp_opp(FP2_REAL(out), FP2_REAL(x));
    fp_opp(FP2_IMAG(out), FP2_IMAG(x));
}

/* (a+b*u)(c+d*u) = (ac-bd) + ((a+b)(c+d)-ac-bd)*u
 * Karatsuba trick: 3 Fp muls instead of 4.
 * Matches the verified bedrock2 Fp2_mul in QuadraticFieldExtensions.v:1662. */
void bls12_Fp2_mul(br_word_t out, br_word_t x, br_word_t y) {
    uint64_t v0[6], v1[6], v2[6];
    /* v0 = x.re * y.re */
    bls12_mul((br_word_t)v0, FP2_REAL(x), FP2_REAL(y));
    /* v1 = x.im * y.im */
    bls12_mul((br_word_t)v1, FP2_IMAG(x), FP2_IMAG(y));
    /* v2 = x.re + x.im */
    bls12_add((br_word_t)v2, FP2_REAL(x), FP2_IMAG(x));
    /* out.im = y.re + y.im (temporary) */
    bls12_add(FP2_IMAG(out), FP2_REAL(y), FP2_IMAG(y));
    /* out.im = (y.re+y.im) * (x.re+x.im) = (a+b)(c+d) */
    bls12_mul(FP2_IMAG(out), FP2_IMAG(out), (br_word_t)v2);
    /* out.im -= v0 */
    bls12_sub(FP2_IMAG(out), FP2_IMAG(out), (br_word_t)v0);
    /* out.im -= v1 = (a+b)(c+d) - ac - bd = ad+bc */
    bls12_sub(FP2_IMAG(out), FP2_IMAG(out), (br_word_t)v1);
    /* out.re = v0 - v1 = ac - bd */
    bls12_sub(FP2_REAL(out), (br_word_t)v0, (br_word_t)v1);
}

/* (a0+a1*u)^2 = ((a0+a1)(a0-a1), 2*a0*a1) */
void bls12_Fp2_square(br_word_t out, br_word_t x) {
    uint64_t sum[6], diff[6], prod[6];
    bls12_add((br_word_t)sum, FP2_REAL(x), FP2_IMAG(x));
    bls12_sub((br_word_t)diff, FP2_REAL(x), FP2_IMAG(x));
    bls12_mul(FP2_REAL(out), (br_word_t)sum, (br_word_t)diff);
    bls12_mul((br_word_t)prod, FP2_REAL(x), FP2_IMAG(x));
    bls12_add(FP2_IMAG(out), (br_word_t)prod, (br_word_t)prod);
}

/* (a0+a1*u)^{-1} = (a0, -a1) / (a0^2 + a1^2) */
void bls12_Fp2_inv(br_word_t out, br_word_t x) {
    uint64_t a0_sq[6], a1_sq[6], norm[6], norm_inv[6];
    bls12_square((br_word_t)a0_sq, FP2_REAL(x));
    bls12_square((br_word_t)a1_sq, FP2_IMAG(x));
    bls12_add((br_word_t)norm, (br_word_t)a0_sq, (br_word_t)a1_sq);
    fp_inv((br_word_t)norm_inv, (br_word_t)norm);
    /* out_real = a0 * norm_inv */
    bls12_mul(FP2_REAL(out), FP2_REAL(x), (br_word_t)norm_inv);
    /* out_imag = -a1 * norm_inv */
    uint64_t neg_a1[6];
    fp_opp((br_word_t)neg_a1, FP2_IMAG(x));
    bls12_mul(FP2_IMAG(out), (br_word_t)neg_a1, (br_word_t)norm_inv);
}
