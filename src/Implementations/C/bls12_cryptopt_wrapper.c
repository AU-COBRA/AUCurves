/**
 * Wrapper to use CryptOpt-generated assembly for Fp mul/square
 * in the BLS12-381 pairing pipeline.
 *
 * The bedrock2-extracted code calls bls12_mul(out, a, b) with
 * br_word_t (= uintptr_t) arguments. CryptOpt exports functions
 * with standard C array signatures. This wrapper bridges the two.
 *
 * Usage: compile with -DUSE_CRYPTOPT_MUL and/or -DUSE_CRYPTOPT_SQUARE,
 * link with the assembled CryptOpt .o files.
 */

#include <stdint.h>

/* CryptOpt-generated functions (from .asm files) */
extern void fiat_bls12_381_p_mul(uint64_t out[6], const uint64_t a[6], const uint64_t b[6]);
extern void fiat_bls12_381_p_square(uint64_t out[6], const uint64_t a[6]);

#ifdef USE_CRYPTOPT_MUL
/* Override bls12_mul with CryptOpt version */
void bls12_mul(uintptr_t out, uintptr_t a, uintptr_t b) {
    fiat_bls12_381_p_mul((uint64_t*)out, (const uint64_t*)a, (const uint64_t*)b);
}
#endif

#ifdef USE_CRYPTOPT_SQUARE
/* Override bls12_square with CryptOpt version */
void bls12_square(uintptr_t out, uintptr_t a) {
    fiat_bls12_381_p_square((uint64_t*)out, (const uint64_t*)a);
}
#endif
