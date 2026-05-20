/* X25519 scalar multiplication using fiat-crypto verified field arithmetic.
 *
 * This implements the same Montgomery ladder algorithm as bedrock2's
 * MontgomeryLadder.v, using the fiat-crypto 5-limb unsaturated Solinas
 * field ops from curve25519_64.c.
 *
 * This represents the performance of the bedrock2 -> ToJasmin -> jasminc
 * verification path, but compiled via clang/gcc instead of jasminc.
 */

#include <stdint.h>
#include <string.h>

/* Include fiat-crypto field ops (all static inline) */
#include "fiat_curve25519_64.c"

typedef fiat_25519_tight_field_element fe;
typedef fiat_25519_loose_field_element fe_loose;

/* fe_mul: tight * tight -> tight (auto-relax inputs) */
static void fe_mul(fe out, const fe a, const fe b) {
    fe_loose a_loose, b_loose;
    fiat_25519_relax(a_loose, a);
    fiat_25519_relax(b_loose, b);
    fiat_25519_carry_mul(out, a_loose, b_loose);
}

/* fe_sqr: tight -> tight */
static void fe_sqr(fe out, const fe a) {
    fe_loose a_loose;
    fiat_25519_relax(a_loose, a);
    fiat_25519_carry_square(out, a_loose);
}

/* fe_add: tight + tight -> tight */
static void fe_add(fe out, const fe a, const fe b) {
    fe_loose sum;
    fiat_25519_add(sum, a, b);
    fiat_25519_carry(out, sum);
}

/* fe_sub: tight - tight -> tight */
static void fe_sub(fe out, const fe a, const fe b) {
    fe_loose diff;
    fiat_25519_sub(diff, a, b);
    fiat_25519_carry(out, diff);
}

/* fe_scmul_a24: multiply by a24 = (A-2)/4 = 121665.
 *
 * Note: fiat-crypto's Curve25519 spec defines a24 = (A-2)/4 = 121665
 * (see Spec/Curve25519.v), NOT (A+2)/4 = 121666.  The fiat-c extraction
 * provides carry_scmul_121666, which is the WRONG constant.
 * We compute 121665*x = 121666*x - x instead. */
static void fe_scmul_a24(fe out, const fe a) {
    fe tmp;
    fe_loose a_loose;
    fiat_25519_relax(a_loose, a);
    fiat_25519_carry_scmul_121666(tmp, a_loose);  /* tmp = 121666 * a */
    fe_sub(out, tmp, a);                           /* out = 121665 * a */
}

/* fe_cswap: constant-time conditional swap */
static void fe_cswap(fe a, fe b, uint8_t swap) {
    fiat_25519_selectznz(a, swap, a, b);
    /* Need a temp since selectznz reads before writing */
    /* Actually we need both directions */
}

/* Proper cswap using selectznz */
static void fe_cswap2(fe a, fe b, fiat_25519_uint1 swap) {
    fe ta, tb;
    fiat_25519_selectznz(ta, swap, a, b);
    fiat_25519_selectznz(tb, swap, b, a);
    memcpy(a, ta, sizeof(fe));
    memcpy(b, tb, sizeof(fe));
}

/* Montgomery ladder step.
 * Inputs: X2, Z2, X3, Z3, X1 (affine x-coordinate of base point)
 * Outputs: updated X2, Z2, X3, Z3
 */
static void ladderstep(fe X2, fe Z2, fe X3, fe Z3, const fe X1) {
    fe A, AA, B, BB, E, C, D, DA, CB;

    fe_add(A, X2, Z2);       /* A = X2 + Z2 */
    fe_sqr(AA, A);            /* AA = A^2 */
    fe_sub(B, X2, Z2);        /* B = X2 - Z2 */
    fe_sqr(BB, B);            /* BB = B^2 */
    fe_sub(E, AA, BB);        /* E = AA - BB */
    fe_add(C, X3, Z3);        /* C = X3 + Z3 */
    fe_sub(D, X3, Z3);        /* D = X3 - Z3 */
    fe_mul(DA, D, A);         /* DA = D * A */
    fe_mul(CB, C, B);         /* CB = C * B */

    fe_add(X3, DA, CB);       /* X3 = DA + CB */
    fe_sqr(X3, X3);           /* X3 = (DA + CB)^2 */

    fe_sub(Z3, DA, CB);       /* Z3 = DA - CB */
    fe_sqr(Z3, Z3);           /* Z3 = (DA - CB)^2 */
    fe_mul(Z3, X1, Z3);       /* Z3 = X1 * (DA - CB)^2 */

    fe_mul(X2, AA, BB);       /* X2 = AA * BB */

    fe_scmul_a24(Z2, E);      /* Z2 = a24 * E */
    fe_add(Z2, AA, Z2);       /* Z2 = AA + a24 * E */
    fe_mul(Z2, E, Z2);        /* Z2 = E * (AA + a24 * E) */
}

/* Modular inversion via Bernstein's addition chain for p-2 = 2^255-21.
 * Same chain as Field25519.v / libjade.
 *
 * 2^255-21 = (2^5)(2^250-1) + 11
 *          = (2^5)(2^250-1) + 8 + 2 + 1
 *
 * Standard Bernstein chain:
 *   z^(2^250-1) via repeated square-and-multiply
 *   then 5 squarings, then multiply by z^11
 */
static void fe_inv(fe out, const fe z) {
    fe z2, z9, z11, z_5_0, z_10_0, z_20_0, z_40_0, z_50_0;
    fe z_100_0, z_200_0, z_250_0, t;
    int i;

    fe_sqr(z2, z);                    /* z^2 */
    fe_sqr(t, z2);                    /* z^4 */
    fe_sqr(t, t);                     /* z^8 */
    fe_mul(z9, z, t);                 /* z^9 */
    fe_mul(z11, z2, z9);             /* z^11 */
    fe_sqr(t, z11);                   /* z^22 */
    fe_mul(z_5_0, z9, t);            /* z^(2^5-1) = z^31 */

    fe_sqr(t, z_5_0);
    for (i = 1; i < 5; i++) fe_sqr(t, t);
    fe_mul(z_10_0, t, z_5_0);        /* z^(2^10-1) */

    fe_sqr(t, z_10_0);
    for (i = 1; i < 10; i++) fe_sqr(t, t);
    fe_mul(z_20_0, t, z_10_0);       /* z^(2^20-1) */

    fe_sqr(t, z_20_0);
    for (i = 1; i < 20; i++) fe_sqr(t, t);
    fe_mul(z_40_0, t, z_20_0);       /* z^(2^40-1) */

    fe_sqr(t, z_40_0);
    for (i = 1; i < 10; i++) fe_sqr(t, t);
    fe_mul(z_50_0, t, z_10_0);       /* z^(2^50-1) */

    fe_sqr(t, z_50_0);
    for (i = 1; i < 50; i++) fe_sqr(t, t);
    fe_mul(z_100_0, t, z_50_0);      /* z^(2^100-1) */

    fe_sqr(t, z_100_0);
    for (i = 1; i < 100; i++) fe_sqr(t, t);
    fe_mul(z_200_0, t, z_100_0);     /* z^(2^200-1) */

    fe_sqr(t, z_200_0);
    for (i = 1; i < 50; i++) fe_sqr(t, t);
    fe_mul(z_250_0, t, z_50_0);      /* z^(2^250-1) */

    fe_sqr(t, z_250_0);              /* z^(2^251-2) */
    fe_sqr(t, t);                     /* z^(2^252-4) */
    fe_sqr(t, t);                     /* z^(2^253-8) */
    fe_sqr(t, t);                     /* z^(2^254-16) */
    fe_sqr(t, t);                     /* z^(2^255-32) */
    fe_mul(out, t, z11);              /* z^(2^255-32+11) = z^(2^255-21) */
}

/* Clamp a 32-byte scalar per RFC 7748 */
static void clamp(uint8_t k[32]) {
    k[0] &= 248;
    k[31] &= 127;
    k[31] |= 64;
}

/* X25519 scalar multiplication.
 * scalar: 32 bytes (clamped internally)
 * point:  32 bytes (u-coordinate, little-endian)
 * out:    32 bytes result
 */
void fiat_x25519(uint8_t out[32], const uint8_t scalar[32], const uint8_t point[32]) {
    uint8_t e[32];
    fe X1, X2, Z2, X3, Z3;
    fiat_25519_uint1 swap = 0;
    int pos;

    memcpy(e, scalar, 32);
    clamp(e);

    /* Decode u-coordinate with high bit cleared per RFC 7748 */
    {
        uint8_t u[32];
        memcpy(u, point, 32);
        u[31] &= 0x7f;
        fiat_25519_from_bytes(X1, u);
    }

    /* X2 = 1, Z2 = 0 */
    memset(X2, 0, sizeof(fe));
    X2[0] = 1;
    memset(Z2, 0, sizeof(fe));

    /* X3 = X1, Z3 = 1 */
    memcpy(X3, X1, sizeof(fe));
    memset(Z3, 0, sizeof(fe));
    Z3[0] = 1;

    for (pos = 254; pos >= 0; --pos) {
        fiat_25519_uint1 bit = (e[pos >> 3] >> (pos & 7)) & 1;
        fiat_25519_uint1 sw = swap ^ bit;
        swap = bit;

        fe_cswap2(X2, X3, sw);
        fe_cswap2(Z2, Z3, sw);
        ladderstep(X2, Z2, X3, Z3, X1);
    }
    fe_cswap2(X2, X3, swap);
    fe_cswap2(Z2, Z3, swap);

    fe_inv(Z2, Z2);
    fe_mul(X2, X2, Z2);
    fiat_25519_to_bytes(out, X2);
}
