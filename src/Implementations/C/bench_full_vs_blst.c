/**
 * Comprehensive benchmark: fiat-crypto BLS12-381 (all optimizations) vs blst
 *
 * fiat-crypto stack:
 *   - Fp mul/square: CryptOpt-generated x86-64 assembly (verified by equivalence checker)
 *   - Fp add/sub: bedrock2-extracted C
 *   - Fp2_mul: Karatsuba (3 Fp muls, verified in QuadraticFieldExtensions.v)
 *   - Fp2_square: complex squaring (2 Fp muls)
 *   - Fp6/Fp12: bedrock2-extracted tower (Karatsuba + Chung-Hasan)
 *   - Fp inversion: Bernstein-Yang divstep (verified bridge + certificate)
 *   - Miller loop + final exp: bedrock2-extracted
 *
 * blst:
 *   - Hand-tuned x86-64 assembly throughout
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>
#include <string.h>

/* Include the CryptOpt-patched pairing pipeline.
 * This defines bls12_mul/square as wrappers around CryptOpt asm,
 * and all Fp6/Fp12/pairing from bedrock2 extraction. */
#include "bls12_pairing_all_cryptopt.c"

/* BY divstep inversion */
#include "bls12_by_inv.c"

/* Fp2 stubs: Karatsuba mul, complex square, BY inv */
#include "bls12_fp2_stubs.c"

/* Optimized pairing functions (DSD final exp, projective Miller) */
#include "bls12_optimized.c"

/* blst */
#include "blst.h"

/* ================================================================ */

static double get_time_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1e9 + ts.tv_nsec;
}

#define FP_BYTES 48
#define FP2_BYTES (2*FP_BYTES)
#define FP6_BYTES (3*FP2_BYTES)
#define FP12_BYTES (2*FP6_BYTES)

static void *ae(size_t n) {
    void *p = aligned_alloc(64, ((n + 63) / 64) * 64);
    memset(p, 0, n);
    return p;
}

#define BENCH(name, call, iters) do { \
    for (int _w = 0; _w < 200; _w++) { call; } \
    double _s = get_time_ns(); \
    for (int _i = 0; _i < (iters); _i++) { call; } \
    double _e = get_time_ns(); \
    printf("%-45s %8.1f ns/op\n", name, (_e - _s) / (iters)); \
} while(0)

/* BLS12-381 G1 generator (Montgomery form) */
static const uint64_t G1_x[6] = {
    0x5cb38790fd530c16ULL, 0x7817fc679976fff5ULL,
    0x154f95c7143ba1c1ULL, 0xf0ae6acdf3d0e747ULL,
    0xedce6ecc21dbf440ULL, 0x120177419e0bfb75ULL
};
static const uint64_t G1_y[6] = {
    0xbaac93d50ce72271ULL, 0x8c22631a7918fd8eULL,
    0xdd595f13570725ceULL, 0x51ac582950405194ULL,
    0x0e1c8c3fad0059c0ULL, 0x0bbc3efc5008a26aULL
};
static const uint64_t G2_x[12] = {
    0xf5f28fa202940a10ULL, 0xb3f5fb2687b4961aULL,
    0xa1a893b53e2ae580ULL, 0x9894999d1a3caee9ULL,
    0x6f67b7631863366bULL, 0x058191924350bcd7ULL,
    0xa5a9c0759e23f606ULL, 0xaaa0c59dbccd60c3ULL,
    0x3bb17e18e2867806ULL, 0x1b1ab6cc8541b367ULL,
    0xc2b6ed0ef2158547ULL, 0x11922a097360edf3ULL
};
static const uint64_t G2_y[12] = {
    0x4c730af860494c4aULL, 0x597cfa1f5e369c5aULL,
    0xe7e6856caa0a635aULL, 0xbbefb5e96e0d495fULL,
    0x07d3a975f0ef25a2ULL, 0x0083fd8e7e80dae5ULL,
    0xadc0fc92df64b05dULL, 0x18aa270a2b1461dcULL,
    0x86adac6a3be4eba0ULL, 0x79495c4ec93da33aULL,
    0xe7175850a43ccaedULL, 0x00b2bc2a163de1bfULL
};

int main(void) {
    printf("======================================================================\n");
    printf("  fiat-crypto BLS12-381 (all optimizations) vs blst (x86-64 asm)\n");
    printf("======================================================================\n");
    printf("  fiat: CryptOpt Fp asm + Karatsuba Fp2 + complex Fp2_sqr + BY inv\n");
    printf("  blst: hand-tuned x86-64 assembly throughout\n\n");

    /* ---- Fp ---- */
    uintptr_t a = (uintptr_t)ae(FP_BYTES);
    uintptr_t b = (uintptr_t)ae(FP_BYTES);
    uintptr_t c = (uintptr_t)ae(FP_BYTES);
    memcpy((void*)a, G1_x, FP_BYTES);
    memcpy((void*)b, G1_y, FP_BYTES);

    blst_fp ba, bb, bc;
    memcpy(&ba, G1_x, sizeof(ba));
    memcpy(&bb, G1_y, sizeof(bb));

    printf("--- Fp (384-bit Montgomery) ---\n");
    BENCH("fiat   Fp mul  (CryptOpt asm)", bls12_mul(c, a, b),        1000000);
    BENCH("blst   Fp mul",                 blst_fp_mul(&bc, &ba, &bb), 1000000);
    BENCH("fiat   Fp sqr  (CryptOpt asm)", bls12_square(c, a),        1000000);
    BENCH("blst   Fp sqr",                 blst_fp_sqr(&bc, &ba),     1000000);
    BENCH("fiat   Fp add  (bedrock2 C)",   bls12_add(c, a, b),        1000000);
    BENCH("blst   Fp add",                 blst_fp_add(&bc, &ba, &bb), 1000000);
    BENCH("fiat   Fp sub  (bedrock2 C)",   bls12_sub(c, a, b),        1000000);
    BENCH("blst   Fp sub",                 blst_fp_sub(&bc, &ba, &bb), 1000000);

    /* ---- Fp2 ---- */
    printf("\n--- Fp2 (Karatsuba mul, complex sqr) ---\n");
    uintptr_t a2 = (uintptr_t)ae(FP2_BYTES);
    uintptr_t b2 = (uintptr_t)ae(FP2_BYTES);
    uintptr_t c2 = (uintptr_t)ae(FP2_BYTES);
    memcpy((void*)a2, G2_x, FP2_BYTES);
    memcpy((void*)b2, G2_y, FP2_BYTES);

    blst_fp2 ba2, bb2, bc2;
    memcpy(&ba2, G2_x, sizeof(ba2));
    memcpy(&bb2, G2_y, sizeof(bb2));

    BENCH("fiat   Fp2 mul  (Karatsuba)",   bls12_Fp2_mul(c2, a2, b2),  500000);
    BENCH("blst   Fp2 mul",               blst_fp2_mul(&bc2, &ba2, &bb2), 500000);
    BENCH("fiat   Fp2 sqr  (complex)",     bls12_Fp2_square(c2, a2),   500000);
    BENCH("blst   Fp2 sqr",               blst_fp2_sqr(&bc2, &ba2),   500000);
    BENCH("fiat   Fp2 add",               bls12_Fp2_add(c2, a2, b2),  1000000);
    BENCH("blst   Fp2 add",               blst_fp2_add(&bc2, &ba2, &bb2), 1000000);
    BENCH("fiat   Fp2 sub",               bls12_Fp2_sub(c2, a2, b2),  1000000);
    BENCH("blst   Fp2 sub",               blst_fp2_sub(&bc2, &ba2, &bb2), 1000000);

    /* ---- Fp2 inv (BY divstep) ---- */
    printf("\n--- Fp2 inversion (Bernstein-Yang divstep) ---\n");
    BENCH("fiat   Fp2 inv (BY divstep)",   bls12_Fp2_inv(c2, a2),     10000);

    /* ---- Fp6 ---- */
    printf("\n--- Fp6 ---\n");
    uintptr_t a6 = (uintptr_t)ae(FP6_BYTES);
    uintptr_t b6 = (uintptr_t)ae(FP6_BYTES);
    uintptr_t c6 = (uintptr_t)ae(FP6_BYTES);
    memcpy((void*)a6, G2_x, FP2_BYTES);  /* partial init is fine for timing */
    ((uint64_t*)a6)[12] = 1;
    memcpy((void*)b6, G2_y, FP2_BYTES);
    ((uint64_t*)b6)[12] = 2;

    BENCH("fiat   Fp6 mul",               bls12_Fp6_mul(c6, a6, b6),  100000);
    BENCH("fiat   Fp6 sqr",               bls12_Fp6_square(c6, a6),   100000);

    /* ---- Fp12 ---- */
    printf("\n--- Fp12 ---\n");
    uintptr_t f1 = (uintptr_t)ae(FP12_BYTES);
    uintptr_t f2 = (uintptr_t)ae(FP12_BYTES);
    uintptr_t f3 = (uintptr_t)ae(FP12_BYTES);
    memcpy((void*)f1, G2_x, FP2_BYTES);
    ((uint64_t*)f1)[0] = 1;
    memcpy((void*)f2, G2_y, FP2_BYTES);
    ((uint64_t*)f2)[0] = 2;

    blst_fp12 bf1, bf2, bf3;
    memset(&bf1, 0, sizeof(bf1)); memset(&bf2, 0, sizeof(bf2));
    bf1.fp6[0].fp2[0].fp[0].l[0] = 1;
    bf2.fp6[0].fp2[0].fp[0].l[0] = 2;

    BENCH("fiat   Fp12 mul",              bls12_Fp12_mul(f3, f1, f2),     100000);
    BENCH("blst   Fp12 mul",              blst_fp12_mul(&bf3, &bf1, &bf2), 100000);
    BENCH("fiat   Fp12 sqr",              bls12_Fp12_square(f3, f1),      100000);
    BENCH("blst   Fp12 sqr",              blst_fp12_sqr(&bf3, &bf1),      100000);
    BENCH("fiat   Fp12 inv",              bls12_Fp12_inv(f3, f1),          10000);
    BENCH("blst   Fp12 inv",              blst_fp12_inverse(&bf3, &bf1),   10000);

    /* ---- Miller Loop ---- */
    printf("\n--- Miller Loop ---\n");
    uintptr_t mout = (uintptr_t)ae(FP12_BYTES);
    uintptr_t px = (uintptr_t)ae(FP_BYTES);
    uintptr_t py = (uintptr_t)ae(FP_BYTES);
    uintptr_t qx = (uintptr_t)ae(FP2_BYTES);
    uintptr_t qy = (uintptr_t)ae(FP2_BYTES);
    memcpy((void*)px, G1_x, FP_BYTES);
    memcpy((void*)py, G1_y, FP_BYTES);
    memcpy((void*)qx, G2_x, FP2_BYTES);
    memcpy((void*)qy, G2_y, FP2_BYTES);

    BENCH("fiat   miller_loop",  bls12_miller_loop(mout, px, py, qx, qy), 1000);

    blst_fp12 bout;
    blst_p1_affine bp1; blst_p2_affine bp2;
    memcpy(&bp1.x, G1_x, sizeof(bp1.x));
    memcpy(&bp1.y, G1_y, sizeof(bp1.y));
    memcpy(&bp2.x.fp[0], G2_x, FP_BYTES);
    memcpy(&bp2.x.fp[1], G2_x + 6, FP_BYTES);
    memcpy(&bp2.y.fp[0], G2_y, FP_BYTES);
    memcpy(&bp2.y.fp[1], G2_y + 6, FP_BYTES);

    BENCH("blst   miller_loop",  blst_miller_loop(&bout, &bp2, &bp1), 1000);

    /* ---- Final Exponentiation ---- */
    printf("\n--- Final Exponentiation ---\n");
    bls12_miller_loop(mout, px, py, qx, qy);
    uintptr_t g1p2 = (uintptr_t)ae(FP6_BYTES);
    uintptr_t g2p2 = (uintptr_t)ae(FP6_BYTES);
    uintptr_t wfc1 = (uintptr_t)ae(FP2_BYTES);
    /* Load Frobenius constants */
    bls12_load_gamma1_p2(g1p2);
    bls12_load_gamma2_p2(g2p2);
    bls12_load_w_frob_p2_c1(wfc1);

    BENCH("fiat   final_exp",    bls12_final_exp(mout, mout, g1p2, g2p2, wfc1), 100);

    blst_miller_loop(&bout, &bp2, &bp1);
    BENCH("blst   final_exp",    blst_final_exp(&bout, &bout), 100);

    /* ---- Optimized Final Exp ---- */
    printf("\n--- Optimized Final Exponentiation (DSD) ---\n");
    bls12_miller_loop(mout, px, py, qx, qy);
    BENCH("fiat   final_exp (DSD)", opt_final_exp(mout, mout), 100);

    /* ---- Optimized Miller Loop ---- */
    printf("\n--- Optimized Miller Loop (projective) ---\n");
    BENCH("fiat   miller_loop (proj)", opt_miller_loop(mout, px, py, qx, qy), 100);

    /* ---- Full Pairing ---- */
    printf("\n--- Full Pairing ---\n");
    uintptr_t pout = (uintptr_t)ae(FP12_BYTES);
    BENCH("fiat   pairing (baseline)", bls12_pairing(pout, px, py, qx, qy), 100);
    BENCH("fiat   pairing (optimized)", opt_pairing(pout, px, py, qx, qy), 100);

    /* blst doesn't have a single pairing call in its public API,
     * so we combine miller_loop + final_exp */
    blst_fp12 blst_pair_out;
    #define BLST_PAIRING() do { \
        blst_miller_loop(&blst_pair_out, &bp2, &bp1); \
        blst_final_exp(&blst_pair_out, &blst_pair_out); \
    } while(0)
    BENCH("blst   pairing (ml+fe)", BLST_PAIRING(), 100);

    /* ---- Summary ---- */
    printf("\n--- Summary (ratios) ---\n");
    int N;
    double s, e, fiat_ns, blst_ns;

    N = 1000000;
    s = get_time_ns(); for (int i=0;i<N;i++) bls12_mul(c,a,b); e = get_time_ns();
    fiat_ns = (e-s)/N;
    s = get_time_ns(); for (int i=0;i<N;i++) blst_fp_mul(&bc,&ba,&bb); e = get_time_ns();
    blst_ns = (e-s)/N;
    printf("Fp mul:      fiat=%5.1f ns  blst=%5.1f ns  ratio=%.2fx\n", fiat_ns, blst_ns, fiat_ns/blst_ns);

    N = 500000;
    s = get_time_ns(); for (int i=0;i<N;i++) bls12_Fp2_mul(c2,a2,b2); e = get_time_ns();
    fiat_ns = (e-s)/N;
    s = get_time_ns(); for (int i=0;i<N;i++) blst_fp2_mul(&bc2,&ba2,&bb2); e = get_time_ns();
    blst_ns = (e-s)/N;
    printf("Fp2 mul:     fiat=%5.1f ns  blst=%5.1f ns  ratio=%.2fx\n", fiat_ns, blst_ns, fiat_ns/blst_ns);

    N = 100000;
    s = get_time_ns(); for (int i=0;i<N;i++) bls12_Fp12_mul(f3,f1,f2); e = get_time_ns();
    fiat_ns = (e-s)/N;
    s = get_time_ns(); for (int i=0;i<N;i++) blst_fp12_mul(&bf3,&bf1,&bf2); e = get_time_ns();
    blst_ns = (e-s)/N;
    printf("Fp12 mul:    fiat=%5.1f ns  blst=%5.1f ns  ratio=%.2fx\n", fiat_ns, blst_ns, fiat_ns/blst_ns);

    N = 1000;
    s = get_time_ns(); for (int i=0;i<N;i++) bls12_miller_loop(mout,px,py,qx,qy); e = get_time_ns();
    fiat_ns = (e-s)/N;
    s = get_time_ns(); for (int i=0;i<N;i++) blst_miller_loop(&bout,&bp2,&bp1); e = get_time_ns();
    blst_ns = (e-s)/N;
    printf("Miller loop: fiat=%5.0f ns  blst=%5.0f ns  ratio=%.2fx\n", fiat_ns, blst_ns, fiat_ns/blst_ns);

    free((void*)a); free((void*)b); free((void*)c);
    free((void*)a2); free((void*)b2); free((void*)c2);
    free((void*)a6); free((void*)b6); free((void*)c6);
    free((void*)f1); free((void*)f2); free((void*)f3);
    free((void*)mout); free((void*)px); free((void*)py);
    free((void*)qx); free((void*)qy); free((void*)pout);
    free((void*)g1p2); free((void*)g2p2); free((void*)wfc1);
    return 0;
}
