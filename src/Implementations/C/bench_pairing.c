/**
 * Benchmarks for the BLS12-381 formally verified pairing implementation.
 *
 * Measures cycle counts for:
 *   - Fp multiplication
 *   - Fp2 multiplication
 *   - Fp6 multiplication
 *   - Fp12 multiplication
 *   - Fp12 squaring
 *   - Miller loop
 *   - Final exponentiation
 *   - Full pairing
 *
 * Uses rdtsc for cycle counting on x86_64.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#include "bls12_pairing_all.c"
extern void by_fp_inv(uintptr_t out, uintptr_t x);
#include "bls12_fp2_stubs.c"

/* ================================================================
 * Cycle counter (rdtsc on x86_64)
 * ================================================================ */
static inline uint64_t rdtsc(void) {
    unsigned int lo, hi;
    __asm__ __volatile__ ("rdtsc" : "=a" (lo), "=d" (hi));
    return ((uint64_t)hi << 32) | lo;
}

/* ================================================================
 * Timing utilities
 * ================================================================ */
#define WARMUP  100
#define TRIALS  1000

static int cmp_u64(const void *a, const void *b) {
    uint64_t x = *(const uint64_t *)a;
    uint64_t y = *(const uint64_t *)b;
    return (x > y) - (x < y);
}

static uint64_t median_cycles(uint64_t *times, int n) {
    qsort(times, n, sizeof(uint64_t), cmp_u64);
    return times[n / 2];
}

/* ================================================================
 * Test data: G1 and G2 generator points (Montgomery form)
 * ================================================================ */
static const uint64_t G1_X[6] = {
    0x5cb38790fd530c16ULL, 0x7817fc679976fff5ULL,
    0x154f95c7143ba1c1ULL, 0xf0ae6acdf3d0e747ULL,
    0xedce6ecc21dbf440ULL, 0x120177419e0bfb75ULL
};
static const uint64_t G1_Y[6] = {
    0xbaac93d50ce72271ULL, 0x8c22631a7918fd8eULL,
    0xdd595f13570725ceULL, 0x51ac582950405194ULL,
    0x0e1c8c3fad0059c0ULL, 0x0bbc3efc5008a26aULL
};
static const uint64_t G2_X[12] = {
    0xf5f28fa202940a10ULL, 0xb3f5fb2687b4961aULL,
    0xa1a893b53e2ae580ULL, 0x9894999d1a3caee9ULL,
    0x6f67b7631863366bULL, 0x058191924350bcd7ULL,
    0xa5a9c0759e23f606ULL, 0xaaa0c59dbccd60c3ULL,
    0x3bb17e18e2867806ULL, 0x1b1ab6cc8541b367ULL,
    0xc2b6ed0ef2158547ULL, 0x11922a097360edf3ULL
};
static const uint64_t G2_Y[12] = {
    0x4c730af860494c4aULL, 0x597cfa1f5e369c5aULL,
    0xe7e6856caa0a635aULL, 0xbbefb5e96e0d495fULL,
    0x07d3a975f0ef25a2ULL, 0x0083fd8e7e80dae5ULL,
    0xadc0fc92df64b05dULL, 0x18aa270a2b1461dcULL,
    0x86adac6a3be4eba0ULL, 0x79495c4ec93da33aULL,
    0xe7175850a43ccaedULL, 0x00b2bc2a163de1bfULL
};

/* ================================================================ */
int main(void) {
    uint64_t times[TRIALS];
    uint64_t t0, t1;

    /* Pre-compute a non-trivial Fp12 element for benchmarking */
    uint64_t fp12_val[72];
    bls12_pairing((uintptr_t)fp12_val,
                  (uintptr_t)G1_X, (uintptr_t)G1_Y,
                  (uintptr_t)G2_X, (uintptr_t)G2_Y);

    /* Scratch buffers */
    uint64_t out_fp[6], out_fp2[12], out_fp6[36], out_fp12[72];
    uint64_t a_fp[6], b_fp[6];
    memcpy(a_fp, fp12_val, 48);
    memcpy(b_fp, fp12_val + 6, 48);

    uint64_t a_fp2[12], b_fp2[12];
    memcpy(a_fp2, fp12_val, 96);
    memcpy(b_fp2, fp12_val + 12, 96);

    uint64_t a_fp6[36], b_fp6[36];
    memcpy(a_fp6, fp12_val, 288);
    memcpy(b_fp6, fp12_val + 36, 288);

    uint64_t a_fp12[72], b_fp12[72];
    memcpy(a_fp12, fp12_val, 576);
    memcpy(b_fp12, fp12_val, 576);

    printf("BLS12-381 Verified Implementation - Benchmarks\n");
    printf("===============================================\n");
    printf("Trials: %d (median of sorted cycle counts)\n\n", TRIALS);

    /* --- Fp mul --- */
    for (int i = 0; i < WARMUP; i++)
        bls12_mul((uintptr_t)out_fp, (uintptr_t)a_fp, (uintptr_t)b_fp);
    for (int i = 0; i < TRIALS; i++) {
        t0 = rdtsc();
        bls12_mul((uintptr_t)out_fp, (uintptr_t)a_fp, (uintptr_t)b_fp);
        t1 = rdtsc();
        times[i] = t1 - t0;
    }
    printf("Fp mul:               %7lu cycles\n", median_cycles(times, TRIALS));

    /* --- Fp square --- */
    for (int i = 0; i < WARMUP; i++)
        bls12_square((uintptr_t)out_fp, (uintptr_t)a_fp);
    for (int i = 0; i < TRIALS; i++) {
        t0 = rdtsc();
        bls12_square((uintptr_t)out_fp, (uintptr_t)a_fp);
        t1 = rdtsc();
        times[i] = t1 - t0;
    }
    printf("Fp square:            %7lu cycles\n", median_cycles(times, TRIALS));

    /* --- Fp2 mul --- */
    for (int i = 0; i < WARMUP; i++)
        bls12_Fp2_mul((uintptr_t)out_fp2, (uintptr_t)a_fp2, (uintptr_t)b_fp2);
    for (int i = 0; i < TRIALS; i++) {
        t0 = rdtsc();
        bls12_Fp2_mul((uintptr_t)out_fp2, (uintptr_t)a_fp2, (uintptr_t)b_fp2);
        t1 = rdtsc();
        times[i] = t1 - t0;
    }
    printf("Fp2 mul:              %7lu cycles\n", median_cycles(times, TRIALS));

    /* --- Fp6 mul --- */
    for (int i = 0; i < WARMUP; i++)
        bls12_Fp6_mul((uintptr_t)out_fp6, (uintptr_t)a_fp6, (uintptr_t)b_fp6);
    for (int i = 0; i < TRIALS; i++) {
        t0 = rdtsc();
        bls12_Fp6_mul((uintptr_t)out_fp6, (uintptr_t)a_fp6, (uintptr_t)b_fp6);
        t1 = rdtsc();
        times[i] = t1 - t0;
    }
    printf("Fp6 mul:              %7lu cycles\n", median_cycles(times, TRIALS));

    /* --- Fp12 mul --- */
    for (int i = 0; i < WARMUP; i++)
        bls12_Fp12_mul((uintptr_t)out_fp12, (uintptr_t)a_fp12, (uintptr_t)b_fp12);
    for (int i = 0; i < TRIALS; i++) {
        t0 = rdtsc();
        bls12_Fp12_mul((uintptr_t)out_fp12, (uintptr_t)a_fp12, (uintptr_t)b_fp12);
        t1 = rdtsc();
        times[i] = t1 - t0;
    }
    printf("Fp12 mul:             %7lu cycles\n", median_cycles(times, TRIALS));

    /* --- Fp12 square --- */
    for (int i = 0; i < WARMUP; i++)
        bls12_Fp12_square((uintptr_t)out_fp12, (uintptr_t)a_fp12);
    for (int i = 0; i < TRIALS; i++) {
        t0 = rdtsc();
        bls12_Fp12_square((uintptr_t)out_fp12, (uintptr_t)a_fp12);
        t1 = rdtsc();
        times[i] = t1 - t0;
    }
    printf("Fp12 square:          %7lu cycles\n", median_cycles(times, TRIALS));

    /* --- Miller loop --- */
    for (int i = 0; i < WARMUP; i++)
        bls12_miller_loop((uintptr_t)out_fp12,
                          (uintptr_t)G1_X, (uintptr_t)G1_Y,
                          (uintptr_t)G2_X, (uintptr_t)G2_Y);
    for (int i = 0; i < TRIALS; i++) {
        t0 = rdtsc();
        bls12_miller_loop((uintptr_t)out_fp12,
                          (uintptr_t)G1_X, (uintptr_t)G1_Y,
                          (uintptr_t)G2_X, (uintptr_t)G2_Y);
        t1 = rdtsc();
        times[i] = t1 - t0;
    }
    printf("Miller loop:          %7lu cycles\n", median_cycles(times, TRIALS));

    /* --- Final exponentiation --- */
    uint64_t gamma1[12], gamma2[12], wfrob[12];
    bls12_load_gamma1_p2((uintptr_t)gamma1);
    bls12_load_gamma2_p2((uintptr_t)gamma2);
    bls12_load_w_frob_p2_c1((uintptr_t)wfrob);
    bls12_miller_loop((uintptr_t)a_fp12,
                      (uintptr_t)G1_X, (uintptr_t)G1_Y,
                      (uintptr_t)G2_X, (uintptr_t)G2_Y);
    for (int i = 0; i < WARMUP; i++)
        bls12_final_exp((uintptr_t)out_fp12, (uintptr_t)a_fp12,
                        (uintptr_t)gamma1, (uintptr_t)gamma2, (uintptr_t)wfrob);
    for (int i = 0; i < TRIALS; i++) {
        t0 = rdtsc();
        bls12_final_exp((uintptr_t)out_fp12, (uintptr_t)a_fp12,
                        (uintptr_t)gamma1, (uintptr_t)gamma2, (uintptr_t)wfrob);
        t1 = rdtsc();
        times[i] = t1 - t0;
    }
    printf("Final exponentiation: %7lu cycles\n", median_cycles(times, TRIALS));

    /* --- Full pairing --- */
    for (int i = 0; i < WARMUP; i++)
        bls12_pairing((uintptr_t)out_fp12,
                      (uintptr_t)G1_X, (uintptr_t)G1_Y,
                      (uintptr_t)G2_X, (uintptr_t)G2_Y);
    for (int i = 0; i < TRIALS; i++) {
        t0 = rdtsc();
        bls12_pairing((uintptr_t)out_fp12,
                      (uintptr_t)G1_X, (uintptr_t)G1_Y,
                      (uintptr_t)G2_X, (uintptr_t)G2_Y);
        t1 = rdtsc();
        times[i] = t1 - t0;
    }
    printf("Full pairing:         %7lu cycles\n", median_cycles(times, TRIALS));

    printf("\n");
    return 0;
}
