/**
 * Benchmark with CryptOpt-optimized Fp mul/square.
 *
 * This file includes the same pairing code as bench_pairing.c but
 * redirects bls12_mul and bls12_square to CryptOpt assembly versions
 * via function pointer redirection after the static definitions.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

/* Include the pairing code (defines static bls12_mul etc.) */
#include "bls12_pairing_all.c"

/* CryptOpt-generated functions (linked from .o files) */
extern void fiat_bls12_381_p_mul(uint64_t out[6], const uint64_t a[6], const uint64_t b[6]);
extern void fiat_bls12_381_p_square(uint64_t out[6], const uint64_t a[6]);

/* Wrappers that call CryptOpt with bedrock2-compatible signatures */
static void cryptopt_mul(br_word_t out, br_word_t a, br_word_t b) {
    fiat_bls12_381_p_mul((uint64_t*)out, (const uint64_t*)a, (const uint64_t*)b);
}

static void cryptopt_square(br_word_t out, br_word_t a) {
    fiat_bls12_381_p_square((uint64_t*)out, (const uint64_t*)a);
}

/* Include BY inversion and Fp2 stubs (these call static bls12_mul) */
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

/* Test data */
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

int main(void) {
    uint64_t times[TRIALS];
    uint64_t t0, t1;

    /* Scratch */
    uint64_t out_fp[6], a_fp[6], b_fp[6];
    memcpy(a_fp, G1_X, 48);
    memcpy(b_fp, G1_Y, 48);

    printf("BLS12-381 CryptOpt vs Baseline - Benchmarks\n");
    printf("=============================================\n");
    printf("Trials: %d (median of sorted cycle counts)\n\n", TRIALS);

    /* --- Baseline Fp mul (bedrock2) --- */
    for (int i = 0; i < WARMUP; i++)
        bls12_mul((uintptr_t)out_fp, (uintptr_t)a_fp, (uintptr_t)b_fp);
    for (int i = 0; i < TRIALS; i++) {
        t0 = rdtsc();
        bls12_mul((uintptr_t)out_fp, (uintptr_t)a_fp, (uintptr_t)b_fp);
        t1 = rdtsc();
        times[i] = t1 - t0;
    }
    printf("Fp mul (bedrock2):    %7lu cycles\n", median_cycles(times, TRIALS));

    /* --- CryptOpt Fp mul --- */
    for (int i = 0; i < WARMUP; i++)
        cryptopt_mul((uintptr_t)out_fp, (uintptr_t)a_fp, (uintptr_t)b_fp);
    for (int i = 0; i < TRIALS; i++) {
        t0 = rdtsc();
        cryptopt_mul((uintptr_t)out_fp, (uintptr_t)a_fp, (uintptr_t)b_fp);
        t1 = rdtsc();
        times[i] = t1 - t0;
    }
    printf("Fp mul (CryptOpt):    %7lu cycles\n", median_cycles(times, TRIALS));

    /* --- Baseline Fp square (bedrock2) --- */
    for (int i = 0; i < WARMUP; i++)
        bls12_square((uintptr_t)out_fp, (uintptr_t)a_fp);
    for (int i = 0; i < TRIALS; i++) {
        t0 = rdtsc();
        bls12_square((uintptr_t)out_fp, (uintptr_t)a_fp);
        t1 = rdtsc();
        times[i] = t1 - t0;
    }
    printf("Fp sqr (bedrock2):    %7lu cycles\n", median_cycles(times, TRIALS));

    /* --- CryptOpt Fp square --- */
    for (int i = 0; i < WARMUP; i++)
        cryptopt_square((uintptr_t)out_fp, (uintptr_t)a_fp);
    for (int i = 0; i < TRIALS; i++) {
        t0 = rdtsc();
        cryptopt_square((uintptr_t)out_fp, (uintptr_t)a_fp);
        t1 = rdtsc();
        times[i] = t1 - t0;
    }
    printf("Fp sqr (CryptOpt):    %7lu cycles\n", median_cycles(times, TRIALS));

    /* --- Full pairing (using bedrock2 mul/square, not CryptOpt) --- */
    uint64_t out_fp12[72];
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
    printf("\nFull pairing (baseline): %7lu cycles\n", median_cycles(times, TRIALS));

    printf("\nNote: Full pairing uses bedrock2 mul/square (static).\n");
    printf("To use CryptOpt for the full pairing, the extracted code\n");
    printf("needs non-static mul/square or link-time optimization.\n");

    return 0;
}
