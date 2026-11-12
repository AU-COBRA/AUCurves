/* Leaf benchmark: serial dependency chain x <- op(x, y), operands black-boxed.
 * N calls per run, RUNS runs, median of per-call rdtsc cycles.  */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <x86intrin.h>
#ifndef NL
#error NL
#endif
#define N 100000
#define RUNS 11
typedef void (*f3)(uint64_t *, const uint64_t *, const uint64_t *);
typedef void (*f2)(uint64_t *, const uint64_t *);
#define BB(p) __asm__ volatile("" : "+r"(p) : : "memory")
static int cmpd(const void *a, const void *b) {
  double x = *(const double *)a, y = *(const double *)b; return (x > y) - (x < y); }
static inline uint64_t t_start(void) { _mm_lfence(); uint64_t t = __rdtsc(); _mm_lfence(); return t; }
static inline uint64_t t_stop(void) { unsigned a; uint64_t t = __rdtscp(&a); _mm_lfence(); return t; }
static uint64_t P[NL];
static uint64_t rng = 0x9e3779b97f4a7c15ULL;
static uint64_t rnd(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static void rand_fe(uint64_t *x) { for (int i = 0; i < NL; i++) x[i] = rnd(); x[NL-1] %= P[NL-1]; }
static double bench3(f3 f) {
  double c[RUNS]; uint64_t A[NL], B[NL], Y[NL];
  rand_fe(A); rand_fe(Y);
  for (int w = 0; w < 2000; w++) { f(B, A, Y); memcpy(A, B, sizeof A); }
  for (int r = 0; r < RUNS; r++) {
    uint64_t *x = A, *t = B, *y = Y;
    uint64_t t0 = t_start();
    for (int i = 0; i < N; i++) { BB(x); BB(y); BB(t); f(t, x, y); uint64_t *s = x; x = t; t = s; }
    uint64_t t1 = t_stop();
    c[r] = (double)(t1 - t0) / N;
  }
  qsort(c, RUNS, sizeof c[0], cmpd); return c[RUNS / 2];
}
static double bench2(f2 f) {
  double c[RUNS]; uint64_t A[NL], B[NL];
  rand_fe(A);
  for (int w = 0; w < 2000; w++) { f(B, A); memcpy(A, B, sizeof A); }
  for (int r = 0; r < RUNS; r++) {
    uint64_t *x = A, *t = B;
    uint64_t t0 = t_start();
    for (int i = 0; i < N; i++) { BB(x); BB(t); f(t, x); uint64_t *s = x; x = t; t = s; }
    uint64_t t1 = t_stop();
    c[r] = (double)(t1 - t0) / N;
  }
  qsort(c, RUNS, sizeof c[0], cmpd); return c[RUNS / 2];
}
/* cross-check: every implementation of an op agrees on 10000 random inputs */
static int check3(const char *nm, f3 ref, f3 g) {
  uint64_t a[NL], b[NL], o1[NL], o2[NL];
  for (int i = 0; i < 10000; i++) { rand_fe(a); rand_fe(b); ref(o1, a, b); g(o2, a, b);
    if (memcmp(o1, o2, sizeof o1)) { printf("MISMATCH %s at %d\n", nm, i); return 1; } }
  return 0;
}
static int check2(const char *nm, f2 ref, f2 g) {
  uint64_t a[NL], o1[NL], o2[NL];
  for (int i = 0; i < 10000; i++) { rand_fe(a); ref(o1, a); g(o2, a);
    if (memcmp(o1, o2, sizeof o1)) { printf("MISMATCH %s at %d\n", nm, i); return 1; } }
  return 0;
}
