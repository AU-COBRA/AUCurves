/* Differential test of all BLS12-381 Fp leaf variants in variants.h (6 x 64-bit little-endian
 * limbs, Montgomery form, inputs < p).  The first variant of each op is the reference (the
 * .jazz build, jasminc 2026.09.0 -auto-spill); every other variant of that op is compared with
 * it limb for limb.  Output buffers carry guard words (writes outside out[0..5]) and inputs are
 * checked to be unchanged.
 * usage: test_variants check [N]   N uniform random inputs < p per op (default 10000) + 64 edge pairs
 *        test_variants dump  [N]   N random + edge inputs, "op label a b out" per variant and input
 *                                  (hex, most significant limb first) for check_bigint.py  */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define NL 6
struct variant { const char *op, *label; void (*f)(void); };
#include "variants.h"
typedef void (*f3)(uint64_t *, const uint64_t *, const uint64_t *);
typedef void (*f2)(uint64_t *, const uint64_t *);

static const uint64_t P[NL] = {0xb9feffffffffaaabULL, 0x1eabfffeb153ffffULL, 0x6730d2a0f6b0f624ULL,
                               0x64774b84f38512bfULL, 0x4b1ba7b6434bacd7ULL, 0x1a0111ea397fe69aULL};
static uint64_t s[2] = {0x243f6a8885a308d3ULL, 0x13198a2e03707344ULL};
static uint64_t rnd(void) { /* xorshift128+ */
  uint64_t a = s[0], b = s[1]; s[0] = b; a ^= a << 23; s[1] = a ^ b ^ (a >> 17) ^ (b >> 26);
  return s[1] + b; }
static int lt_p(const uint64_t *x) {
  for (int i = NL - 1; i >= 0; i--) { if (x[i] < P[i]) return 1; if (x[i] > P[i]) return 0; }
  return 0; }
/* uniform below p: 381 random bits (p < 2^381), rejection */
static void rand_fe(uint64_t *x) {
  do { for (int i = 0; i < NL; i++) x[i] = rnd(); x[NL - 1] &= (1ULL << 61) - 1; } while (!lt_p(x));
}
#define NEDGE 8
static void edge_fe(int k, uint64_t *x) {
  memset(x, 0, NL * 8);
  switch (k) {
  case 0: break;                                           /* 0 */
  case 1: x[0] = 1; break;                                 /* 1 */
  case 2: x[0] = 2; break;                                 /* 2 */
  case 3: memcpy(x, P, NL * 8); x[0] -= 1; break;          /* p-1 */
  case 4: memcpy(x, P, NL * 8); x[0] -= 2; break;          /* p-2 */
  case 5: x[1] = 1; break;                                 /* 2^64 */
  case 6: /* R mod p = 2^384 mod p (Montgomery one) */
    x[0] = 0x760900000002fffdULL; x[1] = 0xebf4000bc40c0002ULL; x[2] = 0x5f48985753c758baULL;
    x[3] = 0x77ce585370525745ULL; x[4] = 0x5c071a97a256ec6dULL; x[5] = 0x15f65ec3fa80e493ULL; break;
  case 7: for (int i = 0; i < NL; i++) x[i] = P[i] >> 1 | (i < NL - 1 ? P[i + 1] << 63 : 0); break; /* (p-1)/2 */
  }
}
static void pr(const uint64_t *x) { for (int i = NL - 1; i >= 0; i--) printf("%016llx", (unsigned long long)x[i]); }
#define G 4
#define GUARD 0x5a5a5a5a5a5a5a5aULL

int main(int argc, char **argv) {
  int dump = argc > 1 && !strcmp(argv[1], "dump");
  long n = argc > 2 ? atol(argv[2]) : (dump ? 300 : 10000);
  static long fails[NVAR], cmps[NVAR];
  long bad = 0;
  static uint64_t buf[NVAR][NL + 2 * G];
  for (long it = 0; it < n + NEDGE * NEDGE; it++) {
    uint64_t a[NL], b[NL], a0[NL], b0[NL];
    if (it < n) { rand_fe(a); rand_fe(b); } else { edge_fe((it - n) / NEDGE, a); edge_fe((it - n) % NEDGE, b); }
    memcpy(a0, a, sizeof a); memcpy(b0, b, sizeof b);
    int ref[4] = {-1, -1, -1, -1};
    const char *ops[4] = {"add", "sub", "mul", "square"};
    for (int k = 0; k < NVAR; k++) {
      int o = 0; while (strcmp(ops[o], VARIANTS[k].op)) o++;
      int sq = o == 3;
      uint64_t *out = buf[k] + G;
      for (int i = 0; i < NL + 2 * G; i++) buf[k][i] = GUARD;
      if (sq) ((f2)VARIANTS[k].f)(out, a); else ((f3)VARIANTS[k].f)(out, a, b);
      for (int i = 0; i < G; i++)
        if (buf[k][i] != GUARD || buf[k][G + NL + i] != GUARD) { printf("GUARD %s %s at %ld\n", VARIANTS[k].op, VARIANTS[k].label, it); fails[k]++; }
      if (memcmp(a, a0, sizeof a) || memcmp(b, b0, sizeof b)) { printf("INPUT CHANGED %s %s at %ld\n", VARIANTS[k].op, VARIANTS[k].label, it); fails[k]++; memcpy(a, a0, sizeof a); memcpy(b, b0, sizeof b); }
      if (dump) { printf("%s %s ", VARIANTS[k].op, VARIANTS[k].label); pr(a); printf(" "); pr(sq ? a : b); printf(" "); pr(out); printf("\n"); }
      if (ref[o] < 0) { ref[o] = k; continue; }
      cmps[k]++;
      if (memcmp(buf[ref[o]] + G, out, NL * 8)) {
        if (fails[k] < 3) { printf("MISMATCH %s %s vs %s at %ld: a=", VARIANTS[k].op, VARIANTS[ref[o]].label, VARIANTS[k].label, it); pr(a); printf(" b="); pr(b); printf("\n"); }
        fails[k]++;
      }
    }
  }
  if (!dump)
    for (int k = 0; k < NVAR; k++) {
      bad += fails[k];
      printf("%-7s %-26s %s\n", VARIANTS[k].op, VARIANTS[k].label,
             cmps[k] ? (fails[k] ? "FAIL" : "ok") : "(reference)");
    }
  if (!dump) printf("%ld random + %d edge inputs per op; %ld failures\n", n, NEDGE * NEDGE, bad);
  return bad != 0;
}
