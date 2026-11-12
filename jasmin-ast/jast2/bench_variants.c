/* Cycles of every leaf variant in variants.h with the jasmin-spill harness (harness.h of
 * the benchmark of the printed leaves, unchanged): rdtsc reference
 * cycles per call, serial chain x <- op(x, y) with black-boxed operand pointers, 2000 warm-up
 * calls, 10^5 calls per run, median of 11 runs.  Prints "op<TAB>label<TAB>cycles" per variant;
 * med3v.py pins to one core (taskset -c 3) and takes the median of three such runs.  */
#define NL 6
#include "harness.h"
struct variant { const char *op, *label; void (*f)(void); };
#include "variants.h"
int main(void) {
  static const uint64_t p[6] = {0xb9feffffffffaaabULL, 0x1eabfffeb153ffffULL, 0x6730d2a0f6b0f624ULL,
                                0x64774b84f38512bfULL, 0x4b1ba7b6434bacd7ULL, 0x1a0111ea397fe69aULL};
  memcpy(P, p, sizeof P);
  for (int k = 0; k < NVAR; k++) {
    double c = strcmp(VARIANTS[k].op, "square") ? bench3((f3)VARIANTS[k].f) : bench2((f2)VARIANTS[k].f);
    printf("%s\t%s\t%.1f\n", VARIANTS[k].op, VARIANTS[k].label, c);
    fflush(stdout);
  }
  return 0;
}
