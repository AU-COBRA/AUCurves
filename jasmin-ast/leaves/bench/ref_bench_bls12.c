#define NL 6
#include "harness.h"
#define D3(n) void n(uint64_t *, const uint64_t *, const uint64_t *);
#define D2(n) void n(uint64_t *, const uint64_t *);
D3(fiat_bls12_381_p_mul) D2(fiat_bls12_381_p_square)
D3(gcc_bls12_mul) D2(gcc_bls12_square) D3(gcc_bls12_add) D3(gcc_bls12_sub)
D3(clang_bls12_mul) D2(clang_bls12_square) D3(clang_bls12_add) D3(clang_bls12_sub)
D3(jp_bls12_mul) D2(jp_bls12_square) D3(jp_bls12_add) D3(jp_bls12_sub)
D3(sh_bls12_add) D3(sh_bls12_sub)
#ifdef NEW
D3(jn_bls12_mul) D2(jn_bls12_square) D3(jn_bls12_add) D3(jn_bls12_sub)
#endif
int main(void) {
  static const uint64_t p[6] = {0xb9feffffffffaaabULL, 0x1eabfffeb153ffffULL, 0x6730d2a0f6b0f624ULL,
                                0x64774b84f38512bfULL, 0x4b1ba7b6434bacd7ULL, 0x1a0111ea397fe69aULL};
  memcpy(P, p, sizeof P);
  int bad = 0;
  bad |= check3("co mul", gcc_bls12_mul, fiat_bls12_381_p_mul);
  bad |= check2("co sq", gcc_bls12_square, fiat_bls12_381_p_square);
  bad |= check3("clang mul", gcc_bls12_mul, clang_bls12_mul);
  bad |= check3("jp mul", gcc_bls12_mul, jp_bls12_mul);
  bad |= check2("jp sq", gcc_bls12_square, jp_bls12_square);
  bad |= check3("jp add", gcc_bls12_add, jp_bls12_add);
  bad |= check3("jp sub", gcc_bls12_sub, jp_bls12_sub);
  bad |= check3("sh add", gcc_bls12_add, sh_bls12_add);
  bad |= check3("sh sub", gcc_bls12_sub, sh_bls12_sub);
#ifdef NEW
  bad |= check3("jn mul", gcc_bls12_mul, jn_bls12_mul);
  bad |= check2("jn sq", gcc_bls12_square, jn_bls12_square);
  bad |= check3("jn add", gcc_bls12_add, jn_bls12_add);
  bad |= check3("jn sub", gcc_bls12_sub, jn_bls12_sub);
#endif
  printf("crosscheck %s\n", bad ? "FAILED" : "ok (10000 random inputs per pair)");
  printf("%-34s %9s %9s %9s %9s\n", "BLS12-381 Fp (cycles/call)", "mul", "square", "add", "sub");
#ifndef ONLYNEW
  printf("%-34s %9.1f %9.1f %9.1f %9.1f\n", "Jasmin pp_module (-auto-spill)", bench3(jp_bls12_mul), bench2(jp_bls12_square), bench3(jp_bls12_add), bench3(jp_bls12_sub));
#endif
#ifdef NEW
  printf("%-34s %9.1f %9.1f %9.1f %9.1f\n", NEW, bench3(jn_bls12_mul), bench2(jn_bls12_square), bench3(jn_bls12_add), bench3(jn_bls12_sub));
#endif
#ifndef ONLYNEW
  printf("%-34s %9.1f %9.1f %9s %9s\n", "CryptOpt p_mul / p_square", bench3(fiat_bls12_381_p_mul), bench2(fiat_bls12_381_p_square), "-", "-");
  printf("%-34s %9.1f %9.1f %9.1f %9.1f\n", "fiat bedrock2 C, gcc -O3", bench3(gcc_bls12_mul), bench2(gcc_bls12_square), bench3(gcc_bls12_add), bench3(gcc_bls12_sub));
  printf("%-34s %9.1f %9.1f %9.1f %9.1f\n", "fiat bedrock2 C, clang -O3", bench3(clang_bls12_mul), bench2(clang_bls12_square), bench3(clang_bls12_add), bench3(clang_bls12_sub));
  printf("%-34s %9s %9s %9.1f %9.1f\n", "bls12-jasmin-rs jazz add/sub", "-", "-", bench3(sh_bls12_add), bench3(sh_bls12_sub));
#endif
  return bad;
}
