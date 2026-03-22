#include <stdint.h>
#include <string.h>
#include <assert.h>

#define BR_WORD_MAX UINTPTR_MAX
typedef uintptr_t br_word_t;
typedef intptr_t br_signed_t;

static_assert(sizeof(br_word_t) == sizeof(br_signed_t), "signed size");
static_assert(UINTPTR_MAX <= BR_WORD_MAX, "pointer fits in int");
static_assert(~(br_signed_t)0 == -(br_signed_t)1, "two's complement");

#if __STDC_VERSION__ >= 202311L && __has_include(<stdbit.h>)
  #include <stdbit.h>
  static_assert(__STDC_ENDIAN_NATIVE__ == __STDC_ENDIAN_LITTLE__, "little-endian");
#elif defined(__GNUC__) && defined(__BYTE_ORDER__) && defined(__ORDER_LITTLE_ENDIAN__)
  static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__, "little-endian");
#elif defined(_MSC_VER) && !defined(__clang__) &&                              \
    (defined(_M_IX86) || defined(_M_X64) || defined(_M_ARM) || defined(_M_ARM64))
  // these MSVC targets are little-endian
#else
  #error "failed to confirm that target is little-endian"
#endif

// "An object shall have its stored value accessed only ... a character type."
static inline br_word_t _br_load1(br_word_t a) {
  return *((uint8_t *)a);
}

static inline br_word_t _br_load2(br_word_t a) {
  uint16_t r = 0;
  memcpy(&r, (void *)a, sizeof(r));
  return r;
}

static inline br_word_t _br_load4(br_word_t a) {
  uint32_t r = 0;
  memcpy(&r, (void *)a, sizeof(r));
  return r;
}

static inline br_word_t _br_load(br_word_t a) {
  br_word_t r = 0;
  memcpy(&r, (void *)a, sizeof(r));
  return r;
}

static inline void _br_store1(br_word_t a, uint8_t v) {
  *((uint8_t *)a) = v;
}

static inline void _br_store2(br_word_t a, uint16_t v) {
  memcpy((void *)a, &v, sizeof(v));
}

static inline void _br_store4(br_word_t a, uint32_t v) {
  memcpy((void *)a, &v, sizeof(v));
}

static inline void _br_store(br_word_t a, br_word_t v) {
  memcpy((void *)a, &v, sizeof(v));
}

static inline br_word_t _br_mulhuu(br_word_t a, br_word_t b) {
  #if BR_WORD_MAX == UINT32_MAX
	  return ((uint64_t)a * b) >> 32;
  #elif BR_WORD_MAX == UINT64_MAX && (defined(__GNUC__) || defined(__clang__))
    return ((unsigned __int128)a * b) >> 64;
  #elif defined(_M_X64)
    uint64_t hi;
    _umul128(a, b, &hi);
    return hi;
  #elif defined(_M_ARM64)
    return __umulh(a, b);
  #else
    // See full_mul.v
    br_word_t hh, lh, hl, low, second_halfword_w_oflow, n, ll, M;
    n = ((((0u-(br_word_t)0x1)>>27)&0x3f)+0x1)>>1;
    M = ((br_word_t)0x1<<n)-0x1;
    ll = (a&M)*(b&M);
    lh = (a&M)*(b>>n);
    hl = (a>>n)*(b&M);
    hh = (a>>n)*(b>>n);
    second_halfword_w_oflow = ((ll>>n)+(lh&M))+(hl&M);
    return ((hh+(lh>>n))+(hl>>n))+(second_halfword_w_oflow>>n);
  #endif
}

static inline br_word_t _br_divu(br_word_t a, br_word_t b) {
  if (!b) return -1;
  return a/b;
}

static inline br_word_t _br_remu(br_word_t a, br_word_t b) {
  if (!b) return a;
  return a%b;
}

static void bls12_sub(br_word_t out0, br_word_t in0, br_word_t in1);
/* CryptOpt-optimized mul/square: formally verified by fiat-crypto equivalence checker */
extern void fiat_bls12_381_p_mul(uint64_t out[6], const uint64_t a[6], const uint64_t b[6]);
extern void fiat_bls12_381_p_square(uint64_t out[6], const uint64_t a[6]);
static void bls12_mul(br_word_t out0, br_word_t in0, br_word_t in1) {
  fiat_bls12_381_p_mul((uint64_t*)out0, (const uint64_t*)in0, (const uint64_t*)in1);
}
static void bls12_square(br_word_t out0, br_word_t in0) {
  fiat_bls12_381_p_square((uint64_t*)out0, (const uint64_t*)in0);
}
static void bls12_select_znz(br_word_t out0, br_word_t in0, br_word_t in1, br_word_t in2);
static void bls12_felem_copy(br_word_t out, br_word_t in);
static void bls12_Fp2_mul_xi(br_word_t out, br_word_t x);
static void bls12_Fp6_felem_copy(br_word_t out, br_word_t x);
static void bls12_Fp6_add(br_word_t out, br_word_t inx, br_word_t iny);
static void bls12_Fp6_sub(br_word_t out, br_word_t inx, br_word_t iny);
static void bls12_Fp6_opp(br_word_t out, br_word_t x);
static void bls12_Fp6_mul(br_word_t out, br_word_t inx, br_word_t iny);
static void bls12_Fp6_square(br_word_t out, br_word_t x);
static void bls12_Fp6_inv(br_word_t out, br_word_t x);
static void bls12_Fp6_mul_by_v(br_word_t out, br_word_t x);
static void bls12_Fp12_felem_copy(br_word_t out, br_word_t x);
static void bls12_Fp12_add(br_word_t out, br_word_t inx, br_word_t iny);
static void bls12_Fp12_sub(br_word_t out, br_word_t inx, br_word_t iny);
static void bls12_Fp12_opp(br_word_t out, br_word_t x);
static void bls12_Fp12_conjugate(br_word_t out, br_word_t x);
static void bls12_Fp12_mul(br_word_t out, br_word_t inx, br_word_t iny);
static void bls12_Fp12_square(br_word_t out, br_word_t x);
static void bls12_Fp12_inv(br_word_t out, br_word_t x);
static void bls12_Fp2_conjugate(br_word_t out, br_word_t x);
static void bls12_Fp6_mul_fp2(br_word_t out, br_word_t x, br_word_t s);
static void bls12_Fp6_frobenius(br_word_t out, br_word_t x, br_word_t gamma1, br_word_t gamma2);
static void bls12_Fp6_frobenius_p2(br_word_t out, br_word_t x, br_word_t gamma1_p2, br_word_t gamma2_p2);
static void bls12_Fp12_frobenius(br_word_t out, br_word_t x, br_word_t gamma1, br_word_t gamma2, br_word_t w_frob_c1);
static void bls12_Fp12_frobenius_p2(br_word_t out, br_word_t x, br_word_t gamma1_p2, br_word_t gamma2_p2, br_word_t w_frob_p2_c1);
static void bls12_Fp2_mul_fp(br_word_t out, br_word_t x, br_word_t s);
static void bls12_make_line(br_word_t out, br_word_t lam, br_word_t x_t, br_word_t y_t, br_word_t x_p, br_word_t y_p);
static void bls12_load_gamma1_p2(br_word_t out);
static void bls12_load_gamma2_p2(br_word_t out);
static void bls12_load_w_frob_p2_c1(br_word_t out);
static void bls12_miller_loop(br_word_t out, br_word_t p_x, br_word_t p_y, br_word_t q_x, br_word_t q_y);
static void bls12_final_exp(br_word_t out, br_word_t f, br_word_t gamma1_p2, br_word_t gamma2_p2, br_word_t w_frob_p2_c1);
static void bls12_pairing(br_word_t out, br_word_t p_x, br_word_t p_y, br_word_t q_x, br_word_t q_y);

void bls12_add(br_word_t out0, br_word_t in0, br_word_t in1) {
  br_word_t x6, x0, x13, x1, x7, x15, x2, x8, x17, x3, x9, x19, x4, x10, x21, x5, x11, x25, x27, x29, x31, x23, x33, x12, x36, x24, x37, x14, x39, x26, x40, x16, x42, x28, x43, x18, x45, x30, x46, x20, x48, x32, x49, x35, x22, x51, x34, x52, x38, x41, x44, x47, x50, x53, x54, x55, x56, x57, x58, x59;
  x0 = _br_load(in0+0);
  x1 = _br_load(in0+8);
  x2 = _br_load(in0+16);
  x3 = _br_load(in0+24);
  x4 = _br_load(in0+32);
  x5 = _br_load(in0+40);
  /*skip*/
  x6 = _br_load(in1+0);
  x7 = _br_load(in1+8);
  x8 = _br_load(in1+16);
  x9 = _br_load(in1+24);
  x10 = _br_load(in1+32);
  x11 = _br_load(in1+40);
  /*skip*/
  /*skip*/
  x12 = x0+x6;
  x13 = ((br_word_t)(x12<x0))+x1;
  x14 = x13+x7;
  x15 = (((br_word_t)(x13<x1))+((br_word_t)(x14<x7)))+x2;
  x16 = x15+x8;
  x17 = (((br_word_t)(x15<x2))+((br_word_t)(x16<x8)))+x3;
  x18 = x17+x9;
  x19 = (((br_word_t)(x17<x3))+((br_word_t)(x18<x9)))+x4;
  x20 = x19+x10;
  x21 = (((br_word_t)(x19<x4))+((br_word_t)(x20<x10)))+x5;
  x22 = x21+x11;
  x23 = ((br_word_t)(x21<x5))+((br_word_t)(x22<x11));
  x24 = x12-0xb9feffffffffaaab;
  x25 = x14-0x1eabfffeb153ffff;
  x26 = x25-((br_word_t)(x12<x24));
  x27 = x16-0x6730d2a0f6b0f624;
  x28 = x27-(((br_word_t)(x14<x25))+((br_word_t)(x25<x26)));
  x29 = x18-0x64774b84f38512bf;
  x30 = x29-(((br_word_t)(x16<x27))+((br_word_t)(x27<x28)));
  x31 = x20-0x4b1ba7b6434bacd7;
  x32 = x31-(((br_word_t)(x18<x29))+((br_word_t)(x29<x30)));
  x33 = x22-0x1a0111ea397fe69a;
  x34 = x33-(((br_word_t)(x20<x31))+((br_word_t)(x31<x32)));
  x35 = (br_word_t)(x23<(x23-(((br_word_t)(x22<x33))+((br_word_t)(x33<x34)))));
  x36 = (0u-(br_word_t)1)+((br_word_t)(x35==(br_word_t)0));
  x37 = x36^0xffffffffffffffff;
  x38 = (x12&x36)|(x24&x37);
  x39 = (0u-(br_word_t)1)+((br_word_t)(x35==(br_word_t)0));
  x40 = x39^0xffffffffffffffff;
  x41 = (x14&x39)|(x26&x40);
  x42 = (0u-(br_word_t)1)+((br_word_t)(x35==(br_word_t)0));
  x43 = x42^0xffffffffffffffff;
  x44 = (x16&x42)|(x28&x43);
  x45 = (0u-(br_word_t)1)+((br_word_t)(x35==(br_word_t)0));
  x46 = x45^0xffffffffffffffff;
  x47 = (x18&x45)|(x30&x46);
  x48 = (0u-(br_word_t)1)+((br_word_t)(x35==(br_word_t)0));
  x49 = x48^0xffffffffffffffff;
  x50 = (x20&x48)|(x32&x49);
  x51 = (0u-(br_word_t)1)+((br_word_t)(x35==(br_word_t)0));
  x52 = x51^0xffffffffffffffff;
  x53 = (x22&x51)|(x34&x52);
  x54 = x38;
  x55 = x41;
  x56 = x44;
  x57 = x47;
  x58 = x50;
  x59 = x53;
  /*skip*/
  _br_store(out0+0, x54);
  _br_store(out0+8, x55);
  _br_store(out0+16, x56);
  _br_store(out0+24, x57);
  _br_store(out0+32, x58);
  _br_store(out0+40, x59);
  /*skip*/
}

static void bls12_sub(br_word_t out0, br_word_t in0, br_word_t in1) {
  br_word_t x6, x7, x0, x8, x1, x13, x9, x2, x15, x10, x3, x17, x11, x4, x19, x5, x21, x12, x25, x14, x27, x16, x29, x18, x31, x20, x22, x23, x24, x26, x28, x30, x32, x33, x34, x35, x36, x37, x38, x39;
  x0 = _br_load(in0+0);
  x1 = _br_load(in0+8);
  x2 = _br_load(in0+16);
  x3 = _br_load(in0+24);
  x4 = _br_load(in0+32);
  x5 = _br_load(in0+40);
  /*skip*/
  x6 = _br_load(in1+0);
  x7 = _br_load(in1+8);
  x8 = _br_load(in1+16);
  x9 = _br_load(in1+24);
  x10 = _br_load(in1+32);
  x11 = _br_load(in1+40);
  /*skip*/
  /*skip*/
  x12 = x0-x6;
  x13 = x1-x7;
  x14 = x13-((br_word_t)(x0<x12));
  x15 = x2-x8;
  x16 = x15-(((br_word_t)(x1<x13))+((br_word_t)(x13<x14)));
  x17 = x3-x9;
  x18 = x17-(((br_word_t)(x2<x15))+((br_word_t)(x15<x16)));
  x19 = x4-x10;
  x20 = x19-(((br_word_t)(x3<x17))+((br_word_t)(x17<x18)));
  x21 = x5-x11;
  x22 = x21-(((br_word_t)(x4<x19))+((br_word_t)(x19<x20)));
  x23 = (0u-(br_word_t)1)+((br_word_t)((((br_word_t)(x5<x21))+((br_word_t)(x21<x22)))==(br_word_t)0));
  x24 = x12+(x23&0xb9feffffffffaaab);
  x25 = ((br_word_t)(x24<x12))+x14;
  x26 = x25+(x23&0x1eabfffeb153ffff);
  x27 = (((br_word_t)(x25<x14))+((br_word_t)(x26<(x23&0x1eabfffeb153ffff))))+x16;
  x28 = x27+(x23&0x6730d2a0f6b0f624);
  x29 = (((br_word_t)(x27<x16))+((br_word_t)(x28<(x23&0x6730d2a0f6b0f624))))+x18;
  x30 = x29+(x23&0x64774b84f38512bf);
  x31 = (((br_word_t)(x29<x18))+((br_word_t)(x30<(x23&0x64774b84f38512bf))))+x20;
  x32 = x31+(x23&0x4b1ba7b6434bacd7);
  x33 = ((((br_word_t)(x31<x20))+((br_word_t)(x32<(x23&0x4b1ba7b6434bacd7))))+x22)+(x23&0x1a0111ea397fe69a);
  x34 = x24;
  x35 = x26;
  x36 = x28;
  x37 = x30;
  x38 = x32;
  x39 = x33;
  /*skip*/
  _br_store(out0+0, x34);
  _br_store(out0+8, x35);
  _br_store(out0+16, x36);
  _br_store(out0+24, x37);
  _br_store(out0+32, x38);
  _br_store(out0+40, x39);
  /*skip*/
}

static void bls12_select_znz(br_word_t out0, br_word_t in0, br_word_t in1, br_word_t in2) {
  br_word_t x6, x12, x0, x13, x7, x15, x1, x16, x8, x18, x2, x19, x9, x21, x3, x22, x10, x24, x4, x25, x11, x27, x5, x28, x14, x17, x20, x23, x26, x29, x30, x31, x32, x33, x34, x35;
  /*skip*/
  x0 = _br_load(in1+0);
  x1 = _br_load(in1+8);
  x2 = _br_load(in1+16);
  x3 = _br_load(in1+24);
  x4 = _br_load(in1+32);
  x5 = _br_load(in1+40);
  /*skip*/
  x6 = _br_load(in2+0);
  x7 = _br_load(in2+8);
  x8 = _br_load(in2+16);
  x9 = _br_load(in2+24);
  x10 = _br_load(in2+32);
  x11 = _br_load(in2+40);
  /*skip*/
  /*skip*/
  x12 = (0u-(br_word_t)1)+((br_word_t)(in0==(br_word_t)0));
  x13 = x12^0xffffffffffffffff;
  x14 = (x6&x12)|(x0&x13);
  x15 = (0u-(br_word_t)1)+((br_word_t)(in0==(br_word_t)0));
  x16 = x15^0xffffffffffffffff;
  x17 = (x7&x15)|(x1&x16);
  x18 = (0u-(br_word_t)1)+((br_word_t)(in0==(br_word_t)0));
  x19 = x18^0xffffffffffffffff;
  x20 = (x8&x18)|(x2&x19);
  x21 = (0u-(br_word_t)1)+((br_word_t)(in0==(br_word_t)0));
  x22 = x21^0xffffffffffffffff;
  x23 = (x9&x21)|(x3&x22);
  x24 = (0u-(br_word_t)1)+((br_word_t)(in0==(br_word_t)0));
  x25 = x24^0xffffffffffffffff;
  x26 = (x10&x24)|(x4&x25);
  x27 = (0u-(br_word_t)1)+((br_word_t)(in0==(br_word_t)0));
  x28 = x27^0xffffffffffffffff;
  x29 = (x11&x27)|(x5&x28);
  x30 = x14;
  x31 = x17;
  x32 = x20;
  x33 = x23;
  x34 = x26;
  x35 = x29;
  /*skip*/
  _br_store(out0+0, x30);
  _br_store(out0+8, x31);
  _br_store(out0+16, x32);
  _br_store(out0+24, x33);
  _br_store(out0+32, x34);
  _br_store(out0+40, x35);
  /*skip*/
}

static void bls12_felem_copy(br_word_t out, br_word_t in) {
  _br_store(out, _br_load(in));
  _br_store(out+8, _br_load(in+8));
  _br_store(out+16, _br_load(in+16));
  _br_store(out+24, _br_load(in+24));
  _br_store(out+32, _br_load(in+32));
  _br_store(out+40, _br_load(in+40));
}

static void bls12_Fp2_mul_xi(br_word_t out, br_word_t x) {
  br_word_t tmp;
  uint8_t _br_stackalloc_tmp[96] = {0}; tmp = (br_word_t)&_br_stackalloc_tmp;
  bls12_felem_copy(tmp, x);
  bls12_felem_copy(tmp+48, x+48);
  bls12_sub(out, tmp, tmp+48);
  bls12_add(out+48, tmp, tmp+48);
}

static void bls12_Fp6_felem_copy(br_word_t out, br_word_t x) {
  bls12_Fp2_felem_copy(out, x);
  bls12_Fp2_felem_copy(out+96, x+96);
  bls12_Fp2_felem_copy(out+192, x+192);
}

static void bls12_Fp6_add(br_word_t out, br_word_t inx, br_word_t iny) {
  br_word_t allocx, allocy;
  uint8_t _br_stackalloc_allocx[0x120] = {0}; allocx = (br_word_t)&_br_stackalloc_allocx;
  uint8_t _br_stackalloc_allocy[0x120] = {0}; allocy = (br_word_t)&_br_stackalloc_allocy;
  bls12_Fp6_felem_copy(allocx, inx);
  bls12_Fp6_felem_copy(allocy, iny);
  bls12_Fp2_add(out, allocx, allocy);
  bls12_Fp2_add(out+96, allocx+96, allocy+96);
  bls12_Fp2_add(out+192, allocx+192, allocy+192);
}

static void bls12_Fp6_sub(br_word_t out, br_word_t inx, br_word_t iny) {
  br_word_t allocx, allocy;
  uint8_t _br_stackalloc_allocx[0x120] = {0}; allocx = (br_word_t)&_br_stackalloc_allocx;
  uint8_t _br_stackalloc_allocy[0x120] = {0}; allocy = (br_word_t)&_br_stackalloc_allocy;
  bls12_Fp6_felem_copy(allocx, inx);
  bls12_Fp6_felem_copy(allocy, iny);
  bls12_Fp2_sub(out, allocx, allocy);
  bls12_Fp2_sub(out+96, allocx+96, allocy+96);
  bls12_Fp2_sub(out+192, allocx+192, allocy+192);
}

static void bls12_Fp6_opp(br_word_t out, br_word_t x) {
  br_word_t allocx;
  uint8_t _br_stackalloc_allocx[0x120] = {0}; allocx = (br_word_t)&_br_stackalloc_allocx;
  bls12_Fp6_felem_copy(allocx, x);
  bls12_Fp2_opp(out, allocx);
  bls12_Fp2_opp(out+96, allocx+96);
  bls12_Fp2_opp(out+192, allocx+192);
}

static void bls12_Fp6_mul(br_word_t out, br_word_t inx, br_word_t iny) {
  br_word_t allocx, allocy, u, a0b0, a2b2, t, a1b1;
  uint8_t _br_stackalloc_allocx[0x120] = {0}; allocx = (br_word_t)&_br_stackalloc_allocx;
  uint8_t _br_stackalloc_allocy[0x120] = {0}; allocy = (br_word_t)&_br_stackalloc_allocy;
  uint8_t _br_stackalloc_a0b0[96] = {0}; a0b0 = (br_word_t)&_br_stackalloc_a0b0;
  uint8_t _br_stackalloc_a1b1[96] = {0}; a1b1 = (br_word_t)&_br_stackalloc_a1b1;
  uint8_t _br_stackalloc_a2b2[96] = {0}; a2b2 = (br_word_t)&_br_stackalloc_a2b2;
  uint8_t _br_stackalloc_t[96] = {0}; t = (br_word_t)&_br_stackalloc_t;
  uint8_t _br_stackalloc_u[96] = {0}; u = (br_word_t)&_br_stackalloc_u;
  bls12_Fp6_felem_copy(allocx, inx);
  bls12_Fp6_felem_copy(allocy, iny);
  bls12_Fp2_mul(a0b0, allocx, allocy);
  bls12_Fp2_mul(a1b1, allocx+96, allocy+96);
  bls12_Fp2_mul(a2b2, allocx+192, allocy+192);
  bls12_Fp2_add(t, allocx+96, allocx+192);
  bls12_Fp2_add(u, allocy+96, allocy+192);
  bls12_Fp2_mul(t, t, u);
  bls12_Fp2_sub(t, t, a1b1);
  bls12_Fp2_sub(t, t, a2b2);
  bls12_Fp2_mul_xi(t, t);
  bls12_Fp2_add(out, a0b0, t);
  bls12_Fp2_add(t, allocx, allocx+96);
  bls12_Fp2_add(u, allocy, allocy+96);
  bls12_Fp2_mul(t, t, u);
  bls12_Fp2_sub(t, t, a0b0);
  bls12_Fp2_sub(t, t, a1b1);
  bls12_Fp2_mul_xi(u, a2b2);
  bls12_Fp2_add(out+96, t, u);
  bls12_Fp2_add(t, allocx, allocx+192);
  bls12_Fp2_add(u, allocy, allocy+192);
  bls12_Fp2_mul(t, t, u);
  bls12_Fp2_sub(t, t, a0b0);
  bls12_Fp2_sub(t, t, a2b2);
  bls12_Fp2_add(out+192, t, a1b1);
}

static void bls12_Fp6_square(br_word_t out, br_word_t x) {
  br_word_t allocx, s1, s2, s3, s0, t, s4;
  uint8_t _br_stackalloc_allocx[0x120] = {0}; allocx = (br_word_t)&_br_stackalloc_allocx;
  uint8_t _br_stackalloc_s0[96] = {0}; s0 = (br_word_t)&_br_stackalloc_s0;
  uint8_t _br_stackalloc_s1[96] = {0}; s1 = (br_word_t)&_br_stackalloc_s1;
  uint8_t _br_stackalloc_s2[96] = {0}; s2 = (br_word_t)&_br_stackalloc_s2;
  uint8_t _br_stackalloc_s3[96] = {0}; s3 = (br_word_t)&_br_stackalloc_s3;
  uint8_t _br_stackalloc_s4[96] = {0}; s4 = (br_word_t)&_br_stackalloc_s4;
  uint8_t _br_stackalloc_t[96] = {0}; t = (br_word_t)&_br_stackalloc_t;
  bls12_Fp6_felem_copy(allocx, x);
  bls12_Fp2_square(s0, allocx);
  bls12_Fp2_mul(t, allocx, allocx+96);
  bls12_Fp2_add(s1, t, t);
  bls12_Fp2_sub(t, allocx, allocx+96);
  bls12_Fp2_add(t, t, allocx+192);
  bls12_Fp2_square(s2, t);
  bls12_Fp2_mul(t, allocx+96, allocx+192);
  bls12_Fp2_add(s3, t, t);
  bls12_Fp2_square(s4, allocx+192);
  bls12_Fp2_mul_xi(t, s3);
  bls12_Fp2_add(out, s0, t);
  bls12_Fp2_mul_xi(t, s4);
  bls12_Fp2_add(out+96, s1, t);
  bls12_Fp2_add(t, s1, s2);
  bls12_Fp2_add(t, t, s3);
  bls12_Fp2_sub(t, t, s0);
  bls12_Fp2_sub(out+192, t, s4);
}

static void bls12_Fp6_inv(br_word_t out, br_word_t x) {
  br_word_t allocx, t3, t2, vA, vB, vC, t1;
  uint8_t _br_stackalloc_allocx[0x120] = {0}; allocx = (br_word_t)&_br_stackalloc_allocx;
  uint8_t _br_stackalloc_vA[96] = {0}; vA = (br_word_t)&_br_stackalloc_vA;
  uint8_t _br_stackalloc_vB[96] = {0}; vB = (br_word_t)&_br_stackalloc_vB;
  uint8_t _br_stackalloc_vC[96] = {0}; vC = (br_word_t)&_br_stackalloc_vC;
  uint8_t _br_stackalloc_t1[96] = {0}; t1 = (br_word_t)&_br_stackalloc_t1;
  uint8_t _br_stackalloc_t2[96] = {0}; t2 = (br_word_t)&_br_stackalloc_t2;
  uint8_t _br_stackalloc_t3[96] = {0}; t3 = (br_word_t)&_br_stackalloc_t3;
  bls12_Fp6_felem_copy(allocx, x);
  bls12_Fp2_square(t1, allocx);
  bls12_Fp2_mul(t2, allocx+96, allocx+192);
  bls12_Fp2_mul_xi(t3, t2);
  bls12_Fp2_sub(vA, t1, t3);
  bls12_Fp2_square(t1, allocx+192);
  bls12_Fp2_mul_xi(t3, t1);
  bls12_Fp2_mul(t2, allocx, allocx+96);
  bls12_Fp2_sub(vB, t3, t2);
  bls12_Fp2_square(t1, allocx+96);
  bls12_Fp2_mul(t2, allocx, allocx+192);
  bls12_Fp2_sub(vC, t1, t2);
  bls12_Fp2_mul(t1, allocx, vA);
  bls12_Fp2_mul(t2, allocx+192, vB);
  bls12_Fp2_mul(t3, allocx+96, vC);
  bls12_Fp2_add(t2, t2, t3);
  bls12_Fp2_mul_xi(t2, t2);
  bls12_Fp2_add(t1, t1, t2);
  bls12_Fp2_inv(t1, t1);
  bls12_Fp2_mul(out, vA, t1);
  bls12_Fp2_mul(out+96, vB, t1);
  bls12_Fp2_mul(out+192, vC, t1);
}

static void bls12_Fp6_mul_by_v(br_word_t out, br_word_t x) {
  br_word_t tmp;
  uint8_t _br_stackalloc_tmp[0x120] = {0}; tmp = (br_word_t)&_br_stackalloc_tmp;
  bls12_Fp6_felem_copy(tmp, x);
  bls12_Fp2_mul_xi(out, tmp+192);
  bls12_Fp2_felem_copy(out+96, tmp);
  bls12_Fp2_felem_copy(out+192, tmp+96);
}

static void bls12_Fp12_felem_copy(br_word_t out, br_word_t x) {
  bls12_Fp6_felem_copy(out, x);
  bls12_Fp6_felem_copy(out+0x120, x+0x120);
}

static void bls12_Fp12_add(br_word_t out, br_word_t inx, br_word_t iny) {
  br_word_t ax, ay;
  uint8_t _br_stackalloc_ax[0x240] = {0}; ax = (br_word_t)&_br_stackalloc_ax;
  uint8_t _br_stackalloc_ay[0x240] = {0}; ay = (br_word_t)&_br_stackalloc_ay;
  bls12_Fp12_felem_copy(ax, inx);
  bls12_Fp12_felem_copy(ay, iny);
  bls12_Fp6_add(out, ax, ay);
  bls12_Fp6_add(out+0x120, ax+0x120, ay+0x120);
}

static void bls12_Fp12_sub(br_word_t out, br_word_t inx, br_word_t iny) {
  br_word_t ax, ay;
  uint8_t _br_stackalloc_ax[0x240] = {0}; ax = (br_word_t)&_br_stackalloc_ax;
  uint8_t _br_stackalloc_ay[0x240] = {0}; ay = (br_word_t)&_br_stackalloc_ay;
  bls12_Fp12_felem_copy(ax, inx);
  bls12_Fp12_felem_copy(ay, iny);
  bls12_Fp6_sub(out, ax, ay);
  bls12_Fp6_sub(out+0x120, ax+0x120, ay+0x120);
}

static void bls12_Fp12_opp(br_word_t out, br_word_t x) {
  br_word_t allocx;
  uint8_t _br_stackalloc_allocx[0x240] = {0}; allocx = (br_word_t)&_br_stackalloc_allocx;
  bls12_Fp12_felem_copy(allocx, x);
  bls12_Fp6_opp(out, allocx);
  bls12_Fp6_opp(out+0x120, allocx+0x120);
}

static void bls12_Fp12_conjugate(br_word_t out, br_word_t x) {
  br_word_t allocx;
  uint8_t _br_stackalloc_allocx[0x240] = {0}; allocx = (br_word_t)&_br_stackalloc_allocx;
  bls12_Fp12_felem_copy(allocx, x);
  bls12_Fp6_felem_copy(out, allocx);
  bls12_Fp6_opp(out+0x120, allocx+0x120);
}

static void bls12_Fp12_mul(br_word_t out, br_word_t inx, br_word_t iny) {
  br_word_t ax, ay, u, v0, t, v1;
  uint8_t _br_stackalloc_ax[0x240] = {0}; ax = (br_word_t)&_br_stackalloc_ax;
  uint8_t _br_stackalloc_ay[0x240] = {0}; ay = (br_word_t)&_br_stackalloc_ay;
  bls12_Fp12_felem_copy(ax, inx);
  bls12_Fp12_felem_copy(ay, iny);
  uint8_t _br_stackalloc_v0[0x120] = {0}; v0 = (br_word_t)&_br_stackalloc_v0;
  uint8_t _br_stackalloc_v1[0x120] = {0}; v1 = (br_word_t)&_br_stackalloc_v1;
  uint8_t _br_stackalloc_t[0x120] = {0}; t = (br_word_t)&_br_stackalloc_t;
  uint8_t _br_stackalloc_u[0x120] = {0}; u = (br_word_t)&_br_stackalloc_u;
  bls12_Fp6_mul(v0, ax, ay);
  bls12_Fp6_mul(v1, ax+0x120, ay+0x120);
  bls12_Fp6_add(t, ax, ax+0x120);
  bls12_Fp6_add(u, ay, ay+0x120);
  bls12_Fp6_mul(t, t, u);
  bls12_Fp6_mul_by_v(u, v1);
  bls12_Fp6_add(out, v0, u);
  bls12_Fp6_sub(t, t, v0);
  bls12_Fp6_sub(out+0x120, t, v1);
}

static void bls12_Fp12_square(br_word_t out, br_word_t x) {
  br_word_t allocx, t0, t1, t2;
  uint8_t _br_stackalloc_allocx[0x240] = {0}; allocx = (br_word_t)&_br_stackalloc_allocx;
  bls12_Fp12_felem_copy(allocx, x);
  uint8_t _br_stackalloc_t0[0x120] = {0}; t0 = (br_word_t)&_br_stackalloc_t0;
  uint8_t _br_stackalloc_t1[0x120] = {0}; t1 = (br_word_t)&_br_stackalloc_t1;
  uint8_t _br_stackalloc_t2[0x120] = {0}; t2 = (br_word_t)&_br_stackalloc_t2;
  bls12_Fp6_square(t0, allocx);
  bls12_Fp6_square(t1, allocx+0x120);
  bls12_Fp6_mul(t2, allocx, allocx+0x120);
  bls12_Fp6_mul_by_v(t1, t1);
  bls12_Fp6_add(out, t0, t1);
  bls12_Fp6_add(out+0x120, t2, t2);
}

static void bls12_Fp12_inv(br_word_t out, br_word_t x) {
  br_word_t t1, allocx, t0;
  uint8_t _br_stackalloc_allocx[0x240] = {0}; allocx = (br_word_t)&_br_stackalloc_allocx;
  bls12_Fp12_felem_copy(allocx, x);
  uint8_t _br_stackalloc_t0[0x120] = {0}; t0 = (br_word_t)&_br_stackalloc_t0;
  uint8_t _br_stackalloc_t1[0x120] = {0}; t1 = (br_word_t)&_br_stackalloc_t1;
  bls12_Fp6_square(t0, allocx);
  bls12_Fp6_square(t1, allocx+0x120);
  bls12_Fp6_mul_by_v(t1, t1);
  bls12_Fp6_sub(t0, t0, t1);
  bls12_Fp6_inv(t0, t0);
  bls12_Fp6_mul(out, allocx, t0);
  bls12_Fp6_mul(out+0x120, allocx+0x120, t0);
  bls12_Fp6_opp(out+0x120, out+0x120);
}

static void bls12_Fp2_conjugate(br_word_t out, br_word_t x) {
  bls12_felem_copy(out, x);
  bls12_opp(out+48, x+48);
}

static void bls12_Fp6_mul_fp2(br_word_t out, br_word_t x, br_word_t s) {
  br_word_t s_copy;
  uint8_t _br_stackalloc_s_copy[96] = {0}; s_copy = (br_word_t)&_br_stackalloc_s_copy;
  bls12_Fp2_felem_copy(s_copy, s);
  bls12_Fp2_mul(out, x, s_copy);
  bls12_Fp2_mul(out+96, x+96, s_copy);
  bls12_Fp2_mul(out+192, x+192, s_copy);
}

static void bls12_Fp6_frobenius(br_word_t out, br_word_t x, br_word_t gamma1, br_word_t gamma2) {
  br_word_t tmp;
  uint8_t _br_stackalloc_tmp[0x120] = {0}; tmp = (br_word_t)&_br_stackalloc_tmp;
  bls12_Fp2_conjugate(tmp, x);
  bls12_Fp2_conjugate(tmp+96, x+96);
  bls12_Fp2_conjugate(tmp+192, x+192);
  bls12_Fp2_felem_copy(out, tmp);
  bls12_Fp2_mul(out+96, tmp+96, gamma1);
  bls12_Fp2_mul(out+192, tmp+192, gamma2);
}

static void bls12_Fp6_frobenius_p2(br_word_t out, br_word_t x, br_word_t gamma1_p2, br_word_t gamma2_p2) {
  bls12_Fp2_felem_copy(out, x);
  bls12_Fp2_mul(out+96, x+96, gamma1_p2);
  bls12_Fp2_mul(out+192, x+192, gamma2_p2);
}

static void bls12_Fp12_frobenius(br_word_t out, br_word_t x, br_word_t gamma1, br_word_t gamma2, br_word_t w_frob_c1) {
  bls12_Fp6_frobenius(out, x, gamma1, gamma2);
  bls12_Fp6_frobenius(out+0x120, x+0x120, gamma1, gamma2);
  bls12_Fp6_mul_fp2(out+0x120, out+0x120, w_frob_c1);
}

static void bls12_Fp12_frobenius_p2(br_word_t out, br_word_t x, br_word_t gamma1_p2, br_word_t gamma2_p2, br_word_t w_frob_p2_c1) {
  bls12_Fp6_frobenius_p2(out, x, gamma1_p2, gamma2_p2);
  bls12_Fp6_frobenius_p2(out+0x120, x+0x120, gamma1_p2, gamma2_p2);
  bls12_Fp6_mul_fp2(out+0x120, out+0x120, w_frob_p2_c1);
}

static void bls12_Fp2_mul_fp(br_word_t out, br_word_t x, br_word_t s) {
  bls12_mul(out, x, s);
  bls12_mul(out+48, x+48, s);
}

static void bls12_make_line(br_word_t out, br_word_t lam, br_word_t x_t, br_word_t y_t, br_word_t x_p, br_word_t y_p) {
  br_word_t tmp;
  uint8_t _br_stackalloc_tmp[96] = {0}; tmp = (br_word_t)&_br_stackalloc_tmp;
  bls12_Fp2_mul(out, lam, x_t);
  bls12_Fp2_sub(out, out, y_t);
  bls12_Fp2_mul_fp(tmp, lam, x_p);
  bls12_Fp2_opp(out+96, tmp);
  bls12_from_word(out+192, (br_word_t)0);
  bls12_from_word((out+192)+48, (br_word_t)0);
  bls12_from_word(out+0x120, (br_word_t)0);
  bls12_from_word((out+0x120)+48, (br_word_t)0);
  bls12_felem_copy((out+0x120)+96, y_p);
  bls12_from_word(((out+0x120)+96)+48, (br_word_t)0);
  bls12_from_word((out+0x120)+192, (br_word_t)0);
  bls12_from_word(((out+0x120)+192)+48, (br_word_t)0);
}

static void bls12_load_gamma1_p2(br_word_t out) {
  _br_store(out, (br_word_t)0x2e01fffffffefffe );
  _br_store(out+8, (br_word_t)0xde17d813620a0002);
  _br_store(out+16, (br_word_t)0xddb3a93be6f89688);
  _br_store(out+24, (br_word_t)0xba69c6076a0f77ea);
  _br_store(out+32, (br_word_t)0x5f19672fdf76ce51);
  _br_store(out+40, (br_word_t)0);
  _br_store(out+48, (br_word_t)0);
  _br_store(out+56, (br_word_t)0);
  _br_store(out+64, (br_word_t)0);
  _br_store(out+72, (br_word_t)0);
  _br_store(out+80, (br_word_t)0);
  _br_store(out+88, (br_word_t)0);
}

static void bls12_load_gamma2_p2(br_word_t out) {
  _br_store(out, (br_word_t)0x8bfd00000000aaac);
  _br_store(out+8, (br_word_t)0x409427eb4f49fffd);
  _br_store(out+16, (br_word_t)0x897d29650fb85f9b);
  _br_store(out+24, (br_word_t)0xaa0d857d89759ad4);
  _br_store(out+32, (br_word_t)0xec02408663d4de85);
  _br_store(out+40, (br_word_t)0x1a0111ea397fe699);
  _br_store(out+48, (br_word_t)0);
  _br_store(out+56, (br_word_t)0);
  _br_store(out+64, (br_word_t)0);
  _br_store(out+72, (br_word_t)0);
  _br_store(out+80, (br_word_t)0);
  _br_store(out+88, (br_word_t)0);
}

static void bls12_load_w_frob_p2_c1(br_word_t out) {
  _br_store(out, (br_word_t)0x2e01fffffffeffff);
  _br_store(out+8, (br_word_t)0xde17d813620a0002);
  _br_store(out+16, (br_word_t)0xddb3a93be6f89688);
  _br_store(out+24, (br_word_t)0xba69c6076a0f77ea);
  _br_store(out+32, (br_word_t)0x5f19672fdf76ce51);
  _br_store(out+40, (br_word_t)0);
  _br_store(out+48, (br_word_t)0);
  _br_store(out+56, (br_word_t)0);
  _br_store(out+64, (br_word_t)0);
  _br_store(out+72, (br_word_t)0);
  _br_store(out+80, (br_word_t)0);
  _br_store(out+88, (br_word_t)0);
}

static void bls12_miller_loop(br_word_t out, br_word_t p_x, br_word_t p_y, br_word_t q_x, br_word_t q_y) {
  br_word_t i, bit, line, lambda, tmp1, t_y, t_x, tmp2, f;
  uint8_t _br_stackalloc_f[0x240] = {0}; f = (br_word_t)&_br_stackalloc_f;
  uint8_t _br_stackalloc_t_x[96] = {0}; t_x = (br_word_t)&_br_stackalloc_t_x;
  uint8_t _br_stackalloc_t_y[96] = {0}; t_y = (br_word_t)&_br_stackalloc_t_y;
  uint8_t _br_stackalloc_lambda[96] = {0}; lambda = (br_word_t)&_br_stackalloc_lambda;
  uint8_t _br_stackalloc_tmp1[96] = {0}; tmp1 = (br_word_t)&_br_stackalloc_tmp1;
  uint8_t _br_stackalloc_tmp2[96] = {0}; tmp2 = (br_word_t)&_br_stackalloc_tmp2;
  uint8_t _br_stackalloc_line[0x240] = {0}; line = (br_word_t)&_br_stackalloc_line;
  bls12_from_word(f, (br_word_t)1);
  bls12_from_word(f+48, (br_word_t)0);
  bls12_from_word(f+96, (br_word_t)0);
  bls12_from_word((f+96)+48, (br_word_t)0);
  bls12_from_word(f+192, (br_word_t)0);
  bls12_from_word((f+192)+48, (br_word_t)0);
  bls12_from_word(f+0x120, (br_word_t)0);
  bls12_from_word((f+0x120)+48, (br_word_t)0);
  bls12_from_word((f+0x120)+96, (br_word_t)0);
  bls12_from_word(((f+0x120)+96)+48, (br_word_t)0);
  bls12_from_word((f+0x120)+192, (br_word_t)0);
  bls12_from_word(((f+0x120)+192)+48, (br_word_t)0);
  bls12_Fp2_felem_copy(t_x, q_x);
  bls12_Fp2_felem_copy(t_y, q_y);
  i = (br_word_t)63;
  while (i) {
    i = i-1;
    bls12_Fp2_square(tmp1, t_x);
    bls12_Fp2_add(lambda, tmp1, tmp1);
    bls12_Fp2_add(lambda, lambda, tmp1);
    bls12_Fp2_add(tmp1, t_y, t_y);
    bls12_Fp2_inv(tmp1, tmp1);
    bls12_Fp2_mul(lambda, lambda, tmp1);
    bls12_make_line(line, lambda, t_x, t_y, p_x, p_y);
    bls12_Fp12_square(f, f);
    bls12_Fp12_mul(f, f, line);
    bls12_Fp2_square(tmp1, lambda);
    bls12_Fp2_sub(tmp1, tmp1, t_x);
    bls12_Fp2_sub(tmp2, tmp1, t_x);
    bls12_Fp2_sub(tmp1, t_x, tmp2);
    bls12_Fp2_mul(tmp1, lambda, tmp1);
    bls12_Fp2_sub(t_y, tmp1, t_y);
    bls12_Fp2_felem_copy(t_x, tmp2);
    bit = ((br_word_t)0xd201000000010000>>(i&(sizeof(br_word_t)*8-1)))&1;
    if (bit) {
      bls12_Fp2_sub(tmp1, q_y, t_y);
      bls12_Fp2_sub(tmp2, q_x, t_x);
      bls12_Fp2_inv(tmp2, tmp2);
      bls12_Fp2_mul(lambda, tmp1, tmp2);
      bls12_make_line(line, lambda, t_x, t_y, p_x, p_y);
      bls12_Fp12_mul(f, f, line);
      bls12_Fp2_square(tmp1, lambda);
      bls12_Fp2_sub(tmp1, tmp1, t_x);
      bls12_Fp2_sub(tmp2, tmp1, q_x);
      bls12_Fp2_sub(tmp1, t_x, tmp2);
      bls12_Fp2_mul(tmp1, lambda, tmp1);
      bls12_Fp2_sub(t_y, tmp1, t_y);
      bls12_Fp2_felem_copy(t_x, tmp2);
    } else {
      /*skip*/
    }
  }
  bls12_Fp12_felem_copy(out, f);
}

static void bls12_final_exp(br_word_t out, br_word_t f, br_word_t gamma1_p2, br_word_t gamma2_p2, br_word_t w_frob_p2_c1) {
  br_word_t tmp, h3, word, i, bit, base, started, result;
  uint8_t _br_stackalloc_result[0x240] = {0}; result = (br_word_t)&_br_stackalloc_result;
  uint8_t _br_stackalloc_tmp[0x240] = {0}; tmp = (br_word_t)&_br_stackalloc_tmp;
  uint8_t _br_stackalloc_base[0x240] = {0}; base = (br_word_t)&_br_stackalloc_base;
  uint8_t _br_stackalloc_h3[160] = {0}; h3 = (br_word_t)&_br_stackalloc_h3;
  bls12_Fp12_conjugate(result, f);
  bls12_Fp12_inv(tmp, f);
  bls12_Fp12_mul(result, result, tmp);
  bls12_Fp12_frobenius_p2(tmp, result, gamma1_p2, gamma2_p2, w_frob_p2_c1);
  bls12_Fp12_mul(result, tmp, result);
  bls12_Fp12_felem_copy(base, result);
  bls12_from_word(result, (br_word_t)1);
  bls12_from_word(result+48, (br_word_t)0);
  bls12_from_word(result+96, (br_word_t)0);
  bls12_from_word((result+96)+48, (br_word_t)0);
  bls12_from_word(result+192, (br_word_t)0);
  bls12_from_word((result+192)+48, (br_word_t)0);
  bls12_from_word(result+0x120, (br_word_t)0);
  bls12_from_word((result+0x120)+48, (br_word_t)0);
  bls12_from_word((result+0x120)+96, (br_word_t)0);
  bls12_from_word(((result+0x120)+96)+48, (br_word_t)0);
  bls12_from_word((result+0x120)+192, (br_word_t)0);
  bls12_from_word(((result+0x120)+192)+48, (br_word_t)0);
  _br_store(h3, (br_word_t)0xe516c3f438e3ba79);
  _br_store(h3+8, (br_word_t)0xfa9912aae208ccf1);
  _br_store(h3+16, (br_word_t)0x905ce937335d5b68);
  _br_store(h3+24, (br_word_t)0xc71a2629b0dea236);
  _br_store(h3+32, (br_word_t)0x83774940996754c8);
  _br_store(h3+40, (br_word_t)0x21d160aeb6a1e799);
  _br_store(h3+48, (br_word_t)0x2ed0b283ed237db4);
  _br_store(h3+56, (br_word_t)0x915c97f36c6f1821);
  _br_store(h3+64, (br_word_t)0x67f17fcbde783765);
  _br_store(h3+72, (br_word_t)0x2378b9039096d1b7);
  _br_store(h3+80, (br_word_t)0x7988f8761bdc51dc);
  _br_store(h3+88, (br_word_t)0x2076995003fc77a1);
  _br_store(h3+96, (br_word_t)0x827eca0ba621315b);
  _br_store(h3+104, (br_word_t)0xe5a72bce8d63cb9f);
  _br_store(h3+112, (br_word_t)0xf68f7764c28b6f8a);
  _br_store(h3+120, (br_word_t)0x2f230063cf081517);
  _br_store(h3+128, (br_word_t)0x94506632528d6a9a);
  _br_store(h3+136, (br_word_t)0xd3cde88eeb996ca3);
  _br_store(h3+144, (br_word_t)0xc0bd38c3195c899e );
  _br_store(h3+152, (br_word_t)0xf686b3d807d01);
  started = (br_word_t)0;
  i = (br_word_t)0x500;
  while (i) {
    i = i-1;
    word = _br_load(h3+((i>>6)<<3));
    bit = (word>>((i&63)&(sizeof(br_word_t)*8-1)))&1;
    if (started) {
      bls12_Fp12_square(result, result);
    } else {
      /*skip*/
    }
    if (bit) {
      if (started) {
        bls12_Fp12_mul(result, result, base);
      } else {
        bls12_Fp12_felem_copy(result, base);
        started = (br_word_t)1;
      }
    } else {
      /*skip*/
    }
  }
  bls12_Fp12_felem_copy(out, result);
}

static void bls12_pairing(br_word_t out, br_word_t p_x, br_word_t p_y, br_word_t q_x, br_word_t q_y) {
  br_word_t tmp, gamma1_p2, gamma2_p2, w_frob_p2_c1;
  uint8_t _br_stackalloc_tmp[0x240] = {0}; tmp = (br_word_t)&_br_stackalloc_tmp;
  uint8_t _br_stackalloc_gamma1_p2[96] = {0}; gamma1_p2 = (br_word_t)&_br_stackalloc_gamma1_p2;
  uint8_t _br_stackalloc_gamma2_p2[96] = {0}; gamma2_p2 = (br_word_t)&_br_stackalloc_gamma2_p2;
  uint8_t _br_stackalloc_w_frob_p2_c1[96] = {0}; w_frob_p2_c1 = (br_word_t)&_br_stackalloc_w_frob_p2_c1;
  bls12_load_gamma1_p2(gamma1_p2);
  bls12_load_gamma2_p2(gamma2_p2);
  bls12_load_w_frob_p2_c1(w_frob_p2_c1);
  bls12_miller_loop(tmp, p_x, p_y, q_x, q_y);
  bls12_final_exp(out, tmp, gamma1_p2, gamma2_p2, w_frob_p2_c1);
}

