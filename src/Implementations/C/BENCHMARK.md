# BLS12-381 Pairing Benchmark: fiat-crypto vs blst

**Date**: 2026-03-26
**Platform**: x86-64 Linux (gcc -O3 -march=native -flto)
**Source**: `bench_full_vs_blst.c`

## Setup

| Component | fiat-crypto | blst 0.3.16 |
|-----------|------------|-------------|
| Fp mul/sqr | CryptOpt x86-64 asm (verified equiv.) | Hand-tuned x86-64 asm |
| Fp add/sub | bedrock2-extracted C | Hand-tuned x86-64 asm |
| Fp2 mul | Karatsuba (3 Fp muls, verified) | Karatsuba (3 Fp muls) |
| Fp2 square | Complex squaring (2 Fp muls) | Complex squaring (2 Fp muls) |
| Fp inv | Bernstein-Yang divstep (verified bridge+certificate) | Assembly |
| Fp6/Fp12 | bedrock2-extracted tower (Karatsuba, Chung-Hasan) | Hand-tuned asm |
| Miller loop | **Affine coordinates** (Fp2_inv in loop) | **Projective** (no inversions) |
| Final exp | **Naive square-and-multiply** (1280-bit exp) | **Devegili-Scott-Dahab** decomposition |

## Results

### Fp (384-bit Montgomery)

| Operation | fiat (ns) | blst (ns) | Ratio |
|-----------|----------|----------|-------|
| Fp mul | 46.4 | 25.6 | 1.81x |
| Fp sqr | 45.3 | 25.0 | 1.81x |
| Fp add | 5.8 | 2.8 | 2.07x |
| Fp sub | 4.9 | 2.8 | 1.75x |

### Fp2

| Operation | fiat (ns) | blst (ns) | Ratio |
|-----------|----------|----------|-------|
| Fp2 mul | 177.5 | 75.2 | 2.36x |
| Fp2 sqr | 111.3 | 58.9 | 1.89x |
| Fp2 add | 12.2 | 5.1 | 2.39x |
| Fp2 sub | 9.8 | 5.0 | 1.96x |
| Fp2 inv | 37,282 | -- | -- |

### Fp6

| Operation | fiat (ns) |
|-----------|----------|
| Fp6 mul | 1,243 |
| Fp6 sqr | 861 |

### Fp12

| Operation | fiat (ns) | blst (ns) | Ratio |
|-----------|----------|----------|-------|
| Fp12 mul | 4,175 | 1,450 | 2.88x |
| Fp12 sqr | 3,137 | 1,107 | 2.83x |
| Fp12 inv | 44,791 | 4,497 | 9.96x |

### Pairing

| Operation | fiat (ns) | blst (ns) | Ratio |
|-----------|----------|----------|-------|
| Miller loop | 3,222,561 | 195,024 | **16.5x** |
| Final exp | 6,772,434 | 256,980 | **26.3x** |
| Full pairing | 9,774,360 | 441,067 | **22.2x** |

## Analysis

### Optimizations Already Integrated

1. **CryptOpt Fp assembly** (WS7): Closes Fp mul gap from 2.3x (pure C) to 1.8x.
   Formally verified equivalence to bedrock2 output.

2. **Karatsuba Fp2_mul** (WS3): 3 Fp muls instead of 4.
   Verified in `QuadraticFieldExtensions.v`.

3. **Complex Fp2_square**: (a+bi)^2 = (a+b)(a-b) + 2abi.
   2 Fp muls instead of 3 (naive Fp2_mul(x,x)).

4. **Bernstein-Yang divstep Fp inversion** (WS2b/WS2c): Constant-time,
   1101 iterations. Verified bridge + O'Connor certificate.

5. **Chung-Hasan Fp6_square**: 3 Fp2_sqr + 2 Fp2_mul (vs 6 Fp2_mul from naive).

### Remaining Gaps

#### Gap 1: Fp-level (1.8x) -- Inherent

CryptOpt auto-generates x86-64 assembly via stochastic search.
blst uses expert hand-tuned assembly with optimal register scheduling.
The 1.8x gap is a fundamental code quality difference. Narrowing this
further requires either improving CryptOpt or hand-tuning assembly.

#### Gap 2: Tower overhead (1.8x -> 2.4x -> 2.9x)

Each tower level adds overhead from:
- `br_word_t` pointer indirection (bedrock2 passes `uintptr_t`, not arrays)
- Defensive input copying (`felem_copy` at every function entry)
- Stack allocation with zero-initialization (`uint8_t[N] = {0}`)
- No cross-function inlining (functions are separate `static` definitions)

This compounds: Fp=1.8x, Fp2=2.4x, Fp12=2.9x.

#### Gap 3: Miller loop (16.5x) -- Algorithmic

The bedrock2-extracted Miller loop uses **affine coordinates**, requiring
an Fp2 field inversion (37us each) at every double and add step. With
x = 0xd201000000010000 (63 doubles, ~6 adds), this means ~69 Fp2_inv
calls = **2.57ms** of pure inversion cost.

blst uses **projective coordinates**: zero inversions during the loop,
single batch inversion at the end.

Fix: Implement projective Miller loop in Rocq/bedrock2.

#### Gap 4: Final exponentiation (26.3x) -- Algorithmic

The current implementation uses naive square-and-multiply over the
hard-part exponent h3 (1280 bits, i = 0x500). This performs ~1280
Fp12_sqr + ~640 Fp12_mul = ~1920 Fp12 operations.

blst uses the **Devegili-Scott-Dahab** decomposition:
  f^((p^12-1)/r) = f^((p^6-1)(p^2+1)) * f^(hard_part)
where hard_part is expressed via the curve parameter x and Frobenius
maps, reducing to ~30 Fp12 operations total.

Fix: Implement optimized final exp decomposition in Rocq/bedrock2.

### Projected Performance After Algorithmic Fixes

Assuming the tower overhead ratio (~2.9x) applies uniformly:

| Operation | Projected fiat (ns) | blst (ns) | Projected ratio |
|-----------|-------------------|----------|----------------|
| Miller loop | ~566,000 | 195,024 | ~2.9x |
| Final exp | ~745,000 | 256,980 | ~2.9x |
| Full pairing | ~1,280,000 | 441,067 | **~2.9x** |

This would bring the full pairing from 22x down to ~3x -- competitive
for formally verified code vs hand-tuned assembly.

## After Algorithmic Optimizations (2026-03-26)

Two C-level optimizations implemented in `bls12_optimized.c`:

### DSD Final Exponentiation

Hayashida-Hayasaka-Teruya (2020) decomposition of the hard part:
4 `exp_by_x` calls (63 sqr + 6 mul each) + 3 Frobenius + 8 Fp12_mul.

| Operation | Baseline (ns) | DSD (ns) | blst (ns) | Improvement |
|-----------|-------------|---------|----------|-------------|
| Final exp | 6,537,159 | **955,358** | 248,732 | **6.8x** faster |

### Projective Miller Loop

Jacobian coordinates for the running point T. Zero Fp2_inv in loop body
(vs ~69 inversions in affine baseline). Mixed addition for Q (affine).

| Operation | Baseline (ns) | Projective (ns) | blst (ns) | Improvement |
|-----------|-------------|-----------------|----------|-------------|
| Miller loop | 3,061,689 | **611,148** | 187,188 | **5.0x** faster |

### Combined Results

| Operation | Baseline (ns) | Optimized (ns) | blst (ns) | Opt/blst |
|-----------|-------------|---------------|----------|----------|
| Final exp | 6,537,159 | 955,358 | 248,732 | **3.8x** |
| Miller loop | 3,061,689 | 611,148 | 187,188 | **3.3x** |
| **Full pairing** | **9,621,475** | **1,597,621** | **435,743** | **3.7x** |

**Overall: 22x → 3.7x blst (6x speedup).**

### Further Optimization Opportunities

1. **Cyclotomic squaring** in `exp_by_x`: replace standard Fp12_sqr (3032ns)
   with Granger-Scott cyclotomic formula (~860ns). Would reduce final exp
   from 955μs to ~400μs.

2. **Sparse Fp12 multiplication** for line functions: currently uses
   full `Fp6_mul` for the sparse line. A dedicated `mul_by_024` that
   exploits the 3 zero Fp2 coefficients would save ~40%.

3. **Tower overhead reduction** (Phase 3): removing defensive copies and
   zero-initialization from bedrock2-extracted Fp6/Fp12 operations.
   Expected additional 20-30% improvement across all operations.

4. **Projective Miller line evaluation**: the current line evaluation
   formulas may not be optimal. Using the explicit formulas from
   Aranha et al. would reduce multiplications per step.

## Reproduction

```bash
cd src/Implementations/C
BLST=/path/to/blst
gcc -O3 -march=native -flto \
    -I"$BLST/bindings" \
    bench_full_vs_blst.c \
    cryptopt/fiat_bls12_381_p_mul.o \
    cryptopt/fiat_bls12_381_p_square.o \
    /path/to/libblst.a \
    -o bench_full_vs_blst
./bench_full_vs_blst
```
