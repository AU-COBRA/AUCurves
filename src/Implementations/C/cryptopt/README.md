# CryptOpt Assembly for BLS12-381

CryptOpt generates optimized x86-64 assembly for field arithmetic primitives.
This directory holds CryptOpt-generated `.asm` files for `bls12_mul` and
`bls12_square`, used as drop-in replacements for the bedrock2-extracted versions.

## Generating BLS12-381 Assembly

Clone and build CryptOpt:

```bash
git clone https://github.com/0xADE1A1DE/CryptOpt.git
cd CryptOpt
npm install
```

Generate optimized assembly for the BLS12-381 base field:

```bash
# Multiplication
./CryptOpt --curve bls12_381_p --method mul --resultDir ./results_bls12_mul

# Squaring
./CryptOpt --curve bls12_381_p --method square --resultDir ./results_bls12_sq
```

Copy the best `.asm` files (lowest ratio) into this directory:

```bash
cp results_bls12_mul/best.asm cryptopt/fiat_bls12_381_p_mul.asm
cp results_bls12_sq/best.asm  cryptopt/fiat_bls12_381_p_square.asm
```

## ABI Convention

CryptOpt assembly follows the System-V AMD64 ABI:
- `rdi` = pointer to output (6 x uint64_t)
- `rsi` = pointer to first input (6 x uint64_t)
- `rdx` = pointer to second input (6 x uint64_t, mul only)

Exported symbols:
- `fiat_bls12_381_p_mul(uint64_t out[6], const uint64_t a[6], const uint64_t b[6])`
- `fiat_bls12_381_p_square(uint64_t out[6], const uint64_t a[6])`

## Building

From the parent directory (`src/Implementations/C/`):

```bash
make bench_cryptopt
```

This assembles the `.asm` files and links them with a benchmark harness that
compares CryptOpt Fp mul/square against the bedrock2-extracted versions.

## Formal Verification

CryptOpt assembly is **formally verified** by fiat-crypto's Coq-verified
equivalence checker. The `--proof` flag (default: on) runs the checker after
optimization. The `word_by_word_montgomery` binary with `--hints-file` can
re-verify any assembly file:

```bash
./word_by_word_montgomery --no-primitives --no-wide-int --shiftr-avoid-uint1 \
  --output /dev/null --output-asm /dev/null \
  'bls12_381_p' '64' '<prime>' mul --hints-file <asm_file>
```

Exit code 0 = proof success. The final Coq theorem states the assembly
implements the same function as the fiat-crypto specification.

## Integration with Pairing Pipeline

`bls12_pairing_all.c` has been patched to use CryptOpt assembly for
`bls12_mul` and `bls12_square`. The patch replaces the gcc-compiled
function bodies with thin wrappers calling the CryptOpt symbols:

```c
extern void fiat_bls12_381_p_mul(uint64_t out[6], const uint64_t a[6], const uint64_t b[6]);
static void bls12_mul(br_word_t out0, br_word_t in0, br_word_t in1) {
  fiat_bls12_381_p_mul((uint64_t*)out0, (const uint64_t*)in0, (const uint64_t*)in1);
}
```

The unpatched baseline is preserved as `bls12_pairing_all_baseline.c`.
After re-extraction from Coq, the patch must be re-applied.

## Measured Performance (2026-03-21, AMD Ryzen 7 PRO 7840U, container)

Standalone Fp operations:
- Fp mul: 198 cycles (gcc) → 164 cycles (CryptOpt) = **-17%**
- Fp sqr: 165 cycles (gcc) → 132 cycles (CryptOpt) = **-20%**

Full pairing (best of 3):
- Baseline (gcc): ~44M cycles
- CryptOpt:       ~37M cycles = **~16% speedup**

## Re-generating Assembly

To re-run CryptOpt with more evaluations for better optimization:

```bash
cd /path/to/CryptOpt
node dist/CryptOpt.js --curve bls12_381_p --method mul --evals 100k
node dist/CryptOpt.js --curve bls12_381_p --method square --evals 100k
```

More evaluations = longer search = faster assembly. The 10k-eval results
here are a starting point; 100k+ would likely yield further improvement.

Reference: Kuepper et al. "CryptOpt: Verified Compilation with Randomized
Program Search for Cryptographic Primitives." PLDI 2023.
