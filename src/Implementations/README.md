# src/Implementations

Reference and benchmark implementations used alongside the verified pipeline.

## Subdirectories

### `C/`

C implementations of BLS12-381 operations for benchmarking and cross-checking.

| File / dir | Contents |
|------------|----------|
| `BLS12Curve_G1.c` / `G2.c` | G1/G2 point addition (bedrock2-extracted C) |
| `bls12_pairing_all.c` | Full pairing pipeline |
| `bls12_pairing_all_cryptopt.c` | Pairing with CryptOpt-optimized Fp mul |
| `bls12_optimized.c` | Optimized variant |
| `bench_pairing*.c` | Benchmarks vs blst |
| `G1_scalarmult.c` | G1 scalar multiplication |
| `cryptopt/` | CryptOpt-generated field multiplication routines |
| `BENCHMARK.md` | Benchmark results and methodology |

### `Rust/`

`BLS12_Curves.rs` — Rust bindings to the bedrock2-extracted BLS12-381 curve
operations, used in the safe-Rust extraction pipeline.

### `SOS/`

Sum-of-squares (SOS) multiplication: an alternative field multiplication
strategy explored for performance.

| File | Contents |
|------|----------|
| `SOSMul.v` | Rocq specification and proof of SOS multiplication |
| `SOSReduction.v` | Reduction correctness proof |
| `lazyreductiontest.c` | C prototype and benchmarks |
