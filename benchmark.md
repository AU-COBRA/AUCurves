# Benchmarks

Hardware: Zen 4, criterion median, release profile.

## Group operations and pairings

Zen 4 (Ryzen 7 PRO 7840U), one core, `[profile.release]` with
`lto = "fat", codegen-units = 1`.  Comparison arms run in the same
process as ours, so the ratios are load-robust; absolute figures are
not.  Ratio is ours / theirs, so below 1.00 means this project is
faster.

### NIST curves against RustCrypto

Both arms use the same a = -3 RCB Algorithm 4 / Algorithm 6 formulas
over the same Montgomery representation, and both scalar
multiplications are constant time with a 4-bit window.

| Curve | Operation | Ours | RustCrypto | Ratio |
|---|---|---:|---:|---:|
| P-256 | `g1_add`    | 303.6 ns | 274.5 ns | 1.11x |
| P-256 | `g1_double` | 270.6 ns | 247.4 ns | 1.09x |
| P-256 | scalar mul (var-base) | 95.8 us | 89.8 us | 1.07x |
| P-384 | `g1_add`    | 652.2 ns | 879.1 ns | **0.74x** |
| P-384 | `g1_double` | 603.3 ns | 797.8 ns | **0.76x** |
| P-384 | scalar mul (var-base) | 374.9 us | 468.1 us | **0.80x** |

P-224 and secp256k1 have no comparable production arm.  P-224:
`fp_mul` 15.3 ns, `g1_add` 345.7 ns, `g1_double` 326.9 ns, scalar mul
149.5 us.  Field multiplication and squaring on P-224/P-256/P-384 and
secp256k1 use CryptOpt assembly, taken verbatim from seeds CryptOpt had
already equivalence-checked against fiat-crypto, with a per-crate
differential test and a fiat fallback when the host lacks BMI2/ADX.

### Pairings

| Implementation | Pairing | Reference |
|---|---:|---|
| BLS12-381, `bls12-jasmin-rs` native | 1.33 ms | blst 0.53 ms, arkworks 0.99 ms |
| BLS12-381, `bls12-381-safe-rust` | 1.99 ms | same |
| BN254, `bn254-safe-rust` | 1.24 ms | arkworks 0.57 ms (2.20x) |

BN254's field multiply is at parity with arkworks (83.2 against 80.1
invariant-TSC cycles, 1.04x), so the remaining gap is above the field
layer.

### BW6-761 G1

Projective coordinates replace affine, so a scalar multiplication
performs one inversion rather than one per bit; on this curve the
Bernstein-Yang inverse costs about 23x a multiply.  The doubling is RCB
2015 Algorithm 9, emitted from the Rocq derivation in
`src/Bedrock/Curve/CurveDoubleA0RustCmd.v`.

| Doubling route | Field ops | Cycles |
|---|---:|---:|
| Algorithm 9, Rocq-emitted | 18 (9 M) | 6818 |
| Algorithm 9, hand-written | 18 (9 M) | 6934 |
| Algorithm 7 self-addition | 33 (14 M) | 11028 |

The emitted body is 1.017x faster than the hand transcription it
replaced and 1.617x faster than reusing the addition, so the
hand-written variant was removed rather than kept alongside.

## Modular inversion — OURS vs constant-time production references

Each row fixes a prime field and compares this project's safegcd
(Bernstein–Yang divstep) port — instantiated for 14 primes via the
const-generic core in `curve25519-jasmin-rs/src/safegcd.rs` — against
the upstream library's own constant-time inverter for the same prime.

| Curve / field    | OURS (safegcd divstep) | Production CT reference                                | Speedup                       |
|------------------|-----------------------:|--------------------------------------------------------|------------------------------:|
| secp256k1 Fp     |               2.28 µs  | `k256` Fermat addition chain                            | **3.3×** faster (7.54 µs)     |
| P-256 Fp         |               1.86 µs  | RustCrypto Fermat chain                                 | **4.0×** faster (7.53 µs)     |
| P-384 Fp         |               2.87 µs  | RustCrypto Fermat chain                                 | **24.5×** faster (70.35 µs)   |
| Pallas Fp        |               1.59 µs  | `pasta_curves` Fermat chain (`pow_vartime` over public p−2) | **6.5×** faster (10.28 µs) |
| Vesta Fq         |               1.45 µs  | `pasta_curves` Fermat chain (`pow_vartime` over public p−2) | **6.5×** faster (9.51 µs)  |
| BLS12-381 Fp     |               2.64 µs  | `blst` hand-tuned x86_64 assembly                       | 0.88× (blst: 2.33 µs)         |
| BLS12-381 Fp     |               same     | `blst` classical Euclidean                              | 0.89× (2.36 µs)               |
| BN254 Fp         |               1.39 µs  | (no CT reference installed)                             | —                             |
| BLS12-377 Fp     |               2.58 µs  | (no CT reference installed)                             | —                             |
| BLS24-509 Fp     |               3.51 µs  | (no CT reference installed)                             | —                             |
| BW6-761 Fp       |               5.85 µs  | (no CT reference installed)                             | —                             |

The four `_noref` rows have no CT reference impl in any
pure-Rust crate we could install: arkworks (`ark-{bn254,bls12-377,
bw6-761}`) is variable-time (BEA), `ark-bls24-509` does not exist,
and `blst` covers BLS12-381 only. These rows still measure
how OUR safegcd scales across prime sizes: 254 → 377 → 509 → 761
bits at 4/6/8/12 saturated u64 limbs.

Run:

```bash
cd curve25519-jasmin-rs
JASMINC=$(which jasminc) cargo bench --bench bench_vs_production \
    --features 'ed25519_rustcmd dalek_leaves'
```

Bench source: `curve25519-jasmin-rs/benches/bench_vs_production.rs`.

## Constant-time verification per library

All references are constant-time over the secret input:

- **k256** (RustCrypto, pure-Rust secp256k1) — fixed addition chain for
  `p − 2`; no data-dependent branches.
  `arithmetic/field.rs:173–202`.
- **p256 / p384** (RustCrypto) — identical Fermat-chain pattern.
  `arithmetic/field.rs`.
- **pasta_curves** — `pow_vartime` is vartime-over-exponent; the
  exponent here is the public constant `p − 2`, so CT over the secret
  input.
  `fields/fp.rs:533`.
- **blst** — hand-tuned x86_64 + ARM64 assembly used by Ethereum-2
  staking infrastructure.

## Libraries excluded as variable-time

- **arkworks 0.4** (`ark-{bn254, bls12-377, bls12-381}`) — uses BEA
  (Guajardo–Kumar–Paar–Pelzl Algorithm 16,
  `ark-ff/montgomery_backend.rs:295`). Data-dependent
  `while u.is_even()` loops → not constant-time over secret inputs.
- **rust-secp256k1 0.30** — does not expose `Scalar::inverse` publicly.
- **ring 0.17** — does not expose modular inverse to users.
- **OpenSSL** `BN_mod_inverse` — variable-time.
  `BN_mod_inverse_no_branch` is misleadingly named and still varies on
  subtle paths (Bernstein–Chen–Harrison–Huang–Maxwell–Wang–Wuille–Yang,
  EUROCRYPT 2026, Table 1.2.1).
- **p224 / p521** (RustCrypto) — `FieldElement` is crate-private in
  0.13.x (no `expose-field` feature). `Scalar::invert` is at a
  different prime than our base-field divstep; omitted to keep the
  comparison fair.

## Ed25519 sign / verify (curve25519-jasmin-rs runtime)

Measured on Zen 4 with `taskset -c 0`; full table in
`curve25519-jasmin-rs/docs/performance-and-panic-freeness-2026-05-13.md`.

| Configuration                                                  |   Sign |  Verify | vs dalek (sign) |
|----------------------------------------------------------------|-------:|--------:|----------------:|
| `curve25519-dalek` upstream                                    | 13.4 µs | 22.3 µs | 1.0×            |
| `wnaf_comb_leaves + tfp25519_limbs + xyzt_limb_abi` (headline) | 29.8 µs | 103 µs  | 2.2×            |
| `+ verify_projective_eq`                                       | 29.8 µs | ~82 µs  | 2.2×            |

X25519 (DH), SHA-256/512, HMAC, HKDF, and ML-KEM-768 stay within a few
percent of the best hand-tuned implementations on the same hardware.

## Pairing throughput (`bls12-jasmin-rs`, sibling repo)

The hand-tuned Rust-native pairing crate at `BLS/bls12-jasmin-rs/`
(remote `spitters/bls12-jasmin-rs`) is the perf-leader for BLS12-381
in our ecosystem.  Distinct from `bls12-381-safe-rust/` (which is the
bedrock2 → safe-Rust full-tower extraction): `bls12-jasmin-rs`
combines hand-written G1/G2/pairing in Rust with libjade Jasmin
assembly for field leaves and Coq-extracted MSM bodies.

| Curve | Operation | This crate | Notes |
|---|---|---:|---|
| BLS12-381 | Pairing (full) | 1.33 ms | Projective Miller loop, gnark final-exp port, constant-time scalar mul. |
| BLS12-381 | G1 add | 17 ns (Jasmin asm) | Vs GCC -O3: 26 ns → 36 % faster |
| BLS12-381 | Fp mul (CryptOpt) | ~170 cyc | Vs GCC -O3: 265 cyc → 55 % faster |
| BLS12-381 | MSM (extracted) | within 1.5× of arkworks at KZG sizes | 4 c-window variants (c=5/7/9/11), cache-aware dispatch |
| BLS12-377 | Pairing (full) | 2.5 ms | DSD optimization on; 2 axioms remain. |

Relationship to the other 14 packaged crates in this workspace:
- `bls12-jasmin-rs` = perf-tuned, hand-written, with Jasmin leaves
- `bls12-381-safe-rust` = bedrock2 → safe-Rust extraction, full Coq pipeline (BridgeReal Qed)
- The two ship the same field semantics; choose `safe-rust` for the
  verified-extraction story and `jasmin-rs` for raw perf.

Source: `BLS/bls12-jasmin-rs/` (own remote at `spitters/bls12-jasmin-rs`,
intentionally NOT moved into the AUCurves workspace since it carries
its own commit history).  Benches: `bls12-jasmin-rs/examples/` +
`bls12-jasmin-rs/benches/`.
