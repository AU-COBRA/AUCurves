# Benchmarks

Hardware: Zen 4, criterion median, release profile.

## Group operations and pairings

Zen 4 (Ryzen 7 PRO 7840U), pinned to one core, `[profile.release]` with
`lto = "fat", codegen-units = 1`.  Figures are **invariant-TSC reference
cycles** (`constant_tsc` + `nonstop_tsc`), not retired core cycles: a
true core-cycle count needs `perf_event_open`, and `perf_event_paranoid`
is 4 on this host.  Every comparison runs both arms in one process,
interleaved round by round, and reports each row's round minimum, so a
load spike hits both arms and the minimum discards the rounds it hit.
Ratio is ours / theirs, so below 1.00 means this project is faster.

### NIST curves against RustCrypto

Both arms use the a = -3 RCB Algorithm 4 / Algorithm 6 formulas over the
same Montgomery representation, and both scalar multiplications are
constant time with a 4-bit window.

| Curve | Operation | Ours | RustCrypto | Ratio |
|---|---|---:|---:|---:|
| P-256 | `g1_add`    |    909–951 |    831–854 | 1.09–1.11x |
| P-256 | `g1_double` |    826–844 |    765–783 | 1.08x |
| P-256 | scalar mul  | 282k–286k | 265k–269k | 1.06x |
| P-384 | `g1_add`    |  1957–1980 |  2650–2689 | **0.74x** |
| P-384 | `g1_double` |  1728–1760 |  2353–2412 | **0.72–0.73x** |
| P-384 | scalar mul  |  876k–884k |      1.19M | **0.74x** |

P-224 and secp256k1 have no comparable production arm.  P-224: `fp_mul`
60.9, `g1_add` 1031, `g1_double` 967, scalar mul 287k, fixed-base 51.3k.
Field multiplication and squaring on P-224/P-256/P-384 and secp256k1 use
CryptOpt assembly, verbatim from seeds CryptOpt equivalence-checked
against fiat-crypto, with a per-crate differential test and a fiat
fallback when the host lacks BMI2/ADX.

### Pairing curves

| Curve | Operation | Ours | blst 0.3 | arkworks 0.5 |
|---|---|---:|---:|---:|
| BLS12-381 | Fp mul      |  128.6 |  107.1 |  106.0 |
| BLS12-381 | Miller loop | 1.906M | 0.624M |      — |
| BLS12-381 | Pairing     | 4.556M | 1.458M | 2.695M |
| BN254     | Fp mul      |   74.5 |      — |   51.0 |
| BN254     | Fp2 mul     |    261 |      — |    197 |
| BN254     | Fp12 mul    |   7970 |      — |   6129 |
| BN254     | Miller loop | 1.482M |      — | 0.526M |
| BN254     | Pairing     |  3.52M |      — |  1.66M |

BLS12-381 is 3.12x blst and 1.69x arkworks on a full pairing; BN254 is
2.13x arkworks.  Where that gap sits depends on which metric is asked.
In cycles BN254's Fp multiply is 1.46x, Fp2 1.32x and Fp12 1.30x.  In
INSTRUCTIONS the Fp multiply is 0.96x -- our leaf issues slightly fewer
instructions than arkworks -- so that row is not extra work but lower
throughput: 3.83 instructions per reference cycle against arkworks'
5.82.  The same measurement puts six other rows across P-256, P-384 and
the BN254 pairing at an instruction-to-cycle ratio of 0.89-0.92, i.e.
this project's generated code consistently retires about 10% fewer
instructions per cycle than the hand-written references.  Read the
cycle ratios as what the machine does and the instruction ratios as
what the algorithm costs; see the iai-callgrind benches for the latter.

A note on measuring a field multiply against arkworks.  Our `fp_mul` is
an out-parameter API, `fp_mul(&mut out, &a, &b)`, and writes through
memory by construction; arkworks' `a * b` returns by value and can stay
in registers.  Passing the arkworks operands through `black_box` *by
value* moves them across the barrier and spills them, adding a
23-cycle store-forward per iteration that our arm pays anyway — which
makes the two look level at 1.02x.  Taking the barrier by reference
gives 1.46-1.53x, and that is the figure quoted above.  Matching the
syntax of two arms does not match their instruction budget.

BN254's `fp2_inv` is 4208 cycles, 23.3% of the Miller loop over its 80
steps.

### BW6-761 G1

Projective coordinates replace affine, so a scalar multiplication
performs one inversion rather than one per bit; the Bernstein-Yang
inverse costs 23.8x a multiply here.  The doubling is RCB 2015
Algorithm 9, emitted from the Rocq derivation in
`src/Bedrock/Curve/CurveDoubleA0RustCmd.v`.

| Operation | Affine | Algorithm 7 | Algorithm 9 (emitted) |
|---|---:|---:|---:|
| doubling    | 22327 | 11902 | **7656** |
| addition    | 21989 | 12363 | — |
| scalar mul  | 13.59M | 7.33M | **5.70M** |

Field leaves: `fp_mul` 788, `fp_square` 656, `fp_inv` 18803.  The
emitted Algorithm 9 body is 1.012x faster than the hand transcription it
replaced and 1.616x faster than reusing the addition, so only the
emitted body ships.

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
