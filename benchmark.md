# Benchmarks

Hardware: Zen 4, criterion median, release profile.

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

The four `_noref` rows have no CT reference impl available in any
pure-Rust crate we could install: arkworks (`ark-{bn254,bls12-377,
bw6-761}`) is variable-time (BEA), `ark-bls24-509` does not exist,
and `blst` covers BLS12-381 only. These rows still serve to measure
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
| BLS12-381 | Pairing (full) | 1.95 ms | Projective Miller loop, gnark final-exp port, constant-time scalar mul. |
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
