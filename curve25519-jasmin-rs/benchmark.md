# Benchmarks

Hardware: Zen 4, criterion median, release profile.

## Modular inversion — OURS vs constant-time production references

The figures below come from `benches/bench_vs_production.rs`. Each row
fixes a prime field and compares this crate's safegcd divstep against
the upstream library's own constant-time inverter for the same prime.

Run:

```bash
JASMINC=$(which jasminc) cargo bench --bench bench_vs_production \
    --features 'ed25519_rustcmd dalek_leaves'
```

| Curve / field    | OURS (safegcd divstep) | Production CT reference                                | Speedup                       |
|------------------|-----------------------:|--------------------------------------------------------|------------------------------:|
| secp256k1 Fp     |               1.41 µs  | `k256` Fermat addition chain                            | **4.3×** faster (6.11 µs)     |
| P-256 Fp         |               1.42 µs  | RustCrypto Fermat chain                                 | **4.7×** faster (6.71 µs)     |
| P-384 Fp         |               2.52 µs  | RustCrypto Fermat chain                                 | **18.7×** faster (47.16 µs)   |
| Pallas Fp        |               1.40 µs  | `pasta_curves` Fermat chain (`pow_vartime` over public p−2) | **6.7×** faster (9.38 µs) |
| Vesta Fq         |               1.41 µs  | `pasta_curves` Fermat chain (`pow_vartime` over public p−2) | **6.7×** faster (9.38 µs) |
| BLS12-381 Fp     |               2.53 µs  | `blst` hand-tuned x86_64 assembly                       | 0.88×  (blst: 2.22 µs)        |
| BLS12-381 Fp     |               same     | `blst` classical Euclidean                              | 0.88×  (2.23 µs)              |
| BN254 Fp         |               1.41 µs  | (no CT reference installed)                             | —                             |

## Constant-time verification per library

All references confirmed constant-time over the secret input:

- **k256** (RustCrypto, pure-Rust secp256k1) — fixed addition chain for
  `p − 2`, no data-dependent branches.
  `arithmetic/field.rs:173–202`.
- **p256 / p384** (RustCrypto) — identical Fermat-chain pattern.
  `arithmetic/field.rs`.
- **pasta_curves** — `pow_vartime` is vartime-over-exponent; the
  exponent here is the public constant `p − 2`, so CT over the secret
  input.
  `fields/fp.rs:533`.
- **blst** — hand-tuned x86_64 + ARM64 assembly used by Ethereum-2
  staking infrastructure. CT by design.

## Libraries excluded as variable-time

- **arkworks 0.4** (`ark-{bn254, bls12-377, bls12-381}`) — uses BEA
  (Guajardo–Kumar–Paar–Pelzl Algorithm 16,
  `ark-ff/montgomery_backend.rs:295`). Data-dependent
  `while u.is_even()` loops → NOT constant-time over secret inputs.
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

## Ed25519 sign / verify

Measured on Zen 4 with `taskset -c 0`, same-process dalek baseline; see
`docs/performance-and-panic-freeness-2026-05-13.md` for the full table.

| Configuration                                                  |   Sign |  Verify | vs dalek (sign) |
|----------------------------------------------------------------|-------:|--------:|----------------:|
| `curve25519-dalek` upstream                                    | 13.4 µs | 22.3 µs | 1.0×            |
| `wnaf_comb_leaves + tfp25519_limbs + xyzt_limb_abi` (headline) | 29.8 µs | 103 µs  | 2.2×            |
| `+ verify_projective_eq`                                       | 29.8 µs | ~82 µs  | 2.2×            |

X25519 (DH), SHA-256/512, HMAC, HKDF, and ML-KEM-768 stay within a few
percent of the best hand-tuned implementations on the same hardware.
