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
| secp256k1 Fp     |               2.28 µs  | `k256` Fermat addition chain                            | **3.3×** faster (7.54 µs)     |
| P-256 Fp         |               1.86 µs  | RustCrypto Fermat chain                                 | **4.0×** faster (7.53 µs)     |
| P-384 Fp         |               2.87 µs  | RustCrypto Fermat chain                                 | **24.5×** faster (70.35 µs)   |
| Pallas Fp        |               1.59 µs  | `pasta_curves` Fermat chain (`pow_vartime` over public p−2) | **6.5×** faster (10.28 µs) |
| Vesta Fq         |               1.45 µs  | `pasta_curves` Fermat chain (`pow_vartime` over public p−2) | **6.5×** faster (9.51 µs)  |
| BLS12-381 Fp     |               2.64 µs  | `blst` hand-tuned x86_64 assembly                       | 0.88×  (blst: 2.33 µs)        |
| BLS12-381 Fp     |               same     | `blst` classical Euclidean                              | 0.89×  (2.36 µs)              |
| BN254 Fp         |               1.39 µs  | (no CT reference installed)                             | —                             |
| BLS12-377 Fp     |               2.58 µs  | (no CT reference installed)                             | —                             |
| BLS24-509 Fp     |               3.51 µs  | (no CT reference installed)                             | —                             |
| BW6-761 Fp       |               5.85 µs  | (no CT reference installed)                             | —                             |

The four `_noref` rows have no constant-time reference impl in any
pure-Rust crate we could install:

- **BN254 / BLS12-377 / BW6-761**: the only widely-used Rust impls are in
  arkworks (`ark-{bn254,bls12-377,bw6-761}`), which uses BEA (Algorithm
  16 GKPP, `ark-ff/montgomery_backend.rs:295`) — data-dependent
  `while u.is_even()` loops, NOT constant-time. Excluded per the
  CT-only policy.
- **BLS24-509**: no mature pure-Rust impl exists at all (no `ark-bls24-509`
  on crates.io as of 2026-05).
- `blst` covers BLS12-381 only.

These rows nevertheless usefully measure how OUR safegcd scales across
prime sizes: 254 → 377 → 509 → 761 bits at 4/6/8/12 saturated u64
limbs.

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
