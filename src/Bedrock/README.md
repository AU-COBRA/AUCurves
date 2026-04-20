# src/Bedrock

Bedrock2 weakest-precondition (WP) proofs for cryptographic operations.
Each file proves that a bedrock2 function satisfies its `spec_of` predicate
using separation logic.

## Subdirectories

| Directory | Contents |
|-----------|----------|
| `Field/` | Field operation specs and fiat-crypto synthesis pipeline |
| `Field/Synthesis/Examples/` | Per-curve synthesized field ops: `BLS12_*.v`, `BN254_*.v`, `BN256_*.v`, `BN446_*.v`, `BLS24_509_*.v`, `bw6_761_*.v`, etc. |
| `Field/FieldExtensions/` | Tower field (Fp2, Fp6, Fp12) operation specs |
| `Field/PairingTheory/` | Miller loop and final exponentiation WP proofs |
| `Curve/` | G1/G2 point addition WP proofs for each curve |
| `Group/` | Group operation helpers (store-point-at-infinity, zero checks) |
| `Arithmetic/` | Arithmetic helpers used across curve proofs |
| `Spec/` | `spec_of` predicate definitions shared across multiple proofs |
| `Specs/` | Additional spec definitions |
| `Jasmin/` | Jasmin bridge: connects bedrock2 `exec` to Jasmin `psem.sem` |
| `Util/` | Separation logic utilities (ecancel fast, word lemmas) |

## Key top-level files

| File | What |
|------|------|
| `BLS12_MSM.v` | Multi-scalar multiplication WP proof (L2–L5 composition) |
| `BLS12_MSM_Extract.v` | OCaml extraction of the MSM implementation |
| `BLS12_PairingRustConcrete.v` | Concrete safe-Rust extraction for BLS12-381 pairing |
| `IteratedSepPoints.v` | Sep-logic library for bucket arrays used in MSM |
| `FrameLocalsWP.v` | Frame-locals helper for L5 composition |

## Curve naming convention

Files follow the pattern `<Curve>Curve_<Group>_<Role>.v`:
- `BLS12Curve_G1.v` — G1 add bedrock2 function + WP proof
- `BLS12Curve_G1_BignumSpecs.v` — bignum-level spec (limb arrays)
- `BLS12Curve_G1_WiredSpecs.v` — wired spec (fiat-crypto field elements)

Curves: `BLS12`, `BLS12_377`, `BN254`, `BN256`, `BN446`, `BW6_761`, `Pallas`, `Vesta`, `P256`, `Secp256k1`.
