# AUCurves

Rocq verification of elliptic curve cryptography using the
[fiat-crypto](https://github.com/mit-plv/fiat-crypto) /
[bedrock2](https://github.com/mit-plv/bedrock2) /
[Rupicola](https://github.com/mit-plv/rupicola) stack, with
[Jasmin](https://github.com/jasmin-lang/jasmin) as a verified-assembly
back-end for the curve leaves.

## What is verified

Pairing-friendly curves paper:

- **Pairing curves**: BLS12-381, BLS12-377, BN254, BN256, BN446, BLS24-509, BW6-761
- **General-purpose curves**: P-224, P-256, P-384, P-521, secp256k1, Pallas, Vesta (Pasta), Curve25519
- **Operations**: G1/G2 point addition, scalar multiplication (GLV, wNAF), Miller loop, final exponentiation, constant-time modular inversion
- **Hash-to-curve**: G1 and G2 (SWU + isogeny), SHAKE-256 via verified Keccak

Commitments paper (built on the pairings above):

- Pedersen-KZG correctness, evaluation binding, polynomial binding, hiding
- Schnorr / linear special-soundness layer
- Multi-scalar multiplication (MSM)
- bedrock2 → safe-Rust extraction pipeline (BLS12-381, BN254, BN256, BN446)
- bedrock2 → Jasmin extraction backend

Signal-messenger paper:

- Curve25519 / Ed25519 / XEdDSA, Ristretto255, ML-KEM-768, SHA-2 family
- Protocol composition (X3DH, PQXDH, Double Ratchet, Sender Keys, SPQR)

## Directory structure

```
src/                       Rocq proofs (see breakdown below)
curve25519-jasmin-rs/      Rust runtime for the Signal stack; also hosts the
                           Bernstein–Yang divstep port for all 14 verified primes
                           as safegcd_<curve>.rs modules
Signal/                    Sigma-protocol theories (Lizard, LinearSigma, Poksho)

# Pairing curves (full field + Fp2/Fp6/Fp12 + Miller loop)
bls12-381-safe-rust/       Packaged crate
bn254-safe-rust/           Packaged crate
bn256-safe-rust/           Packaged crate
bn446-safe-rust/           Packaged crate
bls12-377-safe-rust/       SKELETON — extraction of pairing tower pending
bls24-509-safe-rust/       SKELETON — extraction of pairing tower pending
bw6-761-safe-rust/         SKELETON — extraction of pairing tower pending

# Non-pairing curves (field ops via fiat-rust + safegcd CT inverse)
p224-safe-rust/            fiat-rust wrapper, KAT tested
p256-safe-rust/            fiat-rust wrapper, KAT tested
p384-safe-rust/            fiat-rust wrapper, KAT tested
p521-safe-rust/            fiat-rust wrapper (Solinas form), KAT tested
secp256k1-safe-rust/       fiat-rust wrapper, KAT tested
pallas-safe-rust/          SKELETON — Pasta primes not yet in fiat-rust
vesta-safe-rust/           SKELETON — Pasta primes not yet in fiat-rust

src/
├── Arithmetic/       Field arithmetic helpers (safegcd divstep certificate)
├── Bedrock/          Bedrock2 WP proofs (see src/Bedrock/README.md)
├── End2End/          End-to-end pipelines (X25519, XEdDSA, Ristretto, Rupicola)
├── Hacspec/          Hacspec equivalence proofs for G1/G2
├── Implementations/  C / CryptOpt reference implementations
├── Jasmin/           Jasmin bridge: bedrock2 → psem semantics
├── Spec/             High-level specifications (pairing, hash-to-curve, XEdDSA)
└── Theory/           Mathematical foundations (see src/Theory/README.md)
```

Crate status:

- **Packaged**: BLS12-381, BN254, BN256, BN446 ship full field + pairing
  tower + Miller loop. See each crate's `README.md` for the public API.
- **fiat-rust wrappers**: P-224, P-256, P-384, P-521, secp256k1 are
  thin wrappers around the auto-generated `fiat-crypto/fiat-rust`
  crate (Montgomery for P-224/256/384/secp256k1, Solinas for P-521),
  with constant-time inversion re-exported from
  `curve25519-jasmin-rs/src/safegcd_<curve>.rs`.  KAT tests pass.
- **Skeletons**: BLS12-377, BLS24-509, BW6-761 (pairing-tower
  extraction pending), Pallas, Vesta (Pasta primes not yet in
  fiat-rust).  Each carries a `PENDING.md` listing the verified Rocq
  components already in tree and the concrete steps to turn the
  skeleton into a real crate.  The Bernstein–Yang constant-time
  inversion is the exception: it ships for all 14 primes as
  `safegcd_<curve>.rs` modules inside `curve25519-jasmin-rs/`.

The scaffolder lives at `scripts/scaffold_safe_rust.sh` — re-run it to
regenerate any of the wrapper / skeleton crates from their templates.

## Building

Requires Rocq 9 with the fiat-crypto and bedrock2 dependencies.
Clone with `--recursive` to get the fiat-crypto submodule.

```bash
ulimit -s unlimited
export OCAMLRUNPARAM="b,l=1000000000"
dune build
```

Only one `dune build` can hold `_build/.lock` at a time.
For heavy files use `-j 1` to avoid memory exhaustion.

## Papers

Published:

- Rasmus Holdsbjerg-Larsen, Bas Spitters, Mikkel Milo, [A Verified Pipeline from a Specification Language to Optimized Safe Rust](https://popl22.sigplan.org/details/CoqPL-2022-papers/5/A-Verified-Pipeline-from-a-Specification-Language-to-Optimized-Safe-Rust), CoqPL 2022

In preparation:

- Diego Aranha, Rasmus Holdsbjerg-Larsen, Benjamin Salling Hvass, Bas Spitters,
  *Synthesizing High-Assurance Implementations of Pairing Groups*. Verified
  synthesis of pairing-friendly curves (BLS12-381, BLS12-377, BN254, BN256,
  BN446, BLS24-509, BW6-761): G1/G2 group operations, scalar multiplication
  (GLV, wNAF), Miller loop, final exponentiation, hash-to-curve.
- *Verified cryptographic commitments* — Pedersen-KZG correctness, evaluation
  binding, polynomial binding, hiding, and a Schnorr / linear special-soundness
  layer, built on the pairings paper. Includes multi-scalar multiplication
  (MSM), the bedrock2 → safe-Rust extraction pipeline (BLS12-381, BN254,
  BN256, BN446), and the bedrock2 → Jasmin backend — i.e. the deployable
  production stack for shipping commitments.
- *Verified cryptography for the Signal messenger* — the primitives Signal
  needs (X25519, Ed25519/XEdDSA, Ristretto255, ML-KEM-768, SHA-2 family)
  and the protocol composition (X3DH, PQXDH, Double Ratchet, Sender Keys,
  SPQR) on top of the verified core. Mirrors how `curve25519-dalek` already
  builds on fiat-crypto, providing verified replacements for the remaining
  unverified surface (group operations, scalar arithmetic, protocol glue).
  The production Rust runtime lives in `curve25519-jasmin-rs/`; the
  Sigma-protocol theories used by zkgroup live in `Signal/`.
