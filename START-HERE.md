# Start Here

AUCurves verifies elliptic-curve cryptography in Rocq and extracts it to
running Rust and assembly. The proofs sit on the fiat-crypto / bedrock2 /
Rupicola stack, with [Jasmin](https://github.com/jasmin-lang/jasmin) as a
verified-assembly back-end for the field leaves.

## The work in three papers

The repository backs three papers, each building on the one before it.

1. **Pairing-friendly curves.** G1/G2 arithmetic, scalar multiplication
   (GLV, wNAF), the Miller loop, final exponentiation, and hash-to-curve
   for seven curves: BLS12-381, BLS12-377, BN254, BN256, BN446, BLS24-509,
   and BW6-761. The proofs live in `src/Spec/`, `src/Theory/`, and
   `src/Bedrock/`.

2. **Cryptographic commitments.** Pedersen-KZG (correctness, evaluation
   binding, polynomial binding, hiding), a Schnorr / linear special-soundness
   layer, multi-scalar multiplication, and the bedrock2 → safe-Rust and
   bedrock2 → Jasmin extraction pipelines. This paper builds on the pairing
   curves above.

3. **Cryptography for the Signal messenger.** Curve25519, Ed25519/XEdDSA,
   Ristretto255, ML-KEM-768, the SHA-2 family, and protocol composition
   (X3DH, PQXDH, Double Ratchet, Sender Keys, SPQR). The production runtime
   lives in `curve25519-jasmin-rs/`; the Sigma-protocol theories live in
   `Signal/`.

## What to read, in order

1. **This file** — orientation.
2. **[INSTALL.md](INSTALL.md)** — toolchain, submodules, and first build.
3. **[README.md](README.md)** — the full curve list, crate status, and
   directory map.
4. **[benchmark.md](benchmark.md)** — performance against production
   references (blst, RustCrypto, dalek, arkworks).
5. **`src/*/README.md`** — per-subtree detail for `Theory`, `Spec`,
   `Bedrock`, `Jasmin`, and the rest.

## Build in three commands

```sh
git clone --recursive https://github.com/AU-COBRA/AUCurves.git
cd AUCurves
ulimit -s unlimited && export OCAMLRUNPARAM="b,l=1000000000" && dune build
```

The build needs Rocq 9 with the fiat-crypto and bedrock2 dependencies.
[INSTALL.md](INSTALL.md) gives the full toolchain and the per-file build
notes for the heaviest proofs.

## Where the deployable artifacts are

- **Packaged Rust crates** (full field arithmetic plus the pairing tower):
  `bls12-381-safe-rust/`, `bn254-safe-rust/`, `bn256-safe-rust/`,
  `bn446-safe-rust/`.
- **fiat-rust wrappers with a constant-time inverse** for the remaining
  curves: `p256-safe-rust/`, `secp256k1-safe-rust/`, `pallas-safe-rust/`,
  and the rest.
- **Signal runtime**: `curve25519-jasmin-rs/`.

Each crate ships its own `README.md` and a set of passing known-answer tests.
