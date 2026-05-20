# `bls12-377-safe-rust` — extraction pending

BLS12-377 base field Fp + pairing tower

## Why this crate is empty

Needs Rocq extraction of the full Fp2/Fp6/Fp12 pairing tower (see bn256-safe-rust for the pattern).

## Verified Rocq components already in tree

- `src/Bedrock/Field/Synthesis/Examples/BLS12_377_FpInv.v + BLS12_377_FpInv_closed.v + BLS12_377_InvertBoundInstantiation.v` — the bedrock2-WP
  proofs of the field operations.
- `src/Arithmetic/safegcd/divsteps_bls12_377.v` and
  `divsteps_bls12_377_half.v` — Bernstein-Yang convergence
  certificates.
- `curve25519-jasmin-rs/src/safegcd_bls12_377.rs` — constant-time
  inverse, instantiated from the const-generic Signed62<N> core.

## To turn this skeleton into a real crate

1. Run the bedrock2 → Rust extraction over the field-op specs in the
   `.v` files above to produce a `generated/bls12_377_safe_tower.rs`.
2. Write a hand-tuned `src/stubs.rs` with the prime constants P,
   N_PRIME, R2, MONT_ONE, P_MINUS_2 in the curve's limb layout.
3. Wire `src/lib.rs` to `pub use` the generated tower entry points.
4. Add KAT tests cross-checking against a known reference implementation.

See `bn256-safe-rust/` for the smallest exemplar (no pairing tower,
no Jasmin leaves — just Rust Montgomery field arithmetic).
