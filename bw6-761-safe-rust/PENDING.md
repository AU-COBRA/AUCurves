# `bw6-761-safe-rust` — extraction pending

BW6-761 base field Fp + pairing tower

## Why this crate is empty

Needs Rocq extraction of the full Fp3/Fp6 pairing tower.

## Verified Rocq components already in tree

- `src/Bedrock/Field/Synthesis/Examples/BW6_761_FpInv.v + BW6_761_FpInv_closed.v + BW6_761_InvertBoundInstantiation.v` — the bedrock2-WP
  proofs of the field operations.
- `src/Arithmetic/safegcd/divsteps_bw6_761.v` and
  `divsteps_bw6_761_half.v` — Bernstein-Yang convergence
  certificates.
- `curve25519-jasmin-rs/src/safegcd_bw6_761.rs` — constant-time
  inverse, instantiated from the const-generic Signed62<N> core.

## To turn this skeleton into a real crate

1. Run the bedrock2 → Rust extraction over the field-op specs in the
   `.v` files above to produce a `generated/bw6_761_safe_tower.rs`.
2. Write a hand-tuned `src/stubs.rs` with the prime constants P,
   N_PRIME, R2, MONT_ONE, P_MINUS_2 in the curve's limb layout.
3. Wire `src/lib.rs` to `pub use` the generated tower entry points.
4. Add KAT tests cross-checking against a known reference implementation.

See `bn256-safe-rust/` for the smallest exemplar (no pairing tower,
no Jasmin leaves — just Rust Montgomery field arithmetic).
