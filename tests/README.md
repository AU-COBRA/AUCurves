# Cross-check harness

These scripts generate per-curve Rust examples that exercise pairing
multilinearity (`e(k*P, Q) == e(P, Q)^k` for several `k`) on top of the
safe-Rust crates. Multilinearity is a much stronger end-to-end check than
the simple `k=2` bilinearity test, while remaining cheap to compute.

## Files

```
generate_bn254_multilin.py        → bn254-safe-rust/examples/multilin_test.rs
generate_bls12_381_multilin.py    → bls12-381-safe-rust/examples/multilin_test.rs
run_all.sh                        — regenerate all + run all
```

## Why a generator instead of a fixed test

The Rust example needs the precomputed `k*G1` coordinates in Montgomery
form. Embedding a curve-arithmetic implementation in Rust just for the
test would defeat the purpose; embedding a Python script lets the trusted
"reference" stay in 50 lines of straightforward arithmetic.

## Regenerating after a curve-data change

```
python3 tests/generate_bn254_multilin.py
python3 tests/generate_bls12_381_multilin.py
```

then commit the updated `examples/multilin_test.rs` files. The generated
files have a `DO NOT EDIT BY HAND` header so accidental edits stand out
on review.

## Running the tests

```
sh tests/run_all.sh
```

or per-crate:

```
( cd bn254-safe-rust && cargo run --release --example multilin_test )
( cd bls12-381-safe-rust && cargo run --release --example multilin_test )
```

## What this does NOT cover

- Cross-basis comparison against py_ecc / arkworks. Multilinearity is a
  property of any homomorphism `G1 -> Fp12*` and would still hold for a
  *wrong* but homomorphism-preserving implementation. To rule that out we
  would need a basis-change isomorphism into py_ecc's Fp12 representation
  and a literal value comparison; not yet implemented.
- Non-degeneracy. We never check that the result is not 1.
- The G2 pairing argument is fixed. Bilinearity in the second argument is
  not exercised.
