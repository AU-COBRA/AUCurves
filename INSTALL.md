# Installation

## Requirements

- Rocq 9.0+ (the project uses `(lang dune 3.22)` with `(using coq 0.10)`)
- OCaml ≥ 4.14, dune ≥ 3.22
- An [opam](https://opam.ocaml.org/) switch with the dependencies below

## Toolchain via opam

Create a dedicated switch and pin the Rocq stdlib + coqutil/coq-bignums versions
the build is known to track:

```sh
opam switch create aucurves --packages=ocaml-base-compiler.4.14.2
eval $(opam env)
opam install \
    coq-rocq-prover \
    coq-bignums \
    coq-coqutil \
    coq-coqprime \
    coq-compcert
```

`coq-coqutil` and `coq-coqprime` can also be picked up transitively from the
fiat-crypto submodule; explicit opam installs are simpler.

## Clone with submodules

The build depends on a vendored
[fiat-crypto](https://github.com/mit-plv/fiat-crypto) (with its own bedrock2 /
coqutil / coqprime sub-submodules) plus `rewriter`.

```sh
git clone --recursive https://github.com/AU-COBRA/AUCurves.git
cd AUCurves
git submodule update --init --recursive
```

If you already cloned without `--recursive`, run the two `submodule` commands
inside the existing checkout.

## Build

```sh
ulimit -s unlimited
export OCAMLRUNPARAM="b,l=1000000000"
dune build
```

- `ulimit -s unlimited` prevents kernel-stack overflows on heavy `Z.pow`
  computations and large recursions.
- `OCAMLRUNPARAM` flushes output for live progress and lifts the native
  compiler's stack limit (otherwise dune retries silently).
- For very memory-heavy files (e.g. `BignumShift`, `Secp256k1_G1_Add_Spec`),
  use `dune build -j 1` to avoid exhausting RAM.
- Only one `dune build` can hold `_build/.lock` at a time.

## Build a single target

```sh
dune build src/Bedrock/End2End/Ed25519/Sign.vo
```

## Notes

- The native compiler is required for several heavy proofs; do not disable it
  globally. Per-file overrides exist where needed.
- The submodule pin for fiat-crypto includes `rewriter` and a sub-submodule
  layout; downstream consumers should track the AUCurves pointer rather than
  pulling fiat-crypto master directly.
