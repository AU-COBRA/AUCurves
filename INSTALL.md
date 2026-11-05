# Installation

## Requirements

- Rocq 9.2.0 on OCaml 5.2.0, with `rocq-native`: several proofs use `native_compute`, which Rocq
  supports on OCaml 5 from 9.2.0 on, and `src/Bedrock` and `src/Theory` build with `(mode native)`.
- dune 3.22 or later (`(lang dune 3.22)`, `(using coq 0.10)`); checked with 3.23.1.
- About 16 GB of memory for a full build at `-j2`; some files need 4 to 9 GB each.

## Toolchain via opam

The versions below are the ones the build is checked with.

```sh
opam switch create rocq-9.2 ocaml-base-compiler.5.2.0
eval $(opam env --switch=rocq-9.2 --set-switch)
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install rocq-native.2          # before any Rocq package, so that libraries get native code
opam install dune.3.23.1 rocq-core.9.2.0 rocq-stdlib.9.2.0 rocq-bignums rocq-coqprime.1.9.0 \
  coq-coqutil.0.0.7 coq-bedrock2.0.0.9 coq-rupicola.0.0.11 coq-ext-lib coq-paco coq-itree \
  rocq-mathcomp-ssreflect.2.6.0 rocq-mathcomp-algebra.2.6.0 coq-mathcomp-word.3.5
```

coq-rewriter 0.0.21 needs the patch `patches/coq-rewriter-0.0.21-rocq92.patch`: it builds the library
with native code and disables `NativeCompute Profiling` in four performance tests, which otherwise
start `perf record`.

```sh
git clone --branch v0.0.21 https://github.com/mit-plv/rewriter /tmp/rewriter
git -C /tmp/rewriter apply "$PWD/patches/coq-rewriter-0.0.21-rocq92.patch"   # from the AUCurves checkout
opam pin add coq-rewriter.0.0.21 /tmp/rewriter --kind=path
```

`src/Jasmin` needs Jasmin's Rocq library at commit `294b46e` with the four upstream commits in
`patches/jasmin/`, without `lang/extraction.v`, which hits a Rocq 9.2 extraction anomaly (fixed in
Rocq 9.3, rocq#21757):

```sh
AUCURVES=$PWD
git clone https://github.com/jasmin-lang/jasmin /tmp/jasmin
cd /tmp/jasmin && git checkout 294b46e && git am "$AUCURVES"/patches/jasmin/*.patch
cd proofs
VF="$(grep '\.v$' _CoqProject | grep -vx lang/extraction.v | tr '\n' ' ')"
rocq makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq VFILES="$VF" && make -f Makefile.coq install VFILES="$VF"
cd "$AUCURVES"
```

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
- `src/Bedrock/Field/Synthesis/Examples/bw6_761_prime_ops.v` runs fiat-crypto's synthesis pipeline on a
  12-limb prime and takes hours. Only `BW6_761_Extract.v`, `ExtractSafeTowerBW6_761.v` and
  `src/Jasmin/extractions/BW6_761.v` import it, so building `src/Bedrock` without those three targets
  avoids it; a plain `dune build` includes it.
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
