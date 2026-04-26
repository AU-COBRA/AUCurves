# `coqnative_walk.sh` — fixed-point native artifact populator

Walk every `.vo` in `_build/default/fiat-crypto/src/` (or the opam Rewriter
dir, in `coqnative_walk_opam.sh`) and run `coqnative` on each in dependency
order. Re-runs failed ones each round; converges in 6-8 rounds.

## Why it exists

`make_computed_op` (and the fiat-crypto pipeline more broadly) calls
`native_compute`, which on rocq-9 with `dune (mode vo)` builds `.cmxs`
files on demand. Without persistent `.cmxs`, every `make_computed_op`
invocation pays the full cascade-build cost (~5-15 min just for the dep
load + ocamlopt invocations).

**Caveat**: `dune` purges `.coq-native/` from `_build/` between
unrelated builds. The cache is **not durable** — it has to be re-run
before each heavy build that benefits from it. See
`$CLAUDE_CONFIG/projects/.../memory/feedback_wbw_synthesis_slow_first_build.md`.

## Usage

```bash
cd $WORKSPACE/AUCurves
./scripts/coqnative_walk.sh                    # populates _build/default/fiat-crypto/src/.../*.cmxs
./scripts/coqnative_walk_opam.sh               # populates opam Rewriter .cmxs (bigger one-time cost)
```

The opam variant must be run FIRST if the opam Rewriter package was
installed without native support (i.e. `find ~/.opam/rocq-9/lib/coq/
user-contrib/Rewriter -name '*.cmxs'` returns nothing). Without
Rewriter `.cmxs` cached, ~131 of the 577 fiat-crypto files (the
AbstractInterpretation cluster) cannot be coqnative'd at all.

## Expected output

The fiat-crypto walk on a clean `_build/`:

```
Total .vo files: 577
=== Round 1 ===  ok=374, skipped=203
=== Round 2 ===  ok= 44, skipped=159
=== Round 3 ===  ok= 20, skipped=139
=== Round 4 ===  ok=  7, skipped=132
=== Round 5 ===  ok=  1, skipped=131
... STUCK if no opam Rewriter cmxs
```

After running the opam variant first:

```
=== Round 8 ===  ok=  5, skipped=  0
DONE — all .vo files have .cmxs
Final .cmxs count: 577
Total .cmxs disk: 269M
```

## Wall-clock cost

- First-time fiat-crypto walk: ~30-60 min (mostly ocamlopt runs).
- First-time opam Rewriter walk: ~15-30 min.
- Re-runs after `_build/` purge: same as first-time (no incremental skip).
