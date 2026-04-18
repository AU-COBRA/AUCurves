# Closing the safe-Rust performance gap

**Goal:** bring the deployed `bls12-381-safe-rust` and `bn254-safe-rust`
pairing times from $\sim$4.8\,ms / $\sim$3.2\,ms (today, this dev box)
down to within $2\times$ blst (the paper's stated target, achieved on
the C-output path).

**Baseline measurements (dev box, taskset-pinned, single core):**

| Configuration                              | $\mathbb{F}_p$ mul | Pairing  |
|--------------------------------------------|--------------------|----------|
| BLS12-381 safe-Rust (CryptOpt mul + stub)  | 33.0 ns            | 4.80 ms  |
| BLS12-381 blst                             | 25.9 ns            | 0.47 ms  |
| BN254 safe-Rust (stub leaves)              | 38.9 ns            | 3.16 ms  |
| BN254 arkworks                             | 13.4 ns            | 0.46 ms  |

The BLS12-381 deployed crate already calls the DSD final-exp
(`bls12_final_exp_hard_dsd`); the gap is therefore not a missing
algorithmic optimisation but cumulative overhead from the safe-Rust
pretty printer's per-call clones.

---

## Prerequisite: fix the Jasmin gating bug (≈30 min)

The BN254 crate has `mod stubs;` unconditional in `src/lib.rs`.  When
the jasmin path is built, both stubs and the Jasmin static archive
expose `_bn254_add`, `_bn254_mul`, etc.; the linker silently picks the
Rust stubs (first in link order) and drops the Jasmin code.

**Fix.** In `src/lib.rs`:
```rust
#[cfg(not(feature = "jasmin"))] mod stubs;
```
Verify with `nm target/release/examples/bench_compare | grep _bn254_add`
before/after — the symbol's offset moves into the Jasmin object range.

Same review needed for BLS12-381's `mod stubs;` once it ships a
Jasmin path.

**Expected impact:** Fp mul drops to the Jasmin-CryptOpt number
(~25 ns equivalent); pairing improves marginally because
multiplication is already the fast path in CryptOpt mode.  Real win
is closing the 13% gap on `add`/`sub`/`opp`/`copy` to blst's
hand-tuned assembly.

---

## (b2) Copy elimination in the safe-Rust pretty printer (the big one)

**Why this is the dominant gap.**  Every multi-limb operation in the
generated tower currently issues a `let __ac = src.clone();` pre-pass
before the call, to satisfy Rust's borrow checker when the same
slot is used as input and output.  At Fp12 level that's 576 bytes per
call; the Miller loop and final-exp jointly issue dozens of such
calls.  Stacked through three tower levels, the copies dominate.

A small AST-level pass already exists at the bedrock2 level for
**componentwise** operations (add/sub/opp), and yields 22--37 percent
on those calls.  Extending it to the multiplicative path
(`Fp{2,6,12}_mul`, `_square`, `_inv`) is the engineering blocker.

### Design

1. **Lifetime analysis at AST level.**  For each call site
   `bls12_FpN_mul(out, x, y)`, decide whether `out` provably aliases
   neither `x` nor `y` *at this call site* (separation-logic
   invariant).  If yes, drop the `clone` and call a
   `*_nocopy` variant directly.

2. **Add `_nocopy` siblings.**  The generated tower already has
   some: `bls12_Fp6_add_nocopy`, `bls12_Fp12_mul_nocopy`,
   `bls12_Fp12_sub_nocopy`.  Reuse where possible; otherwise emit
   a fresh `_nocopy` variant from the bedrock2 spec.

3. **Pretty printer edit.** In `src/Bedrock/ToSafeRustBody.v`, add a
   pre-pass that walks the cmd tree, looks at each `cmd.call`, and:
   - if the destination is a fresh stackalloc'd buffer, or proven
     disjoint from both source pointers via separation-logic
     hypothesis lookup, emit the `_nocopy` form;
   - otherwise emit today's `let __ac = ...; clone();` form.

   The proof obligation is local: each `_nocopy` call carries a
   side-condition that's discharged by the existing sep-tree
   structure available in the printer's typing context (`SafeRustReflection_walker`).

4. **Soundness.** `safe_cmd_correct` (the Rocq-proved simulation
   theorem) needs an extension: a parametric "no-aliasing" hypothesis
   that the printer carries through to the call.  This adds a few
   constructor cases to `cmd_clean` and the corresponding cases to
   the simulation proof.

### Effort

- AST pass + per-call disjointness check: 1--2 days.
- Soundness proof extension: 2--4 days (the hard part is the cases
  where `out` is itself a sub-projection like `out.c0`; these
  require an extension of the freshness invariant).
- Per-curve regeneration + paper update: half day.

### Expected impact

Eliminating the Fp12-level copies alone (the most expensive: 576
bytes each, $\geq 60$ calls per pairing) could remove $\sim$80\,$\mu$s
per call on this machine, i.e.\ approaching half of the pairing time.
The paper quotes $\sim$1.5$\times$ for full elimination; observed
gap is closer to $4\times$, so this is the highest-ROI optimisation
available.

### Files touched

- `src/Bedrock/ToSafeRustBody.v` (the printer + the `param_table`
  needs `_nocopy` annotations per function)
- `src/Bedrock/SafeRustSimulation.v` (extend `safe_cmd_correct`)
- regenerate `bls12-381-safe-rust/generated/bls12_safe_tower.rs`
  and the BN254 / BN256 / BN446 siblings via the existing extraction
  pipeline

---

## (b3) Cyclotomic squaring + lazy reduction in the safe-Rust path

The paper's progression table shows 8\% from cyclotomic squaring
(1.2\,ms $\to$ 1.15\,ms) and another 9\% from lazy reduction
(1.15\,ms $\to$ 1.05\,ms).  Smaller individual wins than (b2), but
both are present in the bedrock2 source already and just need to be
on the deployed call chain.

### Cyclotomic squaring

`bls12_Fp12_cyclotomic_sqr` should already be in the bedrock2 source
(the paper quotes 3192\,ns vs.\ 3692\,ns for the regular sqr).
**Verify** by greping the BLS12-381 generated tower for it.  If
present, the deployed `bls12_final_exp_hard_dsd` may already use it
or may still call the dense `bls12_Fp12_square` --- inspect the call
graph and patch if needed.

If absent: the cyclotomic squaring formula is straight-line algebraic
(a few Fp2 mul/add), it would be ~50 lines of bedrock2 plus the
weakest-precondition proof (~150 lines) + an unfold hint in
`bls12_final_exp_hard_dsd`.

### Lazy reduction

The lazy-reduction win in §5 of the paper applies to the SOS-form
$\mathbb{F}_{p^2}$ multiplication: defer the Montgomery reduction
until after the subtraction in the imaginary-part computation.  This
is implemented at the C-output path but not in the safe-Rust tower
because `bls12_Fp2_mul_sos` is a different fiat-crypto function.

To enable in the safe-Rust crate:
1. Add a fiat-crypto reified op for `mul_sos_lazy` and `red`
   (separate multiply phase + separate reduction phase, both already
   exist in the fiat-crypto literature; just need bedrock2 wrappers).
2. Replace the inner-loop $\mathbb{F}_{p^2}$ multiplications in
   `bls12_Fp6_mul`, `bls12_Fp12_mul` with their SOS-lazy versions
   (3 multiplies $\to$ 2 reductions instead of 3).
3. Re-run the WP proof; the only difference is the reduction
   placement (3 separate reductions $\to$ 2), which is a local
   transformation under the existing $\mathbb{F}_p$-bound spec.

### Effort

- Cyclotomic squaring (assuming bedrock2 source needs no changes,
  just call-graph patch): ~half day.
- Lazy reduction at the SOS level: 2--3 days, mostly in the
  fiat-crypto wrappers + matching WP proof.
- Per-curve regeneration: same extraction pipeline as (b2).

### Expected impact

Combined: $\sim$15--20\% on the safe-Rust pairing time, on top of
whatever (b2) delivers.  Less impactful than (b2) but cleaner
proofs and less risk.

---

## Suggested order

1. **Jasmin gating fix** (30 min) --- prerequisite for any honest
   "Jasmin row" in Tables 6 and 7.
2. **Re-measure with Jasmin actually wired in** (5 min) --- gets us
   the all-Jasmin row.
3. **Cyclotomic squaring patch / verify** (half day) --- low risk,
   small visible win.
4. **(b2) copy elimination** (1 week) --- the headline.
5. **(b3) lazy reduction** (3 days) --- final polish.
6. **Re-run benchmarks, regenerate Tables 6 and 7** (half day).

Total: $\sim$2 weeks of focused work to close the pairing-time gap
between the deployed safe-Rust crate and the paper's C-path numbers.
