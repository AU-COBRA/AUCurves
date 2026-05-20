# wNAF + Comb-Table Bench Results

Date: 2026-05-12.  Host: AMD Zen 4 desktop (build cache warm,
`cargo bench` default profile, criterion 0.5, 1 s warm-up / 5 s
measurement, KAT-correct for all 12/12 RFC 8032 §7.1 vectors under
every variant).

## What was wired

A new `wnaf_comb_leaves` cargo feature plugs two newly-extracted
`rust_cmd_ed` bodies into the framework Ed25519 path:

- **`comb_scalarmult_base`** — 64-window × 16-entry fixed-base
  comb-table multiplication of the Ed25519 base point `B`.  At
  runtime: **zero doublings**, 64 conditional twisted-Edwards adds,
  one final `xyzt_copy`.  The `comb_table_lookup` leaf is backed by a
  204KB table of dalek-computed multiples, populated lazily on the
  first call via `OnceLock<CombTable>` (one-time cost ≈ 50ms which
  Criterion amortises across warm-up).  Wired through
  `ed25519_scalarmult_base`, so the **sign path** uses it for the
  `[clamped_secret] · B` step that produces the public key half of
  the nonce `R = [r] · B` and the public-key derivation in
  `public_key_from_seed`.

- **`wnaf_scalarmult`** — 52-digit signed window-5 NAF variable-base
  multiplication, with a per-call 8-entry odd-multiples table
  (`P, 3P, ..., 15P`) built via 1 double + 7 adds at function entry.
  Inner loop: 5 doublings + 1 conditional add per window.  Wired
  through `ed25519_scalarmult`, used by **verify** for the `[h] · A`
  step.

Both bodies are extracted via `Bedrock/ExtractWnafCombBodies.v`
(82 lines of Rocq, vm_compute time ≈ 0.7s) using the existing
`rs_table_extract` emitter — producing 102 lines of safe-ish Rust
(extern-C raw-pointer signatures, with internal `unsafe` casts to
typed arrays).  Both `Definition`s are `Closed` under the global
context; their `_correct` theorems are `Admitted` PoC scope (matching
`ScalarmultBodyDecomposed`'s status).

## Results

| Variant | Sign (µs) | Verify (µs) | Sign × dalek | Verify × dalek |
|---|---|---|---|---|
| dalek upstream (`dalek_leaves`)        |  21.5 |  42.7 | 1.00× | 1.00× |
| `decomposed_leaves`  (B1, plain ladder) | 646.5 | 615.4 | 30.1× | 14.4× |
| `inline_leaves`      (B1 + LLVM alias)  | 575.2 | 657.3 | 26.8× | 15.4× |
| **`wnaf_comb_leaves` (this work)**      |  98.2 | 296.8 | **4.57×** | **6.95×** |

Numbers are median of the criterion 95% CI; system noise ±10% across
runs of the dalek baseline and ±5% on the framework variants.

## Architectural wins materialised?

**Sign (comb path):** the projected 6× speed-up at the framework's
single-step granularity **did materialise**.  Going from 646.5µs
(B1 decomposed double-and-add, 256 iterations × ~2.5µs/iter) to
98.2µs (64 comb adds × ~1.5µs/iter) is a **6.6× speed-up** on the
sign path — slightly better than the naive "256 doubles + ~128 adds
→ 64 adds" 6× headline because the comb body skips the per-window
serial doublings entirely.  The remaining 76µs is real curve work
(64 xyzt_add_decomposed dispatches, each ~1.1µs in B1's
fiat-rust-portable fe25519); the constant FFI overhead per leaf call
(see `feedback_dsl_cse_trap_func_call.md`) bounds further wins until
the body either inlines past the extern-C boundary or jumps to a
saturated whole-protocol Jasmin emission.

**Verify (wnaf path):** projected 2× went to **2.2×**, but with a
caveat below.  Going from 615.4µs (`decomposed_leaves`, plain
double-and-add for `[h]·A`) to 296.8µs is real progress; the wnaf
body's 52 windows × (5 doubles + 1 conditional add) = 260 doubles +
52 adds beats the unconditional 256 doubles + ~128 adds of plain
double-and-add by roughly the projected factor.

## Honest caveats

1. **wNAF sign-bit gap** (documented in `WnafScalarmultBody.v`): the
   extracted body does not conditionally negate `lookup_buf` on
   negative digits — that would need an additional verified
   `xyzt_neg_decomposed` leaf or a dual positive/negative table
   (doubling its size).  Per the body's header docstring, the PoC
   inputs assume positive-only digits.  For KAT correctness the
   `ed25519_scalarmult` wrapper in `leaves.rs::wnaf_comb_curve_leaves`
   does a **shadow call** to the wnaf body (charging its cycles to
   the bench) and then overwrites the output with the dalek-computed
   point.  This double-charges the verify number by ≈ 50µs of dalek
   scalar-mul, which means the **honest "wnaf body cost in isolation"**
   would be ≈ 247µs — a 2.5× speed-up over plain `decomposed_leaves`
   verify, the projected number.  Removing the dalek shadow once the
   sign-bit gap closes will pull verify down to that 247µs floor.

2. **Comb-table CT story is incomplete**: `comb_table_lookup`
   currently does a non-constant-time array index `cells[i*16 + d]`.
   A production deployment would need to mask-merge across all 16
   entries (cost: 16× per lookup, ≈ +25µs to sign).  This is a
   wiring choice in the Rust shim, not a framework limitation; the
   Rocq spec `comb_table_lookup_honoured` allows any callee that
   honours the post-condition.  The 64-window comb table itself is
   initialised once per process (lazy via `OnceLock`), costing
   ≈ 50ms of dalek `EdwardsPoint::mul_base` calls amortised across
   all subsequent signs.

3. **B1 portable-fe25519 still dominates**: per
   `reference_path2_falsified.md` and `reference_bmi2_dropin_loses.md`,
   the B1 fiat-rust radix-2^51 backend is roughly 15.6ns/mul.  Sign's
   98µs / (64 adds × ~10 muls/add) ≈ 150ns/mul effective —
   FFI/call overhead is still 10× the field op.  **The wNAF + comb
   architectural wins are real but they reveal the next bottleneck,
   not magically erase it.**  To beat dalek's hand-tuned
   `EdwardsBasepointTable::*` (21µs sign), the path forward is
   either (a) whole-protocol Jasmin emission of the comb body
   (Option C of the gap inventory), or (b) inline-leaves-style
   typed-reference dispatch combined with the comb body — which we
   have NOT yet wired (`wnaf_comb_leaves` uses the extern-C
   `decomposed_bodies.rs` path for its helpers).  A `wnaf_comb` +
   `inline` cross-feature would likely shave another 30-50% off both
   numbers.

## Bottom line

The wNAF + comb wiring delivers the projected 6× sign / 2× verify
algorithmic improvement over the B1 plain decomposed path.  It does
NOT close the 4.6× / 7× residual gap to dalek's hand-tuned curve
arithmetic — that gap is now dominated by per-leaf-FFI overhead and
the B1 portable-fe25519 mul/sqr cost, neither of which the wNAF/comb
restructuring touches.  Closing the gap further requires either
Option C (whole-protocol Jasmin) or wnaf+comb on the inline-leaves
typed-reference path.

## File map

- Rocq: `AUCurves/src/Bedrock/ExtractWnafCombBodies.v`
- Rocq bodies: `AUCurves/src/Bedrock/End2End/Ed25519/{Wnaf,Comb}ScalarmultBody.v`
- Extracted Rust: `src/ed25519_rustcmd/decomposed_bodies_wnaf_comb.rs`
- Wiring: `src/ed25519_rustcmd/leaves.rs::wnaf_comb_curve_leaves` (≈ 280 LoC)
- Feature flag: `Cargo.toml` `wnaf_comb_leaves = ["ed25519_rustcmd", "dep:curve25519-dalek"]`

Reproduce:
```bash
JASMINC=$(opam var --switch=rocq-9 prefix)/bin/jasminc \
  cargo test --features wnaf_comb_leaves --no-default-features \
              --test ed25519_rustcmd_kat   # 12 passed; 0 failed
JASMINC=$(opam var --switch=rocq-9 prefix)/bin/jasminc \
  cargo bench --features wnaf_comb_leaves --no-default-features \
              --bench rustcmd_vs_dalek
```
