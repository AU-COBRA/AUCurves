# AUCurves TODO

## Caller-side `__ac.clone()` elimination — biggest remaining safe-Rust win (2026-04-19)

After Phase B-1 (cyclotomic squaring) and Phase B-3 (`_nocopy` leaves)
the BLS12 pairing sits at ~4.49 ms vs blst's 0.45 ms — about 10× gap.
The Phase B-3 `_nocopy` switch only eliminates each leaf's INTERNAL
`allocx`/`allocy` copies; the dominant remaining overhead is the
caller-side `let __ac{n} = dest.clone();` clones the pretty printer
emits before every potentially-aliased call.

**Why these clones exist.** Rust's borrow checker forbids
`fn(&mut x, &x, &y)` even when the function would internally read `&x`
before writing `&mut x`. The pretty printer (`safe_cmd` in
`src/Bedrock/ToSafeRustBody.v` line 442) detects when the dest's base
variable name appears in any source expression and emits a clone:
```rust
let __ac0 = result.clone();
bls12_Fp12_mul_nocopy(&mut result, &__ac0, &base);  // result *= base
```

**Cost inventory (verified by grep on the current generated tower).**

| Cloned variable | Type | Bytes | Count in tower |
|-----------------|------|-------|----------------|
| `tmp1` (mostly Fp2 in miller_loop) | Fp2 | 96 | 23 |
| `t` (Fp6 / Fp2) | Fp6 | 288 | 17 |
| `t1` (Fp12) | Fp12 | 576 | 12 |
| `result` (Fp12) | Fp12 | 576 | 9 |
| `f` (Fp12) | Fp12 | 576 | 6 |
| `C` (Fp2) | Fp2 | 96 | 6 |
| `result.c0.c0.c0` (Fp from cyc_sqr +1) | Fp | 48 | 5 |
| `cyc_t0` (Fp6) | Fp6 | 288 | 5 |
| other (`tmp*`, `D`, `E`, `lambda`, …) | mixed | mixed | ~11 |
| **94 total** | | | **~27 KB / pairing call** |

By tower function:

| Function | Clones | Comment |
|----------|--------|---------|
| `bls12_miller_loop_proj` | 23 | called 1× per pairing |
| `bls12_final_exp_hard_dsd` | 23 direct | inner DSD loop runs 252× |
| `bls12_miller_loop` | 13 | not on the projective hot path |
| `bls12_Fp6_mul` | 10 internal | called hundreds of times |
| `bls12_Fp12_mul` | 2 internal | called ~60× |
| (rest) | < 5 each | |

**Ballpark perf impact.** A 576-byte Fp12 clone is ~9 cache-line copies
(~6 ns of pure copy + cache pollution). The 94 clones × ~6 ns ≈ 560 ns
per pairing, *not counting* the cache-pollution cost which is probably
a similar order of magnitude. Removing them all could plausibly save
1–2 ms on the pairing — ~30% improvement, getting us from 4.49 ms down
to ~3 ms range.

**Why blst doesn't pay this cost.** Its leaf ABI uses `fn op(&mut a, &b)`
(self-mutation): `a *= b` style, where `a` is owned-mutable and `b` is
shared. Rust accepts this because `&mut a` and `&b` are guaranteed-disjoint
by the type signature. No clone needed at the call site.

**Proposed fix: add `_into_self` leaf siblings.**

```rust
// Current ABI (3 refs; cannot pass &mut x, &x):
fn bls12_Fp12_mul(out: &mut Fp12, x: &Fp12, y: &Fp12);

// New ABI (handles self-mutation natively):
fn bls12_Fp12_mul_into_self(self_: &mut Fp12, other: &Fp12);
```

Pretty printer extension: when emitting a call where dest aliases
source position 0 (the most common pattern: `result = result * x`),
emit `bls12_Fp12_mul_into_self(&mut result, &x)` — no clone needed,
since `&mut result` and `&x` are guaranteed-disjoint by Rust's type
system.

**Effort breakdown.**

1. Define `_into_self` variants as new bedrock2 functions (or hand-write
   the Rust impl + add to wrapper table) — ~2 days
2. Extend the pretty printer (`safe_cmd` in ToSafeRustBody.v) to detect
   the `dest = dest * other` pattern and emit `_into_self` — ~1 day
3. Verify proofs still hold (the bedrock2 spec for `_into_self` is
   `mul`'s spec specialised to `out = x` — same algebraic guarantee) —
   ~2 days
4. Re-extract, regenerate the tower, benchmark — ~half day

Total: ~5–6 focused days. Risk: low; the algebraic identity is the
same, only the ABI changes.

**Patterns to detect in the pretty printer:**

- `dest = dest * other`  → `mul_into_self(&mut dest, &other)`
- `dest = other * dest`  → `mul_into_self(&mut dest, &other)` (mul is commutative)
- `dest = dest + other`  → `add_into_self(&mut dest, &other)`
- `dest = dest - other`  → `sub_into_self(&mut dest, &other)`
- `dest = dest²`         → `square_into_self(&mut dest)`
- `dest = -dest`         → `neg_into_self(&mut dest)`

Skip when dest's address path is a sub-field (e.g. `out.c0`) — those
already work without aliasing because the printer's `dv` test on
base-name only is the wrong check there; use proper sub-field
disjointness analysis.

**When to revisit.** When closing the safe-Rust ↔ blst gap below 5×
becomes the priority over other Phase B work or paper-writing. As of
2026-04-19 the standing gap is 10× and the dominant cost is exactly
this — so this is the natural next perf optimisation.

---

## BLS12_FinalExp.v ↔ bls12_final_exp definition drift (2026-04-19)

The WP proof in `src/Bedrock/Field/Synthesis/Examples/BLS12_FinalExp.v` was
written against a version of `bls12_final_exp` (defined in BLS12_Pairing.v
~line 1072) and `final_exp_full_body` (~line 1043) that no longer matches
the current source.

**Mismatch 1 — stackalloc count**

- Definition `bls12_final_exp` has 2 stackallocs: `result`, `tmp`
- WP proof at lines 326-343 expects 4: `result`, `tmp`, `base`, `h3`
  (where `h3` is 160 raw bytes for the h3-store buffer used by the cyclotomic
  squaring inner loop)
- Partial fix: adding the missing 2 stackallocs to the def passes the line-337
  error (`apply Z_mod_mult` works again) but exposes Mismatch 2.

**Mismatch 2 — final_exp_full_body call list**

- Current `final_exp_full_body` has 6 calls: `conjugate; inv; mul; frobenius_p2;
  mul; bls12_final_exp_hard_dsd`.
- WP proof at line 467 (after passing the stackalloc fix) expects "Call 6:
  fp12_copy(base, result)" — a `fp12_copy` call from `result` into `base` that
  doesn't exist in the current body. The section comment ("D2: fp12_set_one +
  h3_stores + loop + final copy + dealloc") suggests the proof was written for
  a more elaborate body that inlines part of what `bls12_final_exp_hard_dsd`
  now does (h3 store, exp loop, etc.).

**Likely root cause**

At some point `bls12_final_exp` was simplified to just call
`bls12_final_exp_hard_dsd` after the easy-part cleanup, but the WP proof in
FinalExp.v was not updated to match. The proof appears to have been written
when the entire DSD pipeline (h3 stores, cyclotomic exp loop, final copy) was
inlined into `final_exp_full_body` rather than delegated to `bls12_final_exp_hard_dsd`.

**Two paths to resolve**

1. Re-inline the DSD pipeline back into `final_exp_full_body` (matching what
   the WP proof expects). This means dropping the `cmd.call ... bls12_final_exp_hard_dsd`
   in favour of the explicit body. Effort: medium.

2. Rewrite the FinalExp.v WP proof from line 326 onwards to match the
   current 6-call delegated structure. Effort: large (the proof is ~600 lines
   from line 326 to Qed).

Path 1 is probably easier since the inlined-body version is what the proof
already understands.

**Why this isn't blocking H3**

The H3 fix (`SepReflectiveAC.v` + the reflective emp-True dedup recipe in
`BLS12_FinalExpH3.v`) is independent — H3 builds in ~10s. The drift here only
blocks `BLS12_FinalExp.vo`.

**Why this isn't blocking Phase B-1 cyc_sqr**

Phase B-1's cyc_sqr substitution is in `BLS12_Pairing.v` (compiles fine). The
runtime semantics are unchanged for `bls12_final_exp_hard_dsd`'s body —
`dsd_exp_x_loop` and `dsd_exp_x_half_loop` use cyclotomic squaring instead of
generic Fp12_sqr, and two extra Fp6 stackallocs (`cyc_t0`, `cyc_t1`) are
added to `bls12_final_exp_hard_dsd`. Those don't affect the call signature,
so `bls12_final_exp` (which calls hard_dsd via cmd.call) doesn't see any
difference.

The drift exists in `bls12_final_exp` itself, not in `bls12_final_exp_hard_dsd`.
