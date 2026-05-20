# Plan: kill the per-leaf compress/decompress round-trip

## Problem

The framework's verify is **109 µs**; dalek-native verify is **25 µs**.  Per
`xyzt_micro.rs` (commit `b107bfe`), the layers are already near-parity:

  comb_scalarmult_base : 12.7 µs (1.19× behind dalek's 10.7 µs)
  wnaf_scalarmult      : 43.5 µs (1.59× behind dalek's 27.3 µs)
  xyzt_double          :  108 ns (0.71× — faster than dalek)
  xyzt_add  (in-body)  : ~200 ns (1.3× — near parity)

So algebra isn't the gap.  What's left is **point representation
churn at the leaf-call boundary**.  Three structural costs survive:

  (A) `ed25519_decompress_A/R` (2× per verify): 32-byte canonical →
      200-byte XYZT slot.  Calls `fe25519_portable::decompress`
      (sqrt chain ~250 squares).  ~5 µs each.

  (B) `ed25519_compress` (1× per verify, 1-2× per sign): 200-byte
      XYZT → 32-byte canonical.  Calls `compress_xyz` (Z^-1 chain
      ~250 squares + a few muls).  ~3 µs each.

  (C) `encode_point_xyzt` (1× per verify shadow + 1024× one-time
      comb table init): dalek `EdwardsPoint` → 200-byte slot.
      Currently goes through compress-then-decompress *for the
      same point* — a wasted round-trip just to materialize bytes.

(C) is pure waste.  (A) and (B) are at the wire boundary and dalek
pays the same kind of cost (it just keeps the limbs in
`FieldElement51` instead of converting through canonical bytes
between consecutive ops).

There's also the **wnaf shadow double-count** at
`leaves.rs::ed25519_scalarmult` — runs both dalek (KAT-correct) and
the wnaf body (timing-charged, output discarded).  Adds ~43 µs to
verify.  Not a representation issue per se but enables (C)'s
wasted round-trip.

## Plan

Five phases, ordered by ROI on a Zen 4 baseline (sign 31 µs / verify
109 µs).  Each phase's cost is independent except where noted.

### Phase 1 — Drop the dalek-shadow round-trip in `ed25519_scalarmult`

**Saved on verify:** ~43 µs (the wnaf-body cost stays, the dalek
computation goes away).

The shadow exists because the extracted `wnaf_scalarmult` body's
sign-bit handling is the documented Admitted gap in
`AUCurves/src/Bedrock/End2End/Ed25519/WnafScalarmultBody.v`.  Two
sub-tracks:

  **1a (Rocq, ~1 week).**  Implement the conditional-negate primitive
  at the field level in `WnafScalarmultBody.v`: when the wnaf digit's
  sign bit is set, negate the looked-up table entry's X (and Ta)
  coords before adding.  `fe25519_neg` already exists.  Update the
  body to dispatch on `digit_byte >> 7`.  Re-extract.

  **1b (Rust-only stop-gap, ~1 day).**  Re-instate `ed25519_scalarmult`
  as a thin forwarder to `wnaf_scalarmult` with a Rust-level
  conditional-negate wrapper around the lookup step.  Lose Rocq
  verification of the conditional-negate logic; gain perf today.

After Phase 1 verify drops from 109 → ~66 µs (2.6× behind dalek).

### Phase 2 — Direct dalek → 200B-slot encoder

**Saved on verify** (only relevant if Phase 1 hasn't landed *and* we
still go through the shadow path): ~5 µs.  **Saved on comb-table
build:** ~50 ms one-time warmup (1024 cells × ~5 µs each).

`leaves.rs::encode_point_xyzt` currently does:

```rust
let compressed = point.compress();                       // ~3 µs
match fe25519_portable::decompress(compressed.as_bytes()) // ~5 µs
```

A point that's already in dalek's projective `EdwardsPoint`
representation gets compressed to 32 bytes (a Z^-1 chain) and then
decompressed (a sqrt chain) just to land in our 200-byte slot — and
both reps store the same affine `(x_aff, y_aff)`.

Replace with a direct path: copy dalek's `FieldElement51`'s 5×u64
limbs into our fiat tight slot.  dalek's `FieldElement51` and
fiat's `fiat_25519_tight_field_element` use the same radix-2^51
encoding; the limb values are interchangeable modulo a reduce step.
`curve25519_dalek::edwards::EdwardsPoint` doesn't pub-expose
`X/Y/Z/T` directly, so route through `to_montgomery` /
`compress_internal` private API mirroring, or upstream a
`projective_limbs()` accessor.

Optional follow-on: if Phase 1 closes via track 1a, Phase 2 only
helps the one-time comb-table init.

### Phase 3 — Cache the decompressed pubkey

**Saved on verify** (under a Signal-style use pattern): ~5 µs/verify.

In libsignal a single pubkey is used to verify many signatures.
`ed25519_decompress_A` runs the sqrt-chain decompress on every
verify call.  An API addition would let callers pass a pre-decompressed
200-byte XYZT slot:

```rust
pub fn verify_with_decompressed_pk(
    sig: &[u8; 64], pk_xyzt: &[u8; 200], msg: &[u8],
) -> bool;
```

Callers who hold the pubkey across many verifies decompress once,
amortizing.  No change to the verified extraction or curve
arithmetic — purely a Rust-API surface addition.

### Phase 4 — Skip the verify final-compress via projective equality

**Saved on verify:** ~3 µs.

The verify equation is `R = s·B − k·A`, which the framework
currently checks by computing the rhs in projective form, then
calling `ed25519_compress` (~3 µs Z^-1) and `bytes_equal_32` against
the wire `R`.

Alternative: compute `rhs` projectively and `R_decompressed`
projectively, then check `rhs.X * R.Z = R.X * rhs.Z` and
`rhs.Y * R.Z = R.Y * rhs.Z` (4 muls + 2 sub + 1 OR — under 1 µs).
No Z^-1 needed.

Dalek does compress + compare; we'd be ~3 µs ahead.  But: this
changes the verified body in `Sign_Verify_RustCmd.v` — the verify
chain produces a 32-byte intermediate today that the security proof
references.  Reproving against the projective-equality version is
a meaningful chunk of Rocq work (~3 days).

### Phase 6 — Straus 2-MSM: AUTHORED but **does NOT help here**

**2026-05-12 honest finding**: rust_cmd_ed Straus body authored
(`AUCurves/src/Bedrock/End2End/Ed25519/Straus2MSMBody.v`, extracted
via `ExtractWindow4Body.v` into
`curve25519-jasmin-rs/src/ed25519_rustcmd/decomposed_bodies_window4.rs`
as `straus_2msm`).  **Not wired into verify** because of a
re-analysis showing Straus 2-MSM is **slower** than the current
comb + window-4 split for Ed25519:

Cost comparison (Zen 4, op-count estimates at our measured per-op
amortized cost of ~108 ns/double, ~200 ns/add inlined):

  Current verify scalarmult:
    comb_scalarmult_base (sB):  0 doubles + 64 adds              = 13 µs
    window4 (hA):               252 doubles + 64 adds + 14 setup = 43 µs
    Total:                                                       = 56 µs

  Straus 2-MSM (sB + (-h)·A):
    256 doubles + 128 adds + 30 setup adds                       = 60 µs

Straus is 4 µs SLOWER because we lose the comb's "0 runtime
doublings" property when sharing doublings between both sides.
Conclusion: the comb's pre-computed multiples table (64×16 cells,
~204 KB warmup) is strictly better than Straus's shared-doublings
trick **for this specific 2-MSM**, because one side is a fixed
generator with a precomputable table.

The Straus rust_cmd_ed body stays in tree as a verified-extraction
artefact (demonstrates the framework's ability to author a 4-input
scalarmult body), but is not the verify-time path.

(Original plan estimated ~4 µs verify saved.  The estimate was off
by sign — Straus is ~4 µs WORSE here, not ~4 µs better, because the
original analysis forgot that one of our two scalarmults uses the
basepoint comb.)



**Saved on verify:** ~7 µs (current 13+43 = 56 µs scalarmult cost
→ ~49 µs with shared doublings).

Ed25519 verify is a **2-MSM**: compute `s·B − k·A` from two distinct
bases.  The right algorithm at n=2 is **Straus** (shared doublings
across both scalars), not Pippenger (which amortizes bucketing
over thousands of scalars and would lose at n=2).

We already have a verified Pippenger MSM for BLS12-381 G1
(`AUCurves/src/Bedrock/End2End/BLS12_381/MSM*.v`, 0 admits, 1 axiom).
Pippenger itself doesn't fit, but the **sub-lemmas are reusable**:

| BLS MSM primitive                       | Direct Ed25519 reuse                  |
|-----------------------------------------|---------------------------------------|
| Signed-window NAF table precompute      | Already in `WnafScalarmultBody.v`     |
| Bucket-accumulator running-sum reduction| **Useful** for Straus interleave loop |
| CT conditional select over a table      | Already in `comb_table_lookup`        |
| Window-size dispatch (c = 5, 7, 9, 11)  | Parameterizes the wNAF body's `c`     |
| `IteratedSepPoints` sep-logic           | Re-prove harness for Straus           |

Concrete plan: **author Straus as a `rust_cmd_ed` AST** (per the
2026-05-12 design refinement; matches `WnafScalarmultBody.v` and
`CombScalarmultBody.v`'s shape, not the BLS MSM's bedrock2 WP
shape).

  - New file `End2End/Ed25519/Straus2MSMBody.v`:
      - `straus_2msm_body : function_body_ed`
      - Definitionally: precompute `T_B[0..16]` and `T_A[0..16]`
        (each 16 × `TFp25519`-typed XYZT slots), then 64 iterations
        of `(REdCall xyzt_double_decomposed) × 4` shared between
        both scalarmults + `(REdCall xyzt_add_decomposed)` per
        scalar per nibble + CT-select via 16-way mask merge.
      - Use **unsigned window-4 digits**, sidestepping the wnaf
        sign-bit Admitted gap (same trick Phase 1b uses today).
  - Update `ExtractCurveBodies.v` to extract the new body.
  - Wire `ed25519_verify`'s scalarmult path to call
    `straus_2msm_decomposed` instead of separate `comb` + `wnaf`.

Cost: ~2-3 days authoring + extraction + KAT validation.  The
correctness theorem stays Admitted (PoC-level, same status as the
existing wnaf and comb bodies).  No bedrock2 WP machinery needed —
the BLS MSM's bedrock2 specs were the expensive part; the
`rust_cmd_ed` shape is far simpler.

Predicted ROI: ~4 µs verify saved.

  Current (Phase 1b sign+verify):
    sign:   comb_scalarmult_base(s)         = 13 µs
    verify: comb(s) + window4(k, A)         = 13 + 44 = 57 µs
  Straus 2-MSM (verify only):
    256 shared doublings × 108 ns +
    128 adds × 200 ns + 28 table-setup adds = ~53 µs

Saves ~4 µs verify, no win for sign (sign is 1-MSM with the
basepoint — comb_scalarmult_base is already optimal at 0
doublings).

Phase 6 lands after Phase 1+4 in the recommended sequencing
(verify ~63 → ~59 µs).  With `rust_cmd_ed` it's a small enough
chunk to fit alongside Phase 4 in the same session.

### Phase 1a / Phase 2 deferred — deeper than the plan estimated (2026-05-12 late)

Attempted both; ran into architectural issues that the original plan
hand-waved.  Honest scoping for future sessions:

**Phase 1a (signed wnaf)**: the existing `WnafScalarmultBody.v`'s
fixed-spacing loop (5 doublings + 1 lookup per iter) requires its
digit stream to use **fixed-position windows with odd-only
magnitudes**.  Our `wnaf_digits_compute` produces **variable-spacing
wNAF** (standard form — scans past zero bits, can land at any bit
position).  These are incompatible: the body's `abs_idx :=
magnitude >> 1` only works for odd magnitudes (±1, ±3, …, ±15), but
fixed-width-5 windows produce even digits too unless we propagate
a carry across windows.

To close: either
  (a) write a new `wnaf_digits_compute_aligned` that produces
      fixed-spacing odd-only digits via signed-digit Booth-like
      recoding (~half day Rust);
  (b) generalize `WnafScalarmultBody.v` to accept even digits and
      handle them via xyzt_add_decomposed pairs (~1 day Rocq).
The `xyzt_cond_negate` leaf and the AST modification of
`WnafScalarmultBody.v` (commits not yet wired) are tree-resident
infrastructure for whichever path lands.

**Phase 2 (HWCD 9M precomputed comb tables)**: requires three new
things:
  - New comb-table cell format: 3 × 40 bytes = 120 bytes storing
    `(Y-X, Y+X, 2d·T)`.  Saves 80 bytes per cell, total 82 KB
    (vs current 204 KB).  Plus per-cell-build cost (extra muls).
  - New `xyzt_add_madd_body` (mixed add) in rust_cmd_ed that takes
    one precomputed-format operand: 7M dedicated add per HWCD §3.2.
  - Modified `comb_table_lookup` Rust leaf that outputs the new
    format from dalek's per-cell EdwardsPoint.
  - Updated `CombScalarmultBody.v` to call `xyzt_add_madd` instead
    of `xyzt_add_decomposed`.

Per-add saving: 3 muls = ~0.4 µs.  Per sign / verify: ~2 µs.

Implementation cost: ~1 day Rocq + 1 day Rust.  ROI is small relative
to effort.  Worth doing for the verification narrative + bigger
"verified extended-Edwards add" coverage, but not for perf today.

### Phase 1a-revised — Verified extraction of Phase 1b's window-4

**Status (2026-05-12)**: rust_cmd_ed body authored.  Next step:
extraction wire-up.

Phase 1b shipped a Rust-level window-4 scalarmult (commit `f91c713`,
`leaves.rs::wnaf_comb_curve_leaves::ed25519_scalarmult`).  The
durable-verification follow-on is to author the same algorithm as a
`rust_cmd_ed` AST so it's extracted through the existing
`ExtractCurveBodies.v` pipeline.

  - **AUCurves commit `0632fdd`**: `Window4ScalarmultBody.v` — 299
    LoC, `window4_scalarmult_body : function_body_ed` defined and
    type-checked; `window4_scalarmult_body_correct` theorem stated
    with the same loop-invariant shape (`window4_partial_sum scalar
    j` over the top-j nibbles) as the comb/wnaf bodies and left
    `Admitted` at PoC level.

  - **TODO**: update `Bedrock/ExtractCurveBodies.v` to extract
    `window4_scalarmult_body` to `window4_scalarmult` Rust function.
    Then in curve25519-jasmin-rs, replace the hand-written window-4
    in `ed25519_scalarmult` with an extern call to the auto-extracted
    `window4_scalarmult`.  ~1 day.

  - Same algorithm as Phase 1b, so perf neutral; the win is the
    verified-extraction story.

### Phase 5 — Faster decompress / compress primitive

**Saved on sign:** ~2 µs (1-2 compress per sign × ~1 µs saved).
**Saved on verify:** ~5 µs (2 decompress + 1 compress × ~1 µs each).

The Z^-1 chain in `compress_xyz` and the sqrt chain in `decompress`
are both ~250 squares + a few muls.  Inversion is the standard
Fermat chain (p−2 exponent).  Two paths:

  **5a.** Use a shorter Fermat addition chain (e.g., Bernstein's
  255-bit p-2 chain hand-optimized to 254 squares + 11 muls).
  ~5% improvement — marginal.

  **5b.** Move the inversion chain into Jasmin.  jasminc-verified
  amd64 asm for a 250-square loop should be ~30% faster than
  fiat-rust's loop (no per-square Rust function-call overhead,
  better register scheduling).  But: this is a research project
  with low ROI vs Phase 1 + 4.

Skip 5 unless Phase 1-4 land first and the residual gap warrants it.

## Sequencing recommendation

Three commits to do in order:

  Step 1: Phase 1b (Rust-only conditional-negate wrapper, 1 day).
    Verify drops 109 → ~66 µs.  Lose Rocq cert of that one wrapper,
    gain immediate close to dalek.

  Step 2: Phase 4 (projective equality at verify boundary, ~3 days
    Rocq + 1 day Rust).
    Verify drops 66 → ~63 µs.  Plus Rocq re-prove of verify chain.

  Step 3: Phase 1a (the Rocq sign-bit fix in
    `WnafScalarmultBody.v`, ~1 week).
    Replaces Phase 1b's unverified wrapper; perf is the same; the
    verification artefact tightens.

Phases 2, 3, 5, 6 are independent — each commit lands when the win
exceeds the cost on the day.  Phase 6 collapsed to ~2-3 days once we
realized `rust_cmd_ed` is the natural shape (NOT bedrock2 WP) — its
~4 µs win now lines up cost-comparably with Phase 4's ~3 µs win;
land both opportunistically.

## Expected end-state

After Phases 1+4 (the load-bearing pair):

  sign:    31 µs  (unchanged — sign doesn't hit the wnaf shadow)
  verify:  ~63 µs (vs dalek 25 µs — 2.5×)

After Phases 1+4+3 (Signal-cached pubkey):

  verify per call (amortized): ~58 µs  (2.3× dalek)

Closing the last 2× to dalek would require Phase 5 + a wnaf
algorithm overhaul to match dalek's "table-Pippenger with
pre-doubled comb" verify path.  At that point we're inside dalek's
specific optimisations and the verification overhead probably
isn't worth the win — the framework's value proposition is the
verified chain, not raw speed.

## Out of scope

Things that *look* like representation issues but aren't on the
critical path:

  - The 200-byte slot is already in limb form under `tfp25519_limbs`
    (commit `2bb9efe`).  No further within-body conversion happens.
  - Field arithmetic is at fiat-rust parity with dalek.  CryptOpt
    asm was tried and lost on Zen 4 (`feedback_bmi2_dropin_loses`).
  - LLVM cross-crate inlining is already maximal under release+LTO
    (commit `0855c4a` falsified the "extern C blocks inlining"
    hypothesis).
