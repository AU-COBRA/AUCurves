# `cryptopt_leaves` performance evaluation — 2026-05-13

Roadmap item #10: evaluate whether `cargo --features cryptopt_leaves`
(the 4×64 saturated-Solinas fe25519 shim with CryptOpt-superoptimized
mul / square asm) is a net win over the default `fe25519_portable`
(fiat-rust 5×51 unsaturated radix-2^51) shim for the Ed25519
sign / verify hot path.

## TL;DR

**LOSS — DO NOT enable by default.**

`cryptopt_leaves` causes a **~33–36% end-to-end slow-down** on both
`ed25519_sign` and `ed25519_verify` under the `decomposed_leaves` body
chain.  No code wiring change has been committed.  The fe25519 micro
benchmark confirms the asm itself is ~28 % faster than fiat 5×51
(matching the predicted 30 % field-op speedup), but the
5×51 ↔ 4×64 byte-bridge cost more than erases that win at the
protocol level, exactly as documented in the `fe25519_cryptopt.rs`
header comment from when the shim was first prototyped.

This eval doc is committed; the underlying `cryptopt_leaves` feature
is left in place as-is (still a build target, still KAT-passing) but
remains opt-in only — it is NOT promoted to a default and the
`docs/performance-and-panic-freeness-2026-05-13.md` §1.4 step B
prediction ("~30 % field-op speedup … 1 session") is empirically
falsified for the current ABI.

## 1. Setup

| Item | Value |
|---|---|
| Host | Zen 4 |
| Date | 2026-05-13 |
| Compiler | rustc 1.93.0 |
| jasminc | `$OPAM_ROOT/rocq-9/bin/jasminc` |
| Bench harness | `benches/rustcmd_vs_dalek.rs` (criterion 0.5, `--quick`) |
| Workload | RFC 8032 TEST 2 (1-byte msg) — same vector that gates KAT |

Two feature configurations were measured for the apples-to-apples
comparison.  Both go through the same `decomposed_leaves` body chain
(extracted `XyztAddBodyDecomposed.v` / `XyztDoubleBodyDecomposed.v` /
`ScalarmultBaseBodyDecomposed.v`); the only difference is the
`fe25519_*` leaf shim:

| Config | fe25519 shim | features |
|---|---|---|
| Baseline | `fe25519_portable` (fiat-rust 5×51) | `decomposed_leaves` |
| Variant | `fe25519_cryptopt` (4×64 sat Solinas, asm mul/sq) | `decomposed_leaves cryptopt_leaves` |

Note: `cryptopt_leaves` is gated `not(feature = "dalek_leaves")` and
`cryptopt_leaves = ["decomposed_leaves"]` (Cargo.toml).  So the
strongest framework path that engages cryptopt is the
`decomposed_leaves` chain — `wnaf_comb_leaves` is mutually exclusive
with `decomposed_leaves` at the Rust-cfg level (see
`leaves.rs:598-608`) and therefore CANNOT be measured under cryptopt
with the current feature graph.  This means the rest of the
`performance-and-panic-freeness-2026-05-13.md` §1.4 stack-up
"~13 µs sign, ~35 µs verify with A+B+D" is also blocked on this
mutual-exclusion: B never composes with the wnaf_comb / tfp25519_limbs
chain in the current crate.

## 2. End-to-end results (criterion `--quick`, median)

| Bench | Baseline (`decomposed_leaves`) | + `cryptopt_leaves` | Δ |
|---|---:|---:|---:|
| `ed25519_sign/framework`   | 399.15 µs | 542.61 µs | **+36 %** (regression) |
| `ed25519_verify/framework` | 407.22 µs | 540.97 µs | **+33 %** (regression) |

Cross-check rows from the same runs (orthogonal sanity):

| Bench | Baseline | + cryptopt |
|---|---:|---:|
| `ed25519_sign/dalek` | 14.82 µs | 15.16 µs |
| `ed25519_verify/dalek` | 22.52 µs | 26.16 µs |

The dalek rows are independent of `cryptopt_leaves` (dalek uses its
own internal field arithmetic).  Their values are stable to ~1 µs
across runs and confirm the host wasn't under unusual load during the
cryptopt run.  A second `--quick` repeat of the cryptopt sign reported
527.99 µs (within 2.8 % of the headline 542.61 µs), and a repeat of the
cryptopt verify reported 534.68 µs (within 1.2 %), so the regression is
reproducible.

Criterion CI: the cryptopt sign 95 % CI [541.79, 545.89] µs and
baseline sign 95 % CI [395.87, 399.07] µs **do not overlap**, so the
regression is significant at p < 0.05.  Same for verify
([532.62, 543.06] vs [404.57, 415.62]).

## 3. Why the prediction failed — micro-bench breakdown

The §1.4 step B prediction reasoned "30 % field-op speedup".  This is
**correct at the asm level but wrong at the protocol level**.  The
`fe25519_micro` benchmark decomposes the cost:

| Operation | Time |
|---|---:|
| fiat5x51 `carry_mul` (bare 5×51 input → 5×51 output) | 12.92 ns |
| cryptopt 4×64 mul (bare 4×64 input → 4×64 output) | 9.35 ns |
| cryptopt 4×64 mul with 5×51 ↔ 4×64 bridge | 27.81 ns |
| fiat5x51 full shim (40-byte slot codec, what the bodies actually pay) | 53.22 ns |

So at the asm level cryptopt IS the predicted 28 % faster
(9.35 ns vs 12.92 ns).  But the decomposed bodies call `fe25519_*`
through a byte-slot ABI (`*mut u8` / `*const u8` over 40-byte
slots) — to feed cryptopt's 4×64 asm we need to:

1. Read 40-byte slot.
2. Decode top 32 bytes into fiat 5×51 tight (`fiat_25519_from_bytes`).
3. Re-encode 5×51 → 32 bytes → 4×u64 (`fiat_25519_to_bytes` + 4×
   `u64::from_le_bytes`).
4. Call cryptopt asm.
5. Solinas-fold the [0, 2^256) output to [0, 2^255 + 19) so it
   fits `fiat_25519_from_bytes`'s input range — TWO fold iterations
   in the worst case (see `fe25519_cryptopt.rs:148-185`).
6. Re-encode 4×u64 → 32 bytes → 5×51 tight.
7. Write 40-byte slot.

Steps 2/3/5/6 are what the "with 5×51 ↔ 4×64 bridge" row at
27.81 ns captures.  The total per-call cost is 27.81 ns ≫ the
12.92 ns the portable path needs to do its mul.  The asm savings
(3.6 ns/call) are dwarfed by the bridge cost (~15 ns/call extra
just for the codec).

At ~120 fe25519_mul calls per ed25519_scalarmult (`xyzt_add` 18 muls,
`xyzt_double` 11 muls, 252 ladder steps in the decomposed body), the
extra ~15 ns/call accumulates to ~1.8 ms per sign — consistent with
the observed +140 µs regression (the per-mul bridge gets partially
amortized inside the body's longer chain of ops, but the direction
matches).

## 4. Provability angle

`cryptopt_leaves` does **not** add a new trust assumption — the
CryptOpt-superoptimized asm is verified by CryptOpt's own
`check_equivalence` against fiat-crypto's solinas spec, and the
bridge code is straight-line Rust without new axioms.  So the
*correctness* story is unchanged; the bench just shows there is no
*performance* reason to switch on.

## 5. What would unblock B (for the record)

The asm savings can only be realised if the 5×51 ↔ 4×64 bridge is
eliminated.  Two paths:

1. **Native-4×64 bodies.**  Re-extract the decomposed bodies with
   field-element slot type = 4×u64 saturated.  All fe25519_* ABI
   becomes `*mut u64` (saturated) instead of `*mut u8` (byte slot)
   or fiat 5×51 tight.  Requires:
   - new `fiat_curve25519_solinas_*` add/sub/canon at the leaf level
     (CryptOpt currently only superoptimizes mul/square);
   - re-Rocq the decomposed bodies' correctness against the
     saturated representation (the existing `XyztAddBodyDecomposed.v`
     Qed is over 5×51 tight, not 4×64 saturated);
   - new KAT pass.
   Effort: 1–2 weeks Rocq + extraction, not "1 session" as §1.4
   estimates.

2. **Inline 4×64 in #[inline(always)] body** (parallel to
   `tfp25519_inline_limbs` but for saturated 4×64 instead of 5×51
   limbs).  Keeps the extracted bodies but routes their internal
   field ops through `#[inline(always)]` 4×64 saturated mul/sq that
   stays in registers.  Same Rocq-side caveat as path 1.

Until either path lands, `cryptopt_leaves` should remain an opt-in
build target and NOT be promoted to a default.  The relevant prose
in `docs/performance-and-panic-freeness-2026-05-13.md` §1.4 step B
("~30 % … 1 session") should be revised on its next edit pass to
cite this eval.

## 6. Decision

| Action | Status |
|---|---|
| Code change (default feature flip) | NOT committed — bench-delta-gated rule: ≥5 % win required, observed −33 to −36 % |
| Eval doc (this file) | Committed |
| `cryptopt_leaves` feature itself | Left in place; KAT-passing; opt-in only |

The user-durable rule "If our changes do not improve performance,
record that but don't include them" applies: this eval documents the
falsified prediction, but no Cargo.toml or Rust changes are committed.
