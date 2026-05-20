# Curve25519 Bernstein–Yang Inversion — Rust / Rocq Cross-Reference

This note documents the relationship between the Rocq specification of
δ₀ = 1/2 Bernstein–Yang inversion mod p25519 and the Rust
implementation in the sibling `curve25519-jasmin-rs` crate.

## Files

| Layer | Path | Notes |
|-------|------|-------|
| Convex-hull framework, δ₀ = 1/2 | `src/Arithmetic/safegcd/divsteps_base_half.v` | INC = 2, `state0_half` at δ_int = 0; reuses `divsteps_base.v` for D, DD, DDSet, ZMap, transitions, convex hull |
| Curve25519 certificate (N = 590) | `src/Arithmetic/safegcd/divsteps590.v` | Proves `ZMap.Empty (N.iter 590 (processDivstep_half p25519) state0_half)` |
| Gallina inverse spec + correctness | `src/Bedrock/Field/Synthesis/Examples/Fe25519_FpInv.v` | Defines `divstep_spec_full_half`, `iter_invariant_half`, `fp_inv_spec`, `fe25519_invert_correct` |
| Rust implementation | `curve25519-jasmin-rs/src/safegcd25519.rs` | 10 outer × 59 inner = 590 divsteps; Wuille zeta encoding; 5×62 signed-limb arithmetic; direct port of libsecp256k1's `secp256k1_modinv64` |

## Algorithmic equivalence

The Rust code uses Pieter Wuille's `zeta = -(δ + 1/2)` reformulation:
- δ₀ = 1/2 ⟺ zeta₀ = -1
- "δ > 0" ⟺ "zeta < 0" (top bit set: `c1 = zeta >> 63`)
- δ ↦ -δ + 1 (swap)        ⟺ zeta ↦ -zeta - 2
- δ ↦  δ + 1 (no swap)     ⟺ zeta ↦ zeta - 1

Rocq's `divstep_spec_full_half (m d f g v r)` (in `Fe25519_FpInv.v`)
uses `d := zeta` directly and exactly matches the Rust update rules at
the abstract Z level. The (f, g, v, r) arithmetic is identical to the
standard δ₀ = 1 `divstep_spec_full` (only the test direction and the
update on `d` differ).

## Iteration count: 590 vs 749 (or 724)

- Bernstein–Yang 2019 (CHES) loose bound for δ₀ = 1: `(49b + 57)/17`.
  For b = 256 this gives `(49·256 + 57)/17 = 738` — and they sharpened
  this further using their proof-bound to a value around 749 for b = 256.
- O'Connor convex-hull-tight bound for δ₀ = 1, b = 256: **N = 724**
  (formalised in `src/Arithmetic/safegcd/divsteps724.v`).
- EUROCRYPT 2026, Theorem 1 (Bernstein–Chen–Harrison–Huang–Maxwell–
  Wang–Wuille–Yang), convex-hull-tight bound for **δ₀ = 1/2**, b = 256:
  **N = 590**.  This is the count formalised in `divsteps590.v` and used
  by the Rocq spec.

Adopting δ₀ = 1/2 yields a ~19 % iteration-count reduction for the same
input width, and that is what libsecp256k1 (and our Rust port) already
implements.

## What is proved

`fe25519_invert_correct` (in `Fe25519_FpInv.v`) is:

```
forall x, 0 < x < p25519 -> Z.gcd x p25519 = 1 ->
  (fp_inv_spec x * x) mod p25519 = 1
```

Its proof is the same template as `BLS12_FpInv.fp_inv_correct_ax`:
1. Loop invariant (`iter_invariant_half`) — proved.
2. Convergence at N = 590 — taken as an axiom
   (`by_convergence_dfg_half`) at parity with the BLS12 file's
   `by_convergence_dfg`.
3. Precomp cancellation `precomp · 2^590 ≡ 1 (mod p)` — proved by
   `vm_compute`.

The certificate in `divsteps590.v` discharges convergence for the
3-field `divsteps.step` algorithm at the convex-hull level; the bridge
from `divsteps.step` (3-field, in `divsteps_def.v`) to the 5-field
`divstep_spec_full_half` used here is the same closing step that
`BLS12_FpInv.v` leaves implicit.  Closing it would discharge the
remaining `by_convergence_dfg_half` axiom and bring `fe25519_invert_correct`
to 0 axioms.

## What is NOT yet proved (`.todo`)

1. **Bridge from `divsteps.step` (3-field) to `divstep_spec_full_half`
   (5-field).**  Required to discharge `by_convergence_dfg_half` and the
   parallel BLS12 axiom.  Structurally identical for both curves;
   bookkeeping over (v, r) only.  An afternoon's work.
2. **Bridge from Gallina `fp_inv_spec` to the Rust safegcd25519 impl.**
   The Rust code does 590 divsteps in 10 outer iterations of 59 inner
   steps each, with constant-time mask-and-merge updates over 5×62
   signed limbs.  Showing that this matches `iter_divstep_spec_half` at
   `Z` level requires:
   - a multi-step transition matrix `Trans2x2` correctness lemma
     (the matrix-times-(f, g) and (v, r) equations from libsecp256k1's
     `modinv64_impl.h:167`),
   - signed-limb-to-Z evaluation correctness for `Signed62`,
   - integer-overflow / range bookkeeping (62-bit limbs, 2^62-scaled
     matrices).
   This is the analogue of `BYInv.divstep_correct_full` for δ₀ = 1/2
   plus the limb-format bridge.  Best done after the 3→5 field bridge
   above lands; the same skeleton applies to both curves.
3. **Constant-time analysis.**  The Rust port preserves libsecp256k1's
   mask-and-merge discipline; a formal CT proof through our existing
   Phase J analyser would mirror what's already proved for
   `fe25519_invert` (Fermat).

## KAT cross-check

The Rust impl is KAT-tested against fiat-crypto's Fermat `fe25519_invert`
in `safegcd25519.rs::tests`; both routes (Fermat 5n + safegcd 590-step)
should agree on every input in [0, p25519).
