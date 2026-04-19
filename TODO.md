# AUCurves TODO

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
