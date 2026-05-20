# Framework-vs-dalek perf gap analysis (2026-05-12)

## Observed numbers (Zen 4, criterion median)

| Variant                          | sign µs | verify µs | sign vs dalek | verify vs dalek |
|----------------------------------|--------:|----------:|--------------:|----------------:|
| dalek upstream                   |   13.43 |     22.28 |          1.0× |            1.0× |
| `dalek_leaves`                   |   26.74 |     58.68 |          2.0× |            2.6× |
| `decomposed_leaves`              |  393.68 |    404.25 |         29.3× |           18.1× |
| `inline_leaves`                  |  394.21 |    402.46 |         29.4× |           18.1× |
| `wnaf_comb_leaves`               |   68.67 |    188.39 |          5.1× |            8.5× |
| `wnaf_comb_leaves + tfp25519_limbs` | **39.6** | **131.4** |    **2.9×** |        **5.5×** |
| `wnaf_comb_leaves + tfp25519_limbs + xyzt_limb_abi` | **29.8** | **103.4** | **2.2×** | **3.6×** |
| `jasminc_leaves`                 |   69.99 |    199.55 |          5.2× |            9.0× |

## End-to-end after Phase 1b + Phase 1a + Phase 4 (2026-05-12)

Bench was under heavy system load (dalek baselines ranged 25→35 µs);
**ratios are stable across runs even under noise** — they're the
reliable signal.

| Config (median ratios over 3 runs)                        | sign  | verify |
|-----------------------------------------------------------|------:|-------:|
| `wnaf_comb_leaves` (byte baseline)                        | 5.29× | 6.42×  |
| `+ tfp25519_limbs` (Phase 1a, auto-extracted window4)     | 2.16× | 3.03×  |
| `+ verify_projective_eq` (Phase 4)                        | 2.21× | 2.75×  |

Cumulative speedup over byte baseline: **2.39× sign, 2.33× verify**.

The verify path under the full optimisation:
  - `comb_scalarmult_base` (sB)        ≈ 13 µs
  - `window4_scalarmult` (h·A)         ≈ 44 µs (auto-extracted, Phase 1a)
  - `ed25519_projective_eq`            ≈ 0.5 µs (vs 2× compress @ 6 µs, Phase 4)
  - decompress R + decompress A + sha512 + scalar_reduce + xyzt_add + memmoves ≈ 25 µs
  - Total                              ≈ 82 µs

vs dalek-native verify at ~25 µs.  Remaining gap ≈ 57 µs.  ~25 µs of
that is per-leaf compress/decompress at protocol entry (which dalek
also pays, but with hand-tuned inlining).  The rest is the
algorithmic gap between window4 + comb vs dalek's optimized
double-scalar mult.

2026-05-12 Phase 4 (`verify_projective_eq` feature): replaces
verify's final `compress(sB) + compress(R+hA) + bytes_equal_32`
with a single `ed25519_projective_eq` leaf (4 cross-muls + 4
canonicalize-to-bytes + compare; ~300 ns) instead of 2 Z⁻¹
chains (~6 µs total).  Predicted ~5–6 µs verify saved.

System load during the bench was heavy (dalek baseline ranged
25→55 µs across runs), so a clean delta is hard to pin.  Direction
is consistently `verify_projective_eq` faster than the Phase 1b
baseline.  All 12 RFC 8032 KATs pass.

2026-05-12 layer-by-layer microbench (`benches/xyzt_micro.rs`):

| Operation                            | Framework | Dalek    | Ratio |
|--------------------------------------|----------:|---------:|------:|
| `xyzt_add_decomposed` (standalone)   |  810 ns   |  151 ns  | 5.4×  |
| `xyzt_double_decomposed` (standalone)|  108 ns   |  152 ns  | **0.71× ✓** |
| `comb_scalarmult_base` (sign path)   | 12.7 µs   | 10.7 µs  | **1.19× ✓** |
| `wnaf_scalarmult` (verify path)      | 43.5 µs   | 27.3 µs  | 1.59× |

The standalone `xyzt_add` ratio is misleading — when inlined inside
`comb_scalarmult_base`, the 64 calls amortize to **~200 ns/add**
(12.7 µs / 64), 4× faster than the standalone measurement because
LLVM pipelines field ops across the loop body.  The standalone bench
crosses a crate boundary and gets no inlining.

`xyzt_double` is **faster than dalek's `P + P`** — dalek doesn't
shortcircuit `add(P, P)` to its private `double` path.  When we
trigger doubling via add-self, dalek runs the projective add.

So **field arithmetic + scalarmult are near-parity with dalek**.
The puzzling 2× sign / 4× verify gap from earlier must come from
elsewhere.

### Verify's shadow-call double-counts ~43 µs

Inspecting `leaves.rs::wnaf_comb_curve_leaves::ed25519_scalarmult`:
the verify path runs the wnaf body BUT discards its output and uses
the dalek-computed result for KAT correctness (the wnaf body's
sign-bit handling is an Admitted gap in the source PoC).  Result:
verify's bench number charges **both** the dalek scalarmult (~27 µs)
and the wnaf body (~43 µs) — ~70 µs of "scalarmult" cost where the
honest framework cost is only the wnaf 43 µs.

Honest framework verify (no double-count): **109 − 27 = ~82 µs** ⇒
**3.3× behind dalek-native** (instead of 4.3×).  The remaining gap
is the genuine wnaf-vs-dalek-scalarmult difference (1.59×) plus
non-scalarmult per-leaf overhead (decompress/compress/sha512/
scalar_reduce/scalar_lt_L/xyzt_add).

### Honest gap summary (post-microbench, 2026-05-12)

  sign:     12.7 µs scalarmult + ~18 µs other = 31 µs framework
            10.7 µs scalarmult + ~3 µs other  = 13.7 µs dalek
            → ~15 µs other-work gap (sha512, scalar_reduce, compress,
              FFI per-leaf)

  verify:   43.5 µs wnaf + 13 µs comb + ~26 µs other = 82 µs honest
            27 µs scalarmult + ~few µs other = 25 µs dalek
            → 16 µs scalarmult gap (wnaf vs dalek alg) + ~22 µs other

The "per-leaf" overhead matters: sign+verify both do ~6 leaf calls
that touch the 200-byte point slot + 32-byte scalar slot + 64-byte
sha output.  Each call crosses the FFI boundary AND does encode/
decode work to materialize a point from a CompressedEdwardsY/
canonical-bytes input.  Dalek keeps points in projective form
end-to-end and never round-trips through 32-byte canonical.

2026-05-12 follow-up: tried a `tfp25519_inline_limbs` prototype —
Rust-level `#[inline(always)]` field ops over `[u64; 5]` slots
inlined into `#[inline(always)]` xyzt_add/double bodies, with
`#[unsafe(no_mangle)] extern "C"` wrappers preserving the symbol
surface for the wnaf_comb body's extern callers.  Bench result:
**31.9 µs sign / 110.8 µs verify — within ~2% bench noise of the
auto-extracted path** (31.2 / 109.5 µs).  Conclusion: under
release+LTO, LLVM already inlines `fiat_25519_carry_mul`
(`#[inline]` in fiat-rust src/curve25519_64.rs:216) and the
`extern "C"` `fe25519_*` wrappers across the crate.  The remaining
2× sign / 4× verify gap to dalek-native is **not** function-call
overhead — it's actual field-arithmetic / scalarmul-algorithm cost.
The `tfp25519_inline_limbs` feature stays in tree as a documented
no-op baseline; downstream callers shouldn't need to enable it.

2026-05-12 update: `tfp25519_limbs` was bundled with `xyzt_limb_abi`
when Step 4 of the plumbing plan landed (auto-extracted bodies from
the retyped Rocq AST replaced the hand-written prototype).  The
intermediate "tfp25519_limbs alone, byte-format 200-byte slot" row
(39.6 / 131.4 µs) is no longer reachable through the current cargo
features — it was a hand-written stepping-stone.  Today the relevant
configs are:

  * `wnaf_comb_leaves` alone — byte path (68.7 / 188.4 µs).
  * `wnaf_comb_leaves tfp25519_limbs` — verified extraction path,
    auto-extracted from `Bedrock/ExtractCurveBodies.v` against the
    `TBytes 40 → TFp25519` retyped `XyztAdd/Double BodyDecomposed.v`.
    Bench (Zen 4, 2026-05-12 post-Step-4): sign 31.2 µs / verify 109.5 µs.
    Matches the hand-written prototype to within bench noise — see
    `docs/tfp25519-plumbing-plan.md` for the order of operations
    that built up to this.

The `xyzt_limb_abi` row adds the typed XYZT slot landed 2026-05-12:
the 200-byte slot is reinterpreted as 5 × [u64; 5] tight-limb tuples
(byte offsets 0/40/80/120/160), eliminating the from_bytes/to_bytes
boundary conversion in `decomposed_bodies_limbs::xyzt_*_decomposed`.
All producers/consumers (`comb_table_lookup`, `decompress_R/_A`,
`compress`) write/read limb format.  Marker bytes (`dst[80] = 1` etc.)
remain format-compatible because byte 0 of a limb chunk equals the
lowest u64 limb = the integer 1.  Additional gain on top of
`tfp25519_limbs`: sign 1.33×, verify 1.27×.  Cumulative gain vs
baseline `wnaf_comb_leaves`: sign 2.3×, verify 1.83×.

The remaining ~2× sign / ~3.6× verify gap to dalek-native is now
dominated by the FFI per-call cost: every `fe25519_*_limbs` is an
`extern "C"` call across the static-lib boundary, so the limbs spill
to memory between ops instead of staying in registers.  Closing this
would mean inlining the field ops into the body (à la `inline_leaves`,
but with limb slots) — i.e., the body itself becomes a `#[inline]`
Rust function and LLVM can pipeline across the whole `xyzt_add`.

The `tfp25519_limbs` row is the limb-typed prototype landed 2026-05-12
(see `tfp25519-plumbing-plan.md` order-of-operations step 2): sign
68.7 → 39.6 µs (**1.77× speedup**); verify 188 → 131 µs (**1.43×
speedup**).  Predicted was 25 µs / 70 µs — actual savings smaller
because the unpack/pack boundary conversion at xyzt_add entry/exit
costs roughly what the per-op conversion used to cost, so the net
improvement is the per-op savings less the boundary cost.  Bigger
relative improvement on sign because comb scalarmult has 64
xyzt_add_decomposed entries vs wnaf scalarmult's ~52 entries + 260
xyzt_double_decomposed entries (verify); doubles unpack 1 point
each, adds unpack 2, so verify has higher boundary churn.

`jasminc_leaves` ≈ `wnaf_comb_leaves` because it only swaps a 200-byte
memcpy leaf. Perf is structural to the framework path, not the choice
of leaf for one node.

## Root cause: byte-canonical FFI between every field op

`benches/fe25519_micro.rs` reports (Zen 4, 2026-05-12):

| Op                                     | ns/op |
|----------------------------------------|------:|
| `fiat5x51_carry_mul_bare`              |  12.2 |
| `fiat5x51_full_shim_mul`               |  42.1 |
| `cryptopt4x64_mul_bare`                |   8.3 |
| `cryptopt4x64_mul_with_5x51_bridge`    |  24.9 |

The byte-canonical shim adds **~30 ns (3.5×) per field op** over a
bare `carry_mul`. Each primitive op pays `fiat_25519_from_bytes`
twice (one per input) + `fiat_25519_to_bytes` once (mod-p reduce on
the output).

`xyzt_add_decomposed` calls 18 primitive field ops + 2 unpack_xyzt5 +
1 pack_xyzt5. So one Edwards add costs:

  ~ 18 × 42 ns + (3 × ~80 ns) = **~1.0 µs** total
  of which ~540 ns is unpack/repack and ~220 ns is actual field math.

Comb scalarmult does 64 such adds → **~35 µs of FFI conversion**
alone, plus 64 × 200-byte cmov copies in Rust (~10 µs of memory
traffic). That accounts for the bulk of `wnaf_comb_leaves`'s 70 µs.

## Decomposed gap

  dalek-native (13 µs) →
  + 14 µs decompress/compress on each leaf call (dalek_leaves: 27 µs)
  + 43 µs byte-canonical FFI hops on each field op (wnaf_comb_leaves: 70 µs)

Both costs are **structural to the verified IR**: the bedrock2 / RustCmd
spec mandates byte-canonical 40-byte field-element slots between every
op; the dalek-leaves path materializes points as `CompressedEdwardsY`
in the first 32 bytes of the 200-byte XYZT buffer and decompresses on
entry.

## What would close the gap

Leaf-swapping alone (the `*_leaves` features) cannot reach parity
with dalek because the per-field-op shim cost is paid regardless of
which leaf provides the underlying mul/sqr.

The fix is the **TFp25519_64 plumbing** noted as open design Q1 in
`SSProve-lean/docs/d4-leaf-inline-jasmin-extraction-plan.md`: introduce
a `TFp25519_64` TowerType that carries 5×u64 (or 4×u64 saturated)
limbs across the typed-slot bridge so `fe25519_mul`'s callers and
callees both see limbs, not bytes. This eliminates ~75% of the gap
from-the-field-op-shim and is bit-correctness preserving (no
representation change in the verified algebra, just in the IR-level
type assigned to "field element").

Order-of-magnitude estimate after TFp25519_64:

  `wnaf_comb` sign:     70 µs → ~20–25 µs (parity range with dalek_leaves)
  `wnaf_comb` verify:  200 µs → ~70 µs    (parity range with dalek_leaves)

Reaching dalek-native (13/22 µs) further requires also keeping points
in unpacked XYZT form across calls (no compress-on-output / decompress-
on-input cycle) — i.e., a typed-slot `TPointXYZT` carrying 5 field
limbs per coord instead of a 200-byte byte slot.
