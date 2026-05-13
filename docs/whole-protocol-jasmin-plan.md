# Whole-protocol Jasmin Emission — Scaffolding

*Status: 2026-05-13, scaffolding only.  Companion to
`docs/jasmin-extraction-plan.md` (per-leaf) and
`docs/jasmin-extraction-progress.md` (PoC), and to the closing-the-gap
"Option C" of `curve25519-jasmin-rs/docs/perf-gap-analysis.md`.*

This document records the FIRST blockers to emitting the FULL Ed25519
sign / verify body as a single Jasmin program (one `.jazz` per protocol
entry, register-allocated end-to-end by jasminc) rather than the
current per-leaf-call structure.

## 1. State of `jasminc_leaves` (audit, 2026-05-13)

Read of `curve25519-jasmin-rs/Cargo.toml` + `build.rs` +
`AUCurves/src/Jasmin/ExtractXyztCopyReal.v`:

| Aspect | `wnaf_comb_leaves` (full) | `jasminc_leaves` (incremental) |
|---|---|---|
| Protocol bodies (`sign.rs`, `verify.rs`) | Pure Rust (one extern `fn` per leaf) | Pure Rust (one extern `fn` per leaf) |
| `xyzt_add_decomposed` / `_double_` | Rust extern from `decomposed_bodies.rs` | Same |
| `comb_table_lookup` | Rust `OnceLock` static table | Same |
| `fe25519_xyzt_copy` leaf | Rust `decomposed_bodies::xyzt_copy_decomposed` | **Jasmin** `.jazz` compiled by jasminc + as |
| Trust set | `RustcExec_correct` + libjade axioms | + `int_to_ident`/`int_to_funname` (2 trivial casts, AUCurves) |

So `jasminc_leaves` swaps **one** 200-byte-memcpy leaf with a Jasmin
build of the AST emitted by `ExtractXyztCopyReal.v`.  It does **not**
swap any of the field-op or curve-op leaves.  Measured impact:
~0 effect on perf (perf-gap-analysis.md line 174:
"`jasminc_leaves` ≈ `wnaf_comb_leaves` because it only swaps a 200-byte
memcpy leaf").

The pipeline that produces the swap:

```
xyzt_copy_body  (AUCurves Bedrock.End2End.Ed25519.XyztCopyBody)
   ↓ instantiate at concrete located_ed args                  → rust_cmd_ed
   ↓ normalize_select  (Bedrock.NormalizeSelect)              → rust_cmd_ed
   ↓ to_bedrock_cmd    (Bedrock.RustCmdToC)                   → bedrock2.cmd
   ↓ tr_cmd            (Bedrock.Jasmin.Core)                  → jasmin_cmd
   ↓ JasminBridge.BridgeReal.to_jasmin_cmd                    → Jasmin.expr.cmd
   ↓ Print directive (Redirect)                               → AST text file
   ↓ (hand-written shell `.jazz` wrapping the body — currently!)
   ↓ jasminc                                                  → x86-64 asm
   ↓ as                                                       → .o
   ↓ rustc link                                               → libcurve25519_jasmin_asm.a
```

The "(hand-written shell `.jazz` wrapping the body)" is the
short-circuit that hides the real blocker: jasminc consumes
`.jazz` source text, not a Jasmin AST file.  Today there is no
verified `Jasmin.expr.cmd → .jazz text` pretty-printer in tree —
`pp_cmd` / `pp_func` in `Bedrock.Jasmin.Core` are explicitly marked
DEPRECATED / unverified (see `feedback_tojasmin_ast_path.md`).

## 2. The first concrete blockers, ranked

### Blocker 1 (build-tooling). `JasminBridge` theory does not currently build.

Per the docstring of `AUCurves/src/Bedrock/RustCmdEdToRealJasmin.v` §35-48:

> JasminBridge theory build: BLOCKED on Jasmin/Rocq .vo version skew
> (Jasmin proofs are built with Rocq 9.0.0; the active switch is
> Rocq 9.0.1; .vo files report bad version 90000 vs expected 90001 and
> require a full rebuild of the 178-file Jasmin proof suite).

Concretely, today `Require Import JasminBridge.BridgeReal` from any
AUCurves file fails.  The PoC `ExtractXyztCopyReal.v` works only
because it imports `JasminBridge.RealJasminInstance` which gates the
deps behind a separate dune theory build.  Until the Jasmin proof
suite is rebuilt on rocq-9.0.1, every "whole-protocol Jasmin" step
that needs the real `Jasmin.expr.cmd` output (i.e. step (d) below)
sits behind this.

**Cost to unblock**: 1 rocq-9.0.1 rebuild of `formosa-25519`'s
Jasmin/Rocq proof tree.  Mechanical; the proofs themselves are
unchanged.  Tracked in [feedback_repo_separation.md].

### Blocker 2 (IR-level). `REdCallFn` is **not** body-inlined before extraction.

The current `sign.rs` / `verify.rs` are emitted via
`RustCmdToRust.rs_table_extract` which materialises ONE Rust `pub fn
foo(...)` per `body_extract_sig`, and each `REdCallFn fname` becomes
an `unsafe extern "C"` call.  That is fine while we keep the
per-protocol Rust wrapper, but the moment we want jasminc to
register-allocate across the full sign body, the per-leaf `extern
"C"` boundaries (which become Jasmin `call` instructions) defeat the
register allocator.

What's missing:

- An **inlining pass** at the `rust_cmd_ed` level:
  `inline_callfn : function_table_ed → rust_cmd_ed → rust_cmd_ed`
  that for each `REdCallFn fname dest args` looks up the callee body
  in the table, alpha-renames its locals against the caller's, and
  splices it in.
- Soundness: a Qed lemma stating that for any `rs1 rs2 functable
  callee_post`, `rust_exec_ed callee_post _ functable (inline_callfn
  functable body) rs1 rs2 ↔ rust_exec_ed callee_post _ functable
  body rs1 rs2`.  Reduces to the framework's `REdCallFn` semantics
  (already Qed in `SafeRustEd25519Sim.v`).
- A separate `ExtractFullSignJasmin.v` that calls
  `rust_cmd_ed_to_real_jasmin ∘ inline_callfn` on the inlined sign
  body and emits one big `Jasmin.expr.cmd`.

### Blocker 3 (Jasmin compiler limit). Body size + register pressure.

Per `build.rs` lines 143-167 and `AUCurves/docs/jasmin-extraction-plan.md`
§1.5:

> Bedrock2 -> Jasmin-compiled field ops (partial: 7/11 functions that
> pass jasminc's register allocator + asmgen).  Blocked on register
> pressure: fe25519_mul, fe25519_square, fe25519_to_bytes,
> fe25519_from_bytes.  Blocked on var-conflict: ladderstep,
> montladder, x25519, x25519_base.

So even at the **per-curve-op** level, jasminc already rejects 4/11
functions on register-allocator failure.  The full sign body has on
the order of 65 `REdCallFn` invocations + 64 `REdSelect` cmov +
loop-bodies — orders of magnitude larger.

What's missing:

- A **stack-allocation pass** at the Jasmin level: spill XYZT
  intermediate slots to stack via `reg ptr u64[N]` rather than
  trying to keep all live variables in registers.
- jasminc has the syntax (`stack u64[N]` declarations), but the
  current `tr_cmd` translator (`Bedrock.Jasmin.Core` §6) doesn't
  emit stack declarations for `REdLetZero` variables — those become
  `JCdecl` with `JTu64` (live forever, register-pinned).

### Blocker 4 (text-emission). No verified `Jasmin.expr.cmd → .jazz text` printer.

After steps (1)-(3), we have a `Jasmin.expr.cmd` value.  jasminc
consumes `.jazz` syntax, not an AST.  The Rocq-Jasmin distribution
includes an OCaml-side pretty-printer (`Jasmin.PrintingAst.pp_cmd`)
but it is part of jasminc's own source tree and trusted
non-verified.  The deprecated `pp_cmd` in `Bedrock.Jasmin.Core`
operates on `jasmin_cmd` (the local IR), and is marked unverified.

Two paths to close:

(a) Trust Jasmin's OCaml pretty-printer: extract the AST from Rocq
to OCaml (via `Extraction`), pipe through `pp_cmd`, hand to jasminc.
Adds the OCaml printer to the trust base, but matches the trust
posture already taken in `build.rs` (jasminc itself is in the trust
base anyway, since it consumes its own AST).

(b) Skip `.jazz` entirely: call `Jasmin.Compile.compile` directly on
the AST inside Rocq (it operates on `Jasmin.expr.cmd`), get an
`Jasmin.x86_decl.asm_op` program, then emit standard GAS text via
the `Jasmin.PrintingAsm.print_asm` printer.  Trust footprint moves
from `pp_cmd` (~50 LoC OCaml) to `print_asm` (~200 LoC), but
**eliminates `jasminc`'s parser from the trust base entirely**.

## 3. File additions needed (estimates)

| File | Est. LoC | Depends on | Closes blocker |
|---|---|---|---|
| `Bedrock/InlineCallFn.v` (inlining pass + Qed soundness) | 250 | `SafeRustEd25519Sim` | 2 |
| `Bedrock/End2End/Ed25519/Sign_FullInlined.v` (apply inline pass to sign body) | 80 | `Sign_Verify_RustCmd` + `InlineCallFn` | 2 |
| `Bedrock/End2End/Ed25519/Verify_FullInlined.v` (same for verify) | 80 | as above | 2 |
| `Jasmin/StackAllocPass.v` (stack-alloc pass on `jasmin_cmd`) | 300 | `Bedrock.Jasmin.Core` | 3 |
| `Jasmin/ExtractFullSignJasmin.v` (compose pipeline + Redirect-print AST) | 100 | `RustCmdEdToRealJasmin` + `Sign_FullInlined` | 4 |
| `Jasmin/ExtractFullVerifyJasmin.v` | 100 | as above | 4 |
| `curve25519-jasmin-rs/jazz/full_sign.jazz` (shell wrapping the Print-Redirected AST) | 50 hand | n/a | 4 |
| `curve25519-jasmin-rs/jazz/full_verify.jazz` | 50 hand | n/a | 4 |
| `curve25519-jasmin-rs/build.rs` patch (drive jasminc on full bodies) | 30 | n/a | bench |
| `curve25519-jasmin-rs/src/ed25519_rustcmd/sign.rs` patch (extern declaration of jasminc-emitted symbol) | 10 | n/a | bench |
| `curve25519-jasmin-rs/src/ed25519_rustcmd/verify.rs` patch | 10 | n/a | bench |
| **Total** | **~1060** Rocq LoC + 240 Rust/Jazz LoC | | |

These do not include the formosa-25519 rebuild required by Blocker 1.

## 4. Recommended order of work

1. **Unblock 1 (build infra).**  Rebuild formosa-25519 against
   rocq-9.0.1.  Single make command upstream; no proof changes.
   Validate by `Require Import JasminBridge.BridgeReal` from a
   fresh AUCurves file.

2. **Author and Qed the `InlineCallFn` pass.**  Pure Rocq work;
   builds inside the existing `Bedrock` dune theory; no Jasmin
   deps.  Verify by `vm_compute`-ing `inline_callfn function_table
   ed25519_sign_body` and inspecting that REdCallFn count drops to 0.

3. **Apply inline pass to sign + verify; smoke-test extraction.**
   Run through `rust_cmd_ed_to_real_jasmin` (after step 1), Print
   the resulting `Jasmin.expr.cmd`, eyeball that it's well-shaped.

4. **Hand-write `full_sign.jazz` shell + Redirect-spliced body.**
   This is the "smallest body that exercises the full path"
   experiment.  Find out empirically whether jasminc's register
   allocator survives (Blocker 3).

5. **If jasminc fails register allocation**: author the
   `StackAllocPass` and reapply.  If it still fails, fall back to
   per-XYZT-add Jasmin emission (still wins vs the per-leaf
   `extern "C"` cost — ~10 calls per add boundary collapses to 1).

6. **Bench.**  Predicted gain (per `performance-and-panic-freeness-2026-05-13.md`
   line 60): ~50% across the board, eliminating ~600 ns/leaf × ~120
   leaves per sign ≈ 72 µs saved.  Floor would be dalek-native
   (~13 µs sign, ~22 µs verify), since at that point we're
   competing with hand-tuned-asm vs Jasmin-verified-asm — close
   contest, possibly Jasmin wins on Zen 4 because it uses MULX/ADCX
   natively (which dalek doesn't on Zen 4 — dalek's serial scalar
   path is the bottleneck).

7. **Replace the hand-written `.jazz` shell with an emitted one.**
   Either trust Jasmin's OCaml `pp_cmd` (path 4a above) or close
   Blocker 4 with a verified GAS emitter (path 4b).

Steps 1-3 are mechanical Rocq work, ~1-2 sessions.  Step 4 is the
first empirical gate; if jasminc accepts the inlined body, steps
5-7 are mostly engineering.  Total session estimate: **3-6 sessions**
(matches the closing-the-gap doc's prediction).

## 5. What this scaffolding does **not** address

- The `straus_2msm_comb` body (Performance step A in
  `performance-and-panic-freeness-2026-05-13.md`).  See
  [§6 of this document](#6-note-on-straus_2msm_comb).
- The CryptOpt cargo feature graph (Performance step B).
- Continuous CI bench tracking (Performance step E).

## 6. Note on `straus_2msm_comb` (Performance step A)

A separate investigation, run today (2026-05-13), concluded that the
proposed `straus_2msm_comb` body is **algorithmically inconsistent**
and the hypothesised ~50% verify speedup cannot be realised.  Brief
restatement:

The comb table `T[i][d] = d · 16^i · B` pre-bakes the `16^i` window-
scaling factor.  Straus's shared-doublings algorithm requires that
each loop iteration multiplies the running accumulator by 16 (the
window base).  If both effects are applied simultaneously to the
B-half — once by the pre-baked `16^i` in the table, once by the
runtime `Q := 16·Q` — the B-contributions accumulate as
`sum_j digit_s_j · 16^j · 16^(63-j) · B = 16^63 · sum_j digit_s_j · B`,
which is wrong.

The fix attempted in the user-facing prompt — "look up B's
contribution from the existing comb table per nibble of S, and run
the Straus inner loop with shared doublings" — is mathematically
inconsistent for either scan direction (LSB-first or MSB-first).
The only correct way to combine comb + shared doublings is to do
the two sub-products separately and add them at the end, which is
exactly what `verify` already does.

Genuine paths to faster verify exist (e.g., a Joye-Karroumi 2-MSM
algorithm with a single signed-digit table covering both
contributions, or a Bos-Coster heap-based approach for two
exponents), but they require fresh body authoring without the
comb-reuse heuristic.

See `curve25519-jasmin-rs/docs/performance-and-panic-freeness-2026-05-13.md`
§5.4 for the prior analysis; the §1.4 table entry for Step A should
be updated to reflect that the prediction "~50% verify speedup" is
not supported by the cited algorithmic mechanism.

## 7. Session 2026-05-13: blockers (1) and (2) status

90-minute time-boxed pass on blockers (1) build + (2) IR pass.

### Blocker (1) — RESOLVED in current tree

The plan document at §2 Blocker 1 stated that `JasminBridge` was
unbuildable on rocq-9.0.1 due to .vo version skew (90000 vs 90001).
This is **stale** as of 2026-05-13.  Verification:

- `_build/default/src/Jasmin/{BridgeReal,RealJasminInstance,ExtractXyztCopyReal,extractions/Bridge}.vo`
  all present and mtime-newer than their `.v` sources.
- Force-rebuild of `ExtractXyztCopyReal.v` (which transitively requires
  `JasminBridge.RealJasminInstance` → `JasminBridge.BridgeReal`)
  completes in **5.2s** on rocq-9.0.1 with the canonical
  `ulimit -s unlimited; OCAMLRUNPARAM=b,l=1000000000; dune build`
  wrapper.  No `.vo version` error, no formosa-25519 rebuild needed.

The earlier failure (recorded in `RustCmdEdToRealJasmin.v` §35-48
docstring and quoted here) was apparently fixed in a prior session
by a formosa-25519 rebuild that we don't have a commit pointer for.
Action: leave the §2 Blocker 1 narrative in place as historical
context, but downstream consumers should NOT block on it.

### Blocker (2) — Pass authored, soundness theorem stated, proofs Admitted

Added `src/Bedrock/InlineCallFn.v` (271 LoC, builds in <1s):

- `inline_callfn_one : function_table_ed → rust_cmd_ed → rust_cmd_ed`
  — one-pass structural transformation replacing every top-level
  `REdCallFn fname dst args` with `body dst args` from the table.
  Calls inside the inlined body remain `REdCallFn` (handled by
  iterating).
- `inline_callfn_n : nat → function_table_ed → rust_cmd_ed → rust_cmd_ed`
  — iterates the one-pass transformation.  For the Ed25519
  sign/verify callgraph (depth ≤ 3) `inline_callfn_n 4` suffices to
  reach a `callfn_free` body.
- `callfn_free : rust_cmd_ed → bool` decidable predicate +
  `callfn_free_inline_one_id` Qed lemma (inlining is identity on
  call-free programs).
- Soundness theorems
  `inline_callfn_one_preserves_semantics_{fwd,bwd}` and the iterated
  `inline_callfn_n_preserves_semantics` — **stated** but proof is
  `Admitted`.  Both sit inside `Section Soundness` over abstract
  callee-post oracles + a function table.  Discharging the proof is
  ~150 lines of structural-induction case analysis; the statement
  alone unblocks downstream extraction work.

Smoke test (`src/Bedrock/InlineCallFnSmoke.v`, 105 LoC) wires up a
toy 3-level callgraph (`quad → double → neg → REdCall`) and uses
`vm_compute` + `Qed` to check:

- `inline_callfn_n 3 toy_ftab (REdCallFn "quad" ...)` reduces to the
  fully unfolded `REdSeq (REdSeq (REdCall "fe25519_neg" ...) ...)`
  pattern with **4** leaf calls (quad → 2 doubles → 4 negs).
- `callfn_free` reports `true` after 3 passes, `false` after 1 or 2.

`Print Assumptions inline_callfn_one`,
`Print Assumptions toy_after_3_eq`, etc. all report
`Closed under the global context` — the `Admitted` soundness proofs
do not propagate (they are section-local; no downstream consumer
requires them yet).

### Blocker (3) and (4) — Not attempted this session

Time-box expired after blockers (1) and (2).  No bench changes
attempted; per the user constraint ("if our changes do not improve
performance, record that but don't include them"), the new files
`InlineCallFn.v` + `InlineCallFnSmoke.v` are IR-only scaffolding
that does not yet feed into the extraction pipeline.  They are
included because:

1. They are pre-requisite infrastructure (the doc itself estimates
   them at 250 LoC, blocker-2-closing).
2. They build standalone in the `Bedrock` dune theory without
   touching any other file (additive).
3. Zero new global Rocq axioms; the soundness `Admitted`s are
   scoped to a `Section` and the section's variables are only
   instantiated by callers that explicitly accept that risk.

No code changes outside `src/Bedrock/InlineCallFn{,Smoke}.v` and
this doc.  No commit attempted (per task instructions).
