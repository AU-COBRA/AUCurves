# Jasmin Extraction for `rust_cmd_ed` — Scoping and Plan

*Status: design / scoping (2026-05-12). No production code emitted yet.*

This document scopes "Option C" of the closing-the-gap plan:
extend AUCurves' existing Jasmin extraction infrastructure to accept
`rust_cmd_ed` bodies (the typed AST used to compile Ed25519) and emit
Jasmin source that `jasminc` can compile to optimised x86-64 — with
the Jasmin compiler's correctness theorem covering the lowering.

## 1. Inventory of existing infrastructure

The Jasmin pipeline already exists in AUCurves but is currently fed
from **bedrock2** rather than `rust_cmd_ed`. The pieces:

### 1.1 The local Jasmin AST

`src/Bedrock/Jasmin/Core.v` (2068 LoC) defines a convenience IR
`jasmin_cmd` with constructors covering everything the curve25519 and
BLS12 pairing code needs:

* control flow: `JCskip`, `JCseq`, `JCif`, `JCwhile`, `JCdecl`,
* data flow: `JCset`, `JCstore`, `JCcall`,
* x86 carry-chain intrinsics: `JCadd_flags`, `JCadcx`, `JCmulx`,
  `JCsub_flags`, `JCsbb`,
* types: `JTu64`, `JTptr n`, `JTstack n`.

It also defines `tr_cmd : bedrock2.cmd → jasmin_cmd` with a structural
simulation theorem `tr_cmd_correct` and a deprecated pretty-printer
`to_jasmin_sized` (the text path used to drive `jasminc` in the
X25519-64 pipeline today).

### 1.2 The verified lowering to Jasmin's real AST

`fiat-crypto/src/Bedrock/Field/FieldExtensions/JasminBridgeReal.v`
(currently only present in `_build/`, built from the fiat-crypto
submodule) defines

```
Fixpoint to_jasmin_cmd (c : jasmin_cmd) : Jasmin.expr.cmd
```

which maps `jasmin_cmd` into Jasmin's actual `cmd` (= `seq instr`),
and 17 simulation lemmas (`real_jsem_skip`, `real_jsem_seq`,
`real_jsem_decl`, `real_jsem_set`, `real_jsem_if_*`,
`real_jsem_while_*`, `real_jsem_call`, …) that connect the local
semantics to Jasmin's `psem.sem`. Two axioms remain:
`int_to_ident` and `int_to_funname`, both trivial identity casts
between `Uint63.int` and `Ident.ident`/`funname`. After this point the
Jasmin compiler's own correctness theorem `Compile.compile_correct`
carries the asm down.

### 1.3 The DIRECT `rust_cmd → jasmin_cmd` translator (already in tree)

`src/Bedrock/Jasmin/RustCmdToJasmin.v` (174 LoC) already implements
**Option B** (direct, without going through bedrock2). It translates
the *original* 9-constructor `rust_cmd` (BN254 tower flavour from
`SafeRustSimulation.v`), not the 16-constructor `rust_cmd_ed` of
`SafeRustEd25519Sim.v`. Coverage per constructor is structural
(every `R*` maps to a single `JC*`), the function is total, the
file proves a handful of structural unfolding lemmas, but the
**simulation theorem is deferred** — there is a precise statement
in §5 of that file, including the missing
`rs_to_js : rust_state → jasmin_state` glue function.

### 1.4 The `rust_cmd_ed → bedrock2` bridge

`src/Bedrock/RustCmdToC.v` defines

```
Fixpoint to_bedrock_cmd (c : rust_cmd_ed) : Syntax.cmd
```

mapping all 16 `rust_cmd_ed` constructors into bedrock2 syntax, and
`SafeRustEd25519WPBridge.v` proves the WP-level bridge theorem
`bridge_complete : Qed` (no axioms) connecting `rust_exec_ed` to
`WeakestPrecondition.cmd`.

### 1.5 The CryptOpt-on-Jasmin integration (already in `curve25519-jasmin-rs`)

`build.rs` of the `curve25519-jasmin-rs` crate already drives
`jasminc` on six protocol-level `.jazz` files
(`fe25519_mulx_adcx`, `fe25519_sqr_adcx`,
`scalarmult_cryptopt`, `sha512`, `clamp_64`, `scalarmult`).
A separate code-path (`b2_jasmin_funcs`) runs the bedrock2 →
jasmin_cmd → `to_jasmin_cmd` route and is linked into the same
static library `libcurve25519_jasmin_asm.a`.

The CryptOpt-optimised 4×4 Solinas multiplier lives in
`jazz/cryptopt_mul4.jinc`. It is hand-translated CryptOpt output
written in Jasmin's `inline fn` syntax, **invoked from inside Jasmin
source** (`scalarmult_cryptopt.jazz`); CryptOpt's role is the equivalence
proof against `fiat_curve25519_solinas_mul`, jasminc's role is
register allocation + asm generation.

## 2. Specifying `rust_cmd_ed → Jasmin`

### 2.1 Option A — go through bedrock2

```
rust_cmd_ed
   ↓ to_bedrock_cmd                  (RustCmdToC.v, structural)
 bedrock2.cmd
   ↓ tr_cmd                          (Jasmin/Core.v, tr_cmd_correct Qed)
 jasmin_cmd
   ↓ JasminBridgeReal.to_jasmin_cmd  (17 Qed + 2 trivial cast axioms)
 Jasmin.expr.cmd
   ↓ Jasmin.Compile.compile          (jasminc, mechanised correctness)
 x86-64 asm
```

Every arrow above except the last is already in tree; the last is
the Jasmin compiler's own theorem.

The composition is direct: `(JasminBridgeReal.to_jasmin_cmd ∘ tr_cmd
∘ to_bedrock_cmd) : rust_cmd_ed → Jasmin.expr.cmd`. Verified
end-to-end **up to the gap of `bridge_complete`'s premises** —
`callee_post_wp_compatible` and `all_let_zero_obligations` — which
must be discharged per protocol body, exactly as `Sign_Strong_Correctness.v`
already does for Ed25519 sign.

Net new code: about **40 LoC** (one composition definition, one
extraction directive).

### 2.2 Option B — direct, parallel to `rs_emit`

A new fixpoint `js_emit : rust_cmd_ed → jasmin_cmd` (or directly
to `string` like `rs_emit`) bypasses bedrock2. The existing
`RustCmdToJasmin.v` is exactly this pattern for the old `rust_cmd`;
porting it to `rust_cmd_ed` is a constructor-by-constructor rewrite,
plus a simulation theorem `rj_translate_correct` that does NOT exist
yet (deferred in §5 of that file).

Net new code: **~250 LoC for the translator, plus a multi-hundred-LoC
simulation proof.**

### 2.3 Trade-off

| Criterion | Option A | Option B |
|-----------|----------|----------|
| Reuses Qed bridges already in tree | yes | partial (needs new sim) |
| End-to-end Qed coverage | yes (via bridge_complete) | requires new theorem |
| Output AST shape control | constrained by bedrock2 | direct |
| Code size | ~40 LoC | ~250 + ~600 LoC proof |
| Risk of new axioms | none (all bridges Qed) | new sim proof |
| Aligned with text-deprecation note in `Jasmin/Core.v` | yes | yes |
| Lets us emit x86 intrinsics (mulx/adcx) | only what bedrock2 can express | yes, free |

**Recommendation: ship Option A first** (one composition definition
+ extraction) as a proof of concept, and use Option B later only if a
specific intrinsic (mulx, adcx) is needed at the protocol level — at
which point the right extension is to add the intrinsic to
`bedrock2.bopname`, not to bypass bedrock2.

## 3. CT-preservation guarantee inherited from Jasmin

`Jasmin/proofs/compiler/slh_lowering.v` is the only file in the
Jasmin tree that mentions "constant time"; it is the SLH (selective
load hardening) pass and proves leakage-preservation under a
specific attacker model. **There is no off-the-shelf
"if input is CT then output is CT" theorem for the whole compiler.**

What Option C *does* inherit, end-to-end:

1. **Functional correctness** of the lowering from `rust_cmd_ed`
   semantics to x86-64 instruction semantics, modulo
   `bridge_complete`'s per-protocol obligations and the two trivial
   `int_to_ident` / `int_to_funname` casts in `JasminBridgeReal.v`.

2. **Structural CT-preservation** in the sense that the Jasmin
   compiler does not introduce data-dependent branches or
   data-dependent memory accesses; any CT property of the source
   `rust_cmd_ed` (e.g. `REdSelect` is a branch-free `cmov`) survives
   register allocation and asm emission, because the Jasmin compiler
   never re-introduces a conditional move from a branch.

3. **No new sources of timing leaks** at the boundary, because the
   per-leaf calling convention is pointer-passing and the asm leaves
   stack slot layout decisions to `jasminc`'s verified passes.

What Option C **does not** inherit:

* A formal "no secret leakage" statement at the asm level. That
  would require a CT property on `rust_cmd_ed` first (a
  noninterference predicate on `rust_exec_ed`), threaded through
  `bridge_complete`, `tr_cmd_correct`, `to_jasmin_cmd`. None of
  these intermediate steps currently mention leakage.

* Coverage of the Spectre/SLH layer; SLH would have to be enabled
  explicitly in the Jasmin compile flags.

Net: Option C gives **verified functional correctness** plus
**structural CT preservation by construction**. A separate
noninterference proof on `rust_cmd_ed` is the natural follow-up.

## 4. Per-constructor work for `rust_cmd_ed`

The 16 constructors of `rust_cmd_ed` and their status under Option
A (composition via `to_bedrock_cmd`):

| # | Constructor | `to_bedrock_cmd` status | `tr_cmd` status |
|---|---|---|---|
| 1 | `REdSkip` | done, line 339 | `skip` → `[::]`, done |
| 2 | `REdSeq` | done, line 340 | `seq` → `++`, done |
| 3 | `REdLetZero v t body` | done (stackalloc), line 341 | maps to `JCdecl`, done |
| 4 | `REdLetU64 v e body` | done (set; seq), line 343 | done via set + seq |
| 5 | `REdScalarSet v e` | done, line 347 | done |
| 6 | `REdCall fname dst args` | done, line 349 | done (`JCcall`) |
| 7 | `REdIfNz e ct cf` | done, line 354 | done |
| 8 | `REdWhileNz e body` | done, line 356 | done |
| 9 | `REdByteStore loc idx val` | done (store size 1), line 358 | done (`JCstore` width 1) |
| 10 | `REdByteLoad v loc idx` | done (load size 1), line 364 | needs review: `tr_expr` of `expr.load` produces `JEload base 0`, the offset is in the address. Should be fine but worth checking on a 64-bit byte slot. |
| 11 | `REdFor v n body` | done (set; while; sub), line 370 | reduces to existing while case |
| 12 | `REdSelect cond _ _ _` | **stub** (line 385: `cond skip skip`) | unrelated branch — the actual byte-level merge happens at the `rust_cmd_ed` layer via `rs_set_tower_ed`. For the Jasmin path the `REdSelect` must be lowered to an explicit `JCcmov` (currently absent from `jasmin_cmd`) or to a branch-free expression using `JEand`/`JEor`/`JEsub`. **NEW work: ~80 LoC + 1 lemma.** |
| 13 | `REdCallN fname dests args` | done (multi-binder call), line 397 | done (multi-arg `JCcall`) |
| 14 | `REdCallFn fname dst args` | done (same as `REdCall`), line 410 | done |
| 15 | `REdBlock body` | done (transparent), line 416 | done |
| 16 | (`sexpr_ed` constructors: 8 of them, `SVar`/`SLit`/`SAdd`/`SSub`/`SMul`/`SShr`/`SAnd`/`SLt`) | all mapped in `to_bedrock_expr`, lines 317-333 | all mapped in `tr_expr`, except `SMul`, which is missing from `to_bedrock_expr` (line 325 has `SMul` go to `bopname.mul`, fine). |

**Sharpest blocker: REdSelect.** The CT-safe path uses `rs_emit` for
Rust output, which lowers `REdSelect` to a branchless byte-mask merge.
The bedrock2 path stubs this out, meaning **a `rust_cmd_ed` body that
uses `REdSelect` cannot survive the bedrock2 detour and stay CT**.
For Ed25519 sign the canonical use of `REdSelect` is in `cmov5_felems`
(part of `clamp_64` and the scalar-mult ladder).

Fix options:

* **(a)** Extend bedrock2 with a `cmd.cmov` primitive (intrusive).
* **(b)** Lower `REdSelect` directly to a sequence of `REdByteStore`s
  computing `dst[i] = sel * a[i] + (1-sel) * b[i]` over the
  appropriate byte-count, all using `REdByteStore`/`REdByteLoad`
  primitives that *do* round-trip through bedrock2. This is the
  natural normalisation step. ~120 LoC `rust_cmd_ed → rust_cmd_ed`
  rewrite + a correctness lemma.
* **(c)** Mark sigs that use `REdSelect` as Option-B-only and
  introduce `JCcmov` directly.

Recommendation: **(b)** — the rewrite is local, the correctness
lemma is one inversion, and the result re-uses the entire existing
bedrock2-Jasmin path. Add to `RustCmdToC.v` as a pre-pass
`normalize_select : rust_cmd_ed → rust_cmd_ed` and reuse on the
Rust-emit side as a sanity check that the CT property survives.

## 5. CryptOpt integration story

The existing `curve25519-jasmin-rs/jazz/` arrangement is the
template. CryptOpt-optimised leaves are written in Jasmin source
(`inline fn` over `reg u64[4]`) and inlined into the protocol-level
`.jazz` file, e.g. `scalarmult_cryptopt.jazz` calls
`__mul4_cryptopt` from `cryptopt_mul4.jinc`.

For Option C, the protocol body (e.g. `ed25519_sign_rs`) lowers to
`jasmin_cmd` via §2.1, then `JasminBridgeReal.to_jasmin_cmd` produces
a `Jasmin.expr.cmd` containing **only** `Ccall` opcodes for the leaf
field operations. The CryptOpt-optimised leaves live in a separate
`.jinc` and are linked at the Jasmin source level by including the
`.jinc` ahead of the protocol body.

Concretely the build looks like:

1. Rocq emits `ed25519_sign_jasmin.jazz` containing a function
   `ed25519_sign(reg u64[64] msg, reg u64[32] sk, reg u64[64] sig)`
   whose body is just `Ccall` to `fe25519_mul`, `sha512_64`,
   `xyzt_add`, ….
2. The build prepends `jazz/cryptopt_mul4.jinc` (which defines
   `__mul4_cryptopt`) and `jazz/curve25519_field_ops.jazz` (which
   re-exports CryptOpt leaves under their `fe25519_*` names).
3. `jasminc` compiles the combined source to a single asm file
   with CryptOpt-quality inner loops and Jasmin-quality control
   flow.

This is *exactly* the pattern already proven to work for the
X25519-64 pipeline (`build.rs` lines 17, 37–48); the only delta is
adding `ed25519_sign_jasmin.jazz` as an additional driver entry.

## 6. Effort breakdown

| Phase | Deliverable | Estimate |
|---|---|---|
| P0 | One-liner composition `rust_cmd_ed → Jasmin.cmd` (Option A) plus extraction directive for `xyzt_copy_body` (smallest leaf) | 0.5 wk |
| P1 | `normalize_select` pre-pass to keep `REdSelect` CT through the bedrock2 detour, plus correctness lemma | 1 wk |
| P2 | Wire `ed25519_sign_rs` through the composition and emit `ed25519_sign_jasmin.jazz`. Discharge `bridge_complete` premises for sign (already mostly done in `Sign_Strong_Correctness.v`) | 1.5 wk |
| P3 | Plumb `.jazz` into `curve25519-jasmin-rs/build.rs` analogue inside the Ed25519 crate, link against existing CryptOpt leaves | 0.5 wk |
| P4 | Differential testing + bench (Ed25519 sign vs dalek + libjade) | 0.5 wk |
| **Total** | | **~4 wk** |

A noninterference proof on `rust_cmd_ed` (the natural follow-up that
would tighten the CT story from "structural by construction" to
"theorem in tree") is a separate ~3-week project and not on this
plan's critical path.

## 7. Sharpest blocking issues

1. **`REdSelect` lowering** through bedrock2 is currently a stub
   (`cmd.cond skip skip`). Without the `normalize_select` pre-pass
   above, any `rust_cmd_ed` body that uses CT-cmov silently loses
   its CT property at the Jasmin boundary. **Phase P1 above MUST
   land before any clamp-or-ladder body goes through Option C.**

2. **`bridge_complete` premises** (`callee_post_wp_compatible`,
   `all_let_zero_obligations`) are per-protocol-body and currently
   discharged manually in `Sign_Strong_Correctness.v`. For new
   bodies (verify, batch verify) the obligation discharge work
   recurs. No new infrastructure, just authoring cost.

3. **Two trivial `int_to_ident`/`int_to_funname` axioms** in
   `JasminBridgeReal.v`. They are provable by `eq_refl` after
   unfolding `Ident.ident = WrapIdent.t = Cident.t = int`; they
   block a `Print Assumptions` clean report. Closing them is a
   half-day task and would let us claim a fully axiom-free pipeline
   end-to-end.

4. **No formal CT-preservation theorem** in the Jasmin compiler
   tree (only the SLH leakage-preservation lemma in
   `slh_lowering.v`). The pipeline gives *structural* CT
   preservation only. A claim of "Jasmin-CT-preserved" would
   require either citing libjade's empirical claim (timing-cop or
   ct-verif) or running `tis-ct` on the asm output.

5. **CryptOpt integration is at the source-text level**, not at the
   `jasmin_cmd` AST level. This is good (no new pipeline) but means
   the `Ccall` from the extracted protocol body to e.g.
   `__mul4_cryptopt` is resolved by jasminc's frontend, not by
   anything we prove in Rocq. The CryptOpt equivalence proof
   (`asm ≡ fiat_curve25519_solinas_mul`) is separate Rocq work
   inside the CryptOpt tree.

## 8. Estimated effort to land Option C for `ed25519_sign`

Calling on §6 estimates with the §7 risks:

* Best case (REdSelect not on the sign critical path, sign already
  Qed-clean wrt `bridge_complete`): **2 weeks**, P0+P3+P4 only.
* Realistic (need REdSelect normalize, need one round of
  `bridge_complete` obligation polishing on sign): **3-4 weeks**.
* Pessimistic (must extend `jasmin_cmd` with `JCcmov` and the
  bedrock2-side `cmd.cmov`, redo `tr_cmd_correct`): **6-8 weeks**.

For "principled performance closure" — Rocq-verified sign that links
against CryptOpt-optimised field arithmetic and survives `tis-ct`
attestation — the realistic estimate is **4 weeks** assuming one
engineer working roughly full-time on the pipeline, with the
Mathlib/SSReflect/Jasmin/fiat-crypto build environment already set
up.

## 9. Concrete recommended sequence

1. Land §6 P0 as `src/Bedrock/Jasmin/RustCmdEdToJasmin.v` with one
   theorem `rust_cmd_ed_to_jasmin_correct` that is literally
   `bridge_complete` chained with `tr_cmd_correct` chained with
   `to_jasmin_cmd_correct`. Add `XyztCopyJasmin.v` doing
   `Redirect "xyzt_copy.jazz" Eval native_compute in ...`.
2. Verify `jasminc xyzt_copy.jazz -o xyzt_copy.s` produces valid asm.
3. Decide on `normalize_select` (recommended path b above) and
   implement.
4. Wire ed25519_sign through to a `.jazz` and validate that
   linking against `cryptopt_mul4.jinc` produces a working binary.
5. Benchmark against dalek + libjade.

The plan does **not** require any change to the Jasmin compiler,
to fiat-crypto, to bedrock2, or to the CryptOpt tooling. It is
purely AUCurves-internal plumbing on top of bridges that are
already Qed.
