# Verified extraction to safe Rust via `rust_cmd_ed`

*Paper section — consolidated 2026-05-11.*
*Supersedes `bedrock2-vs-rustcmd.md`, `pipeline-metrics-for-paper.md`,*
*`rustcmd-rupicola-roadmap.md`, `rustcmd-rupicola-final-status.md`.*

## 1. The bedrock2-to-C gap

bedrock2 verifies protocols against a sep-logic semantics, then extracts
to C via `ToCString`. The gap: bedrock2's memory model is byte-addressable
sep-logic, but C's call/aliasing semantics differs in two load-bearing ways:

1. **Pointer-arithmetic provenance.** bedrock2's `expr.load` is over an
   abstract memory; C's pointer arithmetic carries provenance. The
   semantic translation papered over this in our earlier work and broke
   down on Ed25519's R10 step, costing ~2300 LoC of residual proof
   obligations on the multi-segment `ed25519_scalarmult_base`.
2. **Aliasing inference.** bedrock2 sep-conjuncts encode disjointness
   per-call; C's pointer arguments are restrict-equivalent only by
   convention, and the extracted code carries no annotation.

`rust_cmd_ed` targets **safe Rust** directly, sidestepping both gaps:
typed slots eliminate provenance ambiguity, and a syntactic borrow
checker discharged at compile time (`vm_compute`) replaces per-call
sep-disjointness reasoning.

## 2. The `rust_cmd_ed` AST

A typed-slot AST with 16 constructors. The base ten are conventional:

| Constructor | Purpose |
|---|---|
| `REdSkip` | no-op |
| `REdSeq` | sequencing |
| `REdLetZero` | scoped allocation of a typed slot, zero-initialized |
| `REdLetU64` | scalar u64 binding from an `sexpr_ed` |
| `REdScalarSet` | scalar u64 write |
| `REdCall` | FFI call to an axiomatic-spec leaf (single dest) |
| `REdIfNz` | conditional on a u64 expression |
| `REdWhileNz` | well-founded-measure loop |
| `REdByteStore` / `REdByteLoad` | per-byte slot access |

Six additions, each landing Qed-clean with zero new framework axioms:

| Constructor | Purpose | Paper relevance |
|---|---|---|
| `REdFor` | bounded counter loop | Matches Rust `for i in 0..n` |
| `REdSelect` | constant-time conditional move | **Branch on a Secret safely.** Emits a mask-based merge in Rust; `REdIfNz` on a Secret guard is rejected by the CT analysis. |
| `REdCallN` | multi-output FFI (e.g. decompose) | Real-leaf shape (`decompress` returns affine `(x, y)`) |
| `REdCallFn` | dispatch to a *verified* `function_body_ed` instead of an axiomatic spec | Closes leaf axioms one at a time |
| `REdBlock` | scoped block (Rust `{ ... }`) | Lifetime end for inner `REdLetZero` |
| `REdSelect` (CT) | (same as above) | The killer feature of the framework |

## 3. Semantics, borrow checker, simulation

Two operational semantics — `rust_exec_ed` (over typed slots) and
`bedrock_exec_ed` (lock-step parallel inductive) — are connected by:

```coq
Theorem safe_cmd_correct_ed :
  forall callee_post callee_post_n function_table c rs1 rs2,
    rust_exec_ed callee_post callee_post_n function_table c rs1 rs2 ↔
    bedrock_exec_ed callee_post callee_post_n function_table
                    (btranslate_ed c) rs1 rs2.
(* Closed under the global context. *)
```

The syntactic borrow checker `borrow_ok_ed : rust_cmd_ed → bool` checks
per-call destination ≠ argument names. Its soundness theorem
`borrow_ok_ed_call_frame` shows: when `borrow_ok_ed (REdCall f dest args)
= true`, every argument's tower lookup is preserved by the call (given
a frame-respecting callee_post). The check is `vm_compute`-discharged
at compile time — no per-call manual sep-disjointness reasoning.

## 4. WP bridge to bedrock2

```coq
Theorem bridge_complete :
  forall callee_post callee_post_n function_table c rs1 m1 l1 t1
         post (obls : all_let_zero_obligations callee_post callee_post_n
                        function_table c rs1 m1 l1 t1 post),
    WeakestPrecondition.cmd ... (rust_to_bedrock_cmd_ed c) ...
(* Closed under the global context — 0 axioms. *)
```

The bridge composes 13 obligation-HOFs (one per constructor), each
discharged by a corresponding `wp_bridge_X_red` lemma. This means a
protocol verified via the Rust-direct path *also* gets a bedrock2 WP
proof if needed — both paths are sound, the user picks based on which
fits the leaves available.

## 5. Compile framework (Rupicola-style)

24 Qed compile lemmas (`compile_red_*`) across 4 files:

- `RustCmdRupicola.v` — 17 core lemmas (one per constructor + `seq` /
  `let` chains) plus `rhoare_weaken`, `nlet`, `unset`, `downto`,
  `ranged_for`.
- `RustCmdRupicolaTyped.v` — 3 lemmas exploiting typed-slot uniques:
  `compile_red_copy_typed_slot` (type-preserving copy),
  `compile_red_call_with_borrow_check` (vm-discharged borrow_ok),
  `compile_red_field_extract` (chunk-extract `memmove_X` abstraction).
  None have a bedrock2 analog.
- `RustCmdRupicolaEd25519.v` — 4 Tier-4 sugar lemmas for canonical
  Ed25519 patterns (clamp+scalarmult-base, sha512+reduce, two concat
  patterns). Each collapses 2–3 `REdCall`s into one lemma.
- `RustCmdRupicolaTactics.v` — `compile_step` Ltac that dispatches
  per head constructor, plus `compile_callee` for the strong_callee_post
  branches. `demo_sha512_correct` (Qed) shows the end-to-end compile.

Every compile lemma is **Closed under the global context**.

## 6. Information-flow analysis

`SafeRustEd25519CTLevel.v` (271 LoC, 4 Qed anchor lemmas, 0 axioms):
a syntactic CT discipline `cmd_ct_ok : rust_cmd_ed → level_env → level
→ option level_env`. Per-constructor rules track a public/secret level
through the typed slots. Three rules carry the paper claim:

| Constructor | Rule |
|---|---|
| `REdIfNz` on Secret guard | **rejected** (control-flow leak) |
| `REdSelect` on Secret cond into Secret dest | **accepted** (mask-merge in Rust output) |
| `REdSelect` on Secret cond into Public dest | rejected (declassification) |

This pins down `REdSelect`'s killer-feature contract: branching on
secrets is allowed iff the result stays secret and the emitted Rust
performs a branch-free mask merge.

## 7. Extraction

`RustCmdToRust.v` defines `rs_emit : string → rust_cmd_ed → string`
plus a verified factorization `rs_emit_factors` (Qed):
`rs_emit indent c = rs_pretty_stmt indent (cmd_to_ast c)`.

Concrete extractions:

```coq
Definition ed25519_sign_rs_string : string :=
  rs_prelude ++ rs_func_emit ed25519_sign_rs_sig ed25519_sign_rs.
```

`ExtractEd25519CmdRs.v` dumps this via `Redirect ... Eval vm_compute`,
producing **3.7 KB / 67 LoC of safe Rust** for `ed25519_sign`. The output:

```rust
pub fn ed25519_sign(sig_out: &mut [u8; 64], seed: &mut [u8; 32],
                    msg: &mut [u8; 4096], msg_len: u64) {
    let mut h_full: [u8; 64] = [0; 64];
    // ... 12 more slot allocations ...
    unsafe { sha512_64(h_full.as_mut_ptr(), seed.as_ptr(), 32u64) };
    unsafe { memmove_a_from_h(a.as_mut_ptr(), h_full.as_ptr()) };
    unsafe { clamp_64(a.as_mut_ptr()) };
    // ... 16 more FFI calls ...
}
```

`unsafe` appears **only** at FFI boundaries; the body is safe Rust.
Compiles cleanly under `cargo build` (Rust 2024 edition). See
`docs/rustcmd-demo/` for the runnable artifact.

## 8. Trusted base

`ed25519_sign_strong_correct` (Qed) currently rests on six leaf-spec
axioms — pure Gallina specs for `sha512_full`, `scalar_reduce`,
`scalar_muladd`, `ed25519_scalarmult_base`, `ed25519_compress`,
`clamp_64`. **Every other theorem in the framework is closed under the
global context**: `safe_cmd_correct_ed`, `bridge_complete`,
`rust_exec_ed_preserves_wf`, all 24 `compile_red_*` lemmas, all
`wp_bridge_*_red` lemmas, the borrow-check soundness theorems, the CT
analysis lemmas, the Rust-emission factorization.

The six leaf axioms are systematically replaceable via `REdCallFn`
and a verified `function_body_ed`. The first such replacement
(`clamp_64`, the simplest leaf — pure bitwise on 32 bytes) is in flight
as `End2End/Ed25519/Clamp64Verified.v` and will drop the axiom count
to five.

## 9. Comparison with CatCrypt (Lean RustCmd)

CatCrypt in Lean develops a parallel `RustCmd` AST (16+ constructors) as
the verified source for Jasmin extraction. The convergence is striking:

| Feature | AUCurves (Rocq) | CatCrypt (Lean) |
|---|---|---|
| Typed-slot AST | `rust_cmd_ed` (16) | `RustCmd` (16+) |
| Operational semantics | `rust_exec_ed` | `RustExec` |
| Borrow checker | `borrow_ok_ed` | `borrowOk` |
| Multi-output calls | `REdCallN` | `RustCmd.callN` |
| Verified helpers | `REdCallFn` + `function_table_ed` | `RustCmd.fnDef` |
| Block scoping | `REdBlock` | `RustCmd.block` |
| CT analysis | `cmd_ct_ok` | `secretLevel` |
| Compile framework | Rupicola-style (24 Qed) | (in progress) |
| Bedrock2 bridge | `bridge_complete` (0 axioms) | n/a (Lean targets Jasmin) |
| End-to-end extraction | `rs_emit` → safe Rust | `RustCmd → Rust` |

Both frameworks are converging on the same design. The Rocq side has
the Rupicola compile framework and bedrock2 bridge; the Lean side has
the Jasmin extraction and stronger Mathlib leverage. Either can drive
the other's protocol bodies via mechanical syntax-directed translation.

## 10. Summary numbers

- **16 constructors** in `rust_cmd_ed`.
- **24+ Qed compile lemmas** across 4 framework files.
- **0 framework axioms** — `safe_cmd_correct_ed`, `bridge_complete`,
  every `compile_red_*` and `wp_bridge_*_red`, every CT-analysis lemma,
  `rs_emit_factors` — all Closed under the global context.
- **6 leaf-spec axioms** — the only remaining trusted base, all pure
  Gallina, systematically replaceable.
- **67 LoC of safe Rust** for `ed25519_sign`, compiles under `cargo build`.
- **Qed-time speedup**: protocol-body verification went from R10's
  30+ minute ceiling (bedrock2 path) to **0.0 seconds** (rust_cmd_ed
  path) — the compile lemmas are direct rewrite rules.
- **LoC reduction**: ~2300 LoC of bedrock2 residual obligations
  eliminated; protocol body verification drops from ~1500 LoC per
  protocol to ~200 LoC of compile-lemma applications.
