# Verifying our Rust extraction against external Rust semantics — options

**Status: scoping notes.** Records the decision tree for the
`rust_cmd_ed → emitted .rs → rustc → ASM` trust chain so the work can be
picked up later. Companion to `bedrock2-c-semantics-bridge.md`.

## The two gaps

`rust_cmd_ed` already has Rocq-side functional correctness:
`safe_cmd_correct_ed` (Qed) and `ed25519_sign_strong_correct` (Qed). What
remains untrusted is what happens between *our AST* and the *binary that
runs*:

1. **Printer fidelity.** Does `rs_func_emit : rust_cmd_ed -> string`
   produce a `.rs` source that semantically matches the AST? Today this
   is asserted by the printer's structure (term-by-term emission) but not
   theorem-proved.
2. **Compiler fidelity.** Does `rustc` preserve semantics from `.rs`
   source to ASM? No verified Rust compiler exists end-to-end. (2) is
   essentially out of scope; (1) is the actionable target.

## Candidate semantics — comparison

| Tool | Style | What it gives | Status (2026) | Coupling to our stack |
|---|---|---|---|---|
| **RustBelt / λRust** | Type-system formalization in Iris/Rocq | Type-soundness of safe-Rust core; safety of unsafe abstractions | Mature; active under Rocq 9 | Iris-uniform with RefinedC (deferred); needs a `rust_cmd_ed → λRust` translator |
| **Aeneas** (Inria, Charguéraud's group) | Rust MIR → pure functional program in Lean / Rocq / F\* / HOL | Functional correctness in the target prover | Active; used in HACL\* and CryptoLine-style projects | Existing in-house experience (the deleted `curve25519-aeneas` PoC). Lean output composes directly with CatCrypt. |
| **Verus** (MSR, CMU) | SMT-backed Rust verifier, inline annotations | Functional correctness, total correctness, type safety | Active and growing; used internally for kernel components at Microsoft | Annotation-driven; would need a `rust_cmd_ed.spec → Verus annotations` translator |
| **Creusot** (Inria Paris-Saclay) | Rust → Why3 + SMT backends | Functional correctness via Why3 | Active research | Pattern like Verus, Why3-based; less industrial pull |
| **Prusti** (ETH Zurich) | Viper-based separation logic for Rust | Functional correctness via Viper / SMT | Mature; ETHZ Programming Methodology group | Annotation-based; Viper separation logic for Rust is constrained |
| **Stacked Borrows / Tree Borrows** (Niko Matsakis, Ralf Jung et al.) | Operational aliasing model for unsafe Rust | Memory-model soundness; runs in Miri | Tree Borrows is the 2024+ direction | Not a verifier — a runtime checker. Useful as cross-check, not as proof |
| **Kani** (AWS) | Bounded model checker (CBMC backend) | Bug-finding | Industrial-grade | Different goal: find bugs, not prove |
| **Miri** | Tree-Borrows-aware interpreter | Runtime UB detection | Built into the Rust toolchain | Cheap to add to CI |

## Recommended three-layer stack

### Layer 1 — Miri-on-CI (cheap, immediate)

Add `cargo miri test --features ed25519_rustcmd` to `curve25519-jasmin-rs`'s
CI. Catches UB / aliasing bugs in the emitted code on every commit. Doesn't
prove anything, but raises the floor. ~1 day of work.

### Layer 2 — Aeneas round-trip (medium, ~3–6 months)

Extract emitted Rust → Lean (via Aeneas) → compare with our `rust_cmd_ed`
denotational spec. Closes the printer-fidelity gap functionally.

Why this over RustBelt:
- Existing in-house Aeneas experience.
- Output goes to Lean — composes directly with the CatCrypt side
  (same proofs that verify CatCrypt's Lean code can also reason about
  Aeneas-extracted bodies).
- Strictly stronger than type-safety: gives functional fidelity, which
  is what the paper claims.
- Aeneas's niche (small, allocation-free, no-trait-magic code) matches
  our extracted Rust exactly.

### Layer 3 — RustBelt λRust translation (long term, paper-worthy)

For the rust_cmd paper's strongest claim: `borrow_ok_ed c = true ⇒
rcmd_to_lambda c` type-checks in RustBelt. Replaces "rustc accepts our
code" with a Rocq+Iris theorem. ~6–9 months; PhD-thesis scale.

## Why not Verus / Creusot / Prusti?

For our particular shape — small, `unsafe`-free, single-function bodies
extracted from a known-safe IR — these would work but require writing a
separate spec for each emitted function in Rust syntax. We already have
those specs in Rocq. Aeneas closes the loop in the more natural
direction: extract Rust → already in Lean/Rocq → reuse the existing
spec.

If, however, the goal extends to verifying **hand-written** additions to
the emitted code (e.g., protocol-glue layers in
`curve25519-jasmin-rs/src/x3dh.rs`), Verus becomes attractive — that
code isn't extracted, so Aeneas can't easily compare it to a Rocq spec.

## Aeneas round-trip — concrete sketch

```
ed25519_sign_rs : rust_cmd_ed           ← already in AUCurves Rocq
       │
       │  rs_func_emit (printer, today trusted)
       ▼
ed25519_rustcmd/sign.rs                  ← what we ship
       │
       │  cargo aeneas (extract MIR → Lean)
       ▼
ed25519_sign : ByteList → ByteList → ByteList   ← Lean pure function
       │
       │  prove equality with rust_cmd_ed denotation
       ▼
Theorem: Aeneas-extracted ed25519_sign = denote ed25519_sign_rs

(Composes with `ed25519_sign_strong_correct` to close:
 Aeneas-extracted = rfc8032_ed25519_sign.)
```

Two cross-checks for free:
- If printer drops a step, Aeneas-extracted ≠ denotation — caught.
- If rustc fundamentally misinterprets the emitted code (e.g.,
  re-ordering a side-effecting expression), Miri + the equality theorem
  catch it.

## RustBelt translation — concrete sketch

```
rust_cmd_ed term  + borrow_ok_ed proof
       │
       │  rcmd_to_lambda
       ▼
λRust term + RustBelt type
       │
       │  prove: ⊢ t :ₘ τ  in RustBelt
       ▼
Safety theorem: t has no UB, ownership respected
```

This closes the type-safety side. Combined with the Aeneas round-trip's
functional-fidelity side, the trust chain reduces to RustBelt's
safety theorem + Aeneas's correctness theorem + rustc's compilation.

## Phases (combined recommendation)

| Phase | What | Estimate |
|---|---|---|
| L1.1 Miri CI | Add `cargo miri test` to `curve25519-jasmin-rs` CI; fix any UB it surfaces | 1 day |
| L1.2 Tree Borrows mode | Enable Tree Borrows in the Miri run; ratchet aliasing strictness | 1 day |
| L2.1 Aeneas tooling | Install Aeneas under our toolchain; verify it can extract a hello-world `rust_cmd_ed` body | 1 week |
| L2.2 Aeneas PoC | Extract `ed25519_sign_rs`-produced source through Aeneas; manually compare with `rust_cmd_ed` denotation in Lean | 2–4 weeks |
| L2.3 Aeneas theorem | Mechanize the equality: extracted-Lean = `rust_cmd_ed`-denotation, for the 13-constructor subset | 2–3 months |
| L3.1 RustBelt tooling | Build `lambda-rust` under our Rocq switch | 1 week |
| L3.2 RustBelt translation | `rcmd_to_lambda` translator + soundness proof for 8–10 core constructors | 6–10 weeks |
| L3.3 RustBelt extensions | `RFor`, `RSelect` (CT-cmov as branchless), `RCallN` (tuple), `RCloneCall` (Borrow/Cell pattern) | 4–6 weeks |
| L3.4 RustBelt operational simulation | `rust_exec_ed ↔ λRust steps` for the whole subset | 4–8 weeks |
| L3.5 End-to-end Ed25519 | Apply both L2 and L3 to `ed25519_sign_rs`; combined trust statement | 1–2 weeks |

## Output artifacts

- `Bedrock/AeneasBridge.v` (or its Lean counterpart) — extracted-Rust →
  Lean equality theorem.
- `Bedrock/RustBeltBridge.v` — `rcmd_to_lambda` + type-soundness theorem.
- CI workflow with `cargo miri test` integrated.
- Paper section claiming the combined trust statement.

## Risks

- **Aeneas tooling stability.** Pre-1.0; expect MIR-frontend churn as
  Rust evolves.
- **`unsafe` blocks in emitted Rust.** The `ed25519_rustcmd` extraction
  uses `unsafe extern "C" { ... }` blocks for FFI to the leaf
  primitives. Aeneas doesn't model `extern` calls — these become opaque
  function symbols, which is fine for the round-trip but blurs what
  exactly is verified.
- **RustBelt's lifetime machinery.** Heavyweight even for our
  single-function-bodies usage; expect non-trivial setup.
- **`rust_cmd_ed`'s `RSelect` and `RCallN`** map awkwardly to λRust.
  Each needs an encoding argument.

## Cross-references

- `docs/bedrock2-c-semantics-bridge.md` — the parallel C-semantics track
  (CN/Cerberus). Iris-uniform composition with RustBelt is in the joint
  plan; CN sits in a different logical world but composes at the
  trust-base level.
- `docs/rust_cmd_ed-emit-evaluation.md` — the three current emission
  paths; this document is the "what's beyond the paths" follow-on.
- `docs/rustcmd-paper-section.md` — the rust_cmd paper. The combined
  L2+L3 result is its strongest possible verification claim.

## Decision deferred

The pipeline ships at L0 (no external Rust-side verification) for the
Commitments and Signal papers. L1 (Miri-on-CI) is recommended as the
next concrete step regardless — it's nearly free and catches real bugs.
