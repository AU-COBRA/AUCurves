# AUCurves `docs/` — Topical Index

Structured view of the planning, status, and design notes under `docs/`.
Each entry is one line: filename + scope. For agent operating conventions
see `../AGENTS.md`; for build instructions see `../README.md` and
`../INSTALL.md`.

Snapshot dates are embedded in filenames where present; the most recent
status doc for a topic supersedes earlier ones.

---

## Signal protocol stack

The end-to-end "verified Signal" line: X3DH / PQXDH / Double Ratchet /
Sender Keys / SPQR, wired onto our verified primitives.

- `signal-stack-roadmap-2026-05-13.md` — point-in-time summary of every open
  work item across the Signal stack (roadmap snapshot).
- `signal-stack-status-2026-05-13.md` — proof-and-coverage status for every
  Signal component (post-session refresh).

## Trust / axiom audit

- `trust-audit-2026-05-13.md` — end-to-end `Print Assumptions` audit of every
  axiom that survives in the Rocq stack.
- `trust-audit-2026-05-13-refresh.md` — delta refresh of the audit after the
  post-A16 Tier-1 / Tier-2 closures.
- `axiom-closure-plan-2026-05-13.md` — plan for retiring remaining axioms,
  cross-references the trust audit.

## `rust_cmd_ed` IR + Rupicola framework

Verified extraction path from a single Rocq AST to safe Rust (and
alternatives), replacing bedrock2-via-C for new protocols.

- `rustcmd-rupicola-roadmap.md` — roadmap, plus comparison with CatCrypt's
  Lean RustCmd ecosystem.
- `rustcmd-rupicola-final-status.md` — comprehensive status (2026-05-10) of
  the AUCurves `rust_cmd_ed` framework.
- `rustcmd-paper-section.md` — paper-section writeup of the verified-extraction
  story (consolidated 2026-05-11).
- `rust_cmd_ed-emit-evaluation.md` — side-by-side evaluation of the three
  verified emission paths.
- `bedrock2-vs-rustcmd.md` — architectural comparison: why new Ed25519 (and
  successors) pivot off bedrock2-via-C onto `rust_cmd_ed`.
- `generalized-slot-type-bridge.md` — design for collapsing the per-primitive
  WP bridges into one slot-typed file.
- `wp-bridge-residual-work.md` — residual work items after the parallel
  agent investigation into bedrock2 internals.
- `rustcmd-demo/README.md` — runnable demo of the `rust_cmd_ed` pipeline.

## Ed25519 / scalar multiplication

- `ed25519-wiring-plan.md` — wiring `ed25519_rustcmd` to verified leaf
  implementations (anchored on `Sign_Strong_Correctness`).
- `sign-rustcmd-body-rewrite.md` — plan to rewrite `ed25519_sign`'s bedrock2
  body as the `rust_cmd_ed` translation directly.
- `scalarmult-verification-plan.md` — refined plan for a verified
  `ed25519_scalarmult_base` body (supersedes original Phase 4 estimate).
- `edwards-xyzt-64bit-port-findings.md` — accumulated findings from porting
  upstream's `EdwardsXYZT64.v`.
- `upstream-pr-draft-extended-scalarmult.md` — draft PR adding
  `Extended.scalarmult` + correctness lemma to `mit-plv/fiat-crypto`.

## Jasmin extraction

Bedrock2 → Jasmin → asm, used for Curve25519 / XEdDSA whole-protocol.

- `jasmin-extraction-plan.md` — scoping and plan for emitting `rust_cmd_ed`
  to Jasmin.
- `jasmin-extraction-progress.md` — concrete artefact from Option C PoC.
- `whole-protocol-jasmin-plan.md` — scaffolding for whole-protocol Jasmin
  emission.
- `whole-protocol-jasmin-bench-2026-05-14.md` — runnability + bench of the
  Jasmin-emitted Ed25519 `sign`.
- `libjade-comparison.md` — code/proof survey vs libjade / formosa-25519.

## AES-GCM / symmetric

- `aes-gcm-libjade-plan.md` — survey + foundation plan preceding any
  AES-GCM work (roadmap item #13).

## Performance / benchmarks

- `pipeline-metrics-for-paper.md` — concrete numbers for the paper:
  bedrock2-via-C vs `rust_cmd_ed` direct.
- `architectural-gap-inventory.md` — Ed25519 sign perf-vs-dalek audit of
  AUCurves and `catcrypt-bench` assets that could close the gap.

---

## Cross-references outside `docs/`

Several top-level files in `AUCurves/` are point-in-time planning
snapshots; group them with the relevant topic above:

- Ed25519 / `rust_cmd_ed` planning: `../RUSTCMD_ED25519_PLAN.md`,
  `../R10_RUSTCMD_PORT_PLAN.md`, `../R10_DECOMPOSITION_PLAN.md`.
- Pairing-curves planning: `../PLAN_PAIRING_SPECS.md`,
  `../PLAN_FORMAL_REFINEMENT.md`.
- MSM: `../MSM_NEXT_SESSION.md`.
- Pasta: `../PASTA_COMPLETION_PLAN.md`.
- Performance: `../PERF_OPTIMIZATION_PLAN.md`.
- bedrock2 reflective pipeline: `../BEDROCK2_REFLECTIVE_PLAN.md`.
- Bug tracker + extraction audit: `../BUGS_FOUND.md`,
  `../EXTRACTION_AUDIT.md`.
- Open TODOs: `../TODO.md`.

For agent operating conventions (anti-patterns, build wrapper, common
pitfalls, memory pointers) see `../AGENTS.md`.
