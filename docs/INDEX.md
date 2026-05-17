# AUCurves `docs/` — Topical Index

Structured view of the design notes and active plans under `docs/`.
Each entry is one line: filename + scope. For build instructions see
`../README.md` and `../INSTALL.md`.

---

## `rust_cmd_ed` IR + verified extraction

Verified extraction path from a single Rocq AST to safe Rust (and
alternatives), replacing bedrock2-via-C for new protocols.

- `rustcmd-paper-section.md` — paper-section writeup of the verified-extraction
  story.
- `rust_cmd_ed-emit-evaluation.md` — side-by-side evaluation of the three
  verified emission paths.
- `generalized-slot-type-bridge.md` — design for collapsing the per-primitive
  WP bridges into one slot-typed file.
- `rustcmd-demo/README.md` — runnable demo of the `rust_cmd_ed` pipeline.

## Ed25519 / scalar multiplication

- `ed25519-wiring-plan.md` — wiring `ed25519_rustcmd` to verified leaf
  implementations (anchored on `Sign_Strong_Correctness`).
- `sign-rustcmd-body-rewrite.md` — plan to rewrite `ed25519_sign`'s bedrock2
  body as the `rust_cmd_ed` translation directly.
- `scalarmult-verification-plan.md` — refined plan for a verified
  `ed25519_scalarmult_base` body.
- `edwards-xyzt-64bit-port-findings.md` — accumulated findings from porting
  upstream's `EdwardsXYZT64.v` to AUCurves' 64-bit representation.

## Jasmin extraction

Bedrock2 → Jasmin → asm, used for Curve25519 / XEdDSA whole-protocol.

- `jasmin-extraction-plan.md` — scoping and plan for emitting `rust_cmd_ed`
  to Jasmin.
- `whole-protocol-jasmin-plan.md` — scaffolding plan for whole-protocol
  Jasmin emission.
- `libjade-comparison.md` — code/proof survey vs libjade / formosa-25519.

## AES-GCM / symmetric

- `aes-gcm-libjade-plan.md` — survey + foundation plan preceding any
  AES-GCM work.

## Performance / publication material

- `architectural-gap-inventory.md` — inventory of AUCurves and
  `catcrypt-bench` assets that could close the Ed25519 sign perf gap vs
  dalek.

## Source-tree READMEs

The `src/` subtree has its own READMEs co-located with the code:
`src/Bedrock/README.md`, `src/Bedrock/End2End/README.md`,
`src/Bedrock/RustCmdBorrowPlan.md`, `src/Bedrock/RustJasmin.md`,
`src/Bedrock/SafeRustPerformance.md`, `src/Implementations/README.md`,
`src/Implementations/C/BENCHMARK.md`,
`src/Implementations/C/cryptopt/README.md`, `src/Jasmin/README.md`,
`src/Spec/README.md`, `src/Theory/README.md`,
`src/Arithmetic/safegcd/README.md`,
`src/Arithmetic/safegcd/SETUP.md`,
`src/Arithmetic/safegcd/OPTIMIZATION.md`, `tests/README.md`.
