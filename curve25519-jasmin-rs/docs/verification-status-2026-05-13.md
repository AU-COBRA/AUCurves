# Verification status — Signal stack on verified primitives

Snapshot 2026-05-13.

## TL;DR

- **127/127 crate tests pass** under `--features "wnaf_comb_leaves tfp25519_limbs verify_projective_eq"`.
- **4 of 4 Signal protocols** (X3DH, PQXDH, Sender Keys, SPQR) wired through their hax-extracted trait abstractions onto our verified primitives. Double Ratchet connected via a different pattern (haxpipeT pipeline).
- **3 of 4 algebraic-correctness theorems Qed** for the dalek-replacement primitives (Fe25519Invert, Scalar25519FromWide, MontToEdwards). 1 partial (BuildCombTable, ~80% — inner-step admit).
- **Rocq IR** has TArr + REdArrLoad/Store with `safe_cmd_correct_ed` Qed, 0 new axioms beyond `RustcExec_correct`.
- **Lean IR** has TArr + RArrLoad/Store + SExpr + RScalarSetExpr. CombTableInitArrV2 emits 1135B Rust (244× compression).
- **Sender Keys** has CatCrypt scaffold (sorries inside) + new `sender-keys-hax` crate (28 tests pass).

## Layer-by-layer trust set

### Cryptographic primitives

| Primitive | Implementation | Verification status |
|---|---|---|
| X25519 | libjade Jasmin (`x25519_jasmin`, `x25519_jasmin_base`) | EasyCrypt + jasminc Qed (formosa-25519) |
| SHA-256, SHA-512 | libjade Jasmin (`sha256`, `sha512`) | EasyCrypt + jasminc Qed |
| ML-KEM-768 | formosa-mlkem (`mlkem768_keygen/enc/dec`) | EasyCrypt + jasminc Qed |
| Ed25519 (sign/verify) | rust_cmd_ed extracted Window4 + verified xyzt ops + Scalar25519 + Fe25519Invert | Rocq Qed (`Fe25519InvertCorrect.v`, `Scalar25519FromWideCorrect.v`, `Sign_Verify_RustCmd.v`); 12/12 RFC 8032 KATs |
| XEdDSA (`xeddsa_sign_deterministic`, `xeddsa_verify`) | Composed from Ed25519 + Mont→Edwards (`MontToEdwardsCorrect.v` Qed) | Composition correctness inherited; KAT against dalek |
| HMAC-SHA-256, HKDF-SHA-256 | RFC 2104 / 5869 composition over libjade SHA-256 | Composition audit-by-inspection; KAT against RFC test vectors |
| AES-256-GCM | RustCrypto `aes-gcm` 0.10 (hardware AES-NI) | NOT verified — libjade has CTR but no GHASH yet |

### Comb-table init

- Originally: dalek `mul_base × 1024` cells.
- Now (default): ~30 LoC safe-Rust loop on verified `xyzt_add_decomposed` + `xyzt_double_decomposed`. Hand-coded B basepoint constant. KAT'd by 12 RFC 8032 sign+verify tests.
- Optional `lean_emitted_comb_table` feature: 6194-byte Rust emitted from a Lean RustCmd AST. KAT'd against the hand-coded.

### Signal protocol composition

All 4 protocols wired through hax-extracted trait abstractions:

| Protocol | hax crate | Integration test | Tests |
|---|---|---|---|
| X3DH | `signal-hax/x3dh-hax` | `tests/x3dh_with_aucurves.rs` | 3 |
| PQXDH | `signal-hax/pqxdh-hax` | `tests/pqxdh_with_aucurves.rs` | 2 |
| Sender Keys | `signal-hax/sender-keys-hax` (authored this round) | `tests/sender_keys_with_aucurves.rs` | 3 |
| SPQR | `signal-hax/signal-spqr-hax` | `tests/spqr_with_aucurves.rs` | 3 |
| Double Ratchet | `signal-hax/doubleratchet-hax` (toy primitives baked in) | hand-coded `src/double_ratchet.rs` | 5 |

Double Ratchet: the hax crate uses toy primitives (e.g., `dh = XOR`); the production composition is `src/double_ratchet.rs` with verified primitives, following the same algorithmic shape that CatCrypt's `dr_uc_secure` theorem covers (via haxpipeT → `DoubleratchetDeps` → `DRConfig` chain).

## Verified IR extensions (2026-05-13)

### Rocq

- `RustCmdToRustSimulates.v` — single named axiom `RustcExec_correct`, `print_module_preserves_semantics` Qed-trivial consequence.
- `TArr (n : nat) (t : tower_type_ed)` + `VArr` (rust_val_ed).
- `REdArrLoad` / `REdArrStore` (rust_cmd_ed) + `BEdArrLoad` / `BEdArrStore` (bedrock_cmd_ed).
- `safe_cmd_correct_ed` Qed-extends with one-liner cases (`eapply rexec_arr_*; eauto`).
- `RustcExec_correct` remains the SOLE axiom — no new global axioms.

### Lean

- `TArr n t` TowerType + `RArrStore` / `RArrLoad` constructors with runtime-indexed access via scalar-var binding.
- `SExpr` (8 constructors: SVar/SLit/SAdd/SSub/SMul/SShr/SAnd/SLt) + `RScalarSetExpr`. Mirrors Rocq's `sexpr_ed`.
- LeafSpec gains `arrStore`/`arrLoad` oracle fields with identity defaults (back-compatible).
- ppRustCmd printer + rustTowerType updated for new constructors.
- `RustCmdToJasmin.lean` propagated through 14 sites (translate, predicates, induction proofs); new constructors gated out of the simulation theorem's `callFree ∧ whileFree` precondition.

### Lean-emitted .rs files

- `Fe25519Invert.lean` → 2535-byte Rust, KAT'd against hand-coded fe25519_invert in 5 random inputs.
- `CombTableInit.lean` → 277 KB (1024 cells named).
- `CombTableInitArrV2.lean` (using TArr + SExpr) → 1135 bytes (244× compression).
- `ArrayDemo.lean` smoke test for TArr IR.

## Functional correctness proofs (Rocq)

| Theorem | File | Status |
|---|---|---|
| `fe25519_invert_correct` | `Fe25519InvertCorrect.v` | **Qed**, Closed under global context (1222 LoC) |
| `from_wide_correct` (Scalar25519 wide mod L) | `Scalar25519FromWideCorrect.v` | **Qed**, Closed (528 LoC) |
| `mont_to_edwards_correct` | `MontToEdwardsCorrect.v` | **Qed**, Closed (481 LoC) |
| `build_comb_table_correct` | `BuildCombTableCorrect.v` | Partial — outer rfor_invariant Qed, inner-step Admitted (~80% closed, 472 LoC) |

`Print Assumptions print_module_preserves_semantics` shows exactly one axiom: `RustcExec_correct`.

## Open items (ranked)

1. **Close `build_comb_table_correct` inner-step** (~1-2 sessions of unification surgery).
2. **Verified AES-GCM** — GHASH on top of libjade AES-CTR. Multi-session.
3. **CatCrypt Sender Keys** UC proof closure (2 sorries; multi-week hybrid argument).
4. **Lean `rustExecSimulates` full lift** — agent `a642e794bd47a36d7` left a checkpoint lemma + design doc; full theorem rewrite is multi-week.
5. **Verified protobuf marshaler** — replaces `prost` (~2 months CatCrypt work per the dalek-free memory note).
6. **DR via fork** — only relevant if we want trait-based wiring; otherwise DR is already connected via the haxpipeT pipeline + hand-coded production composition.

## Known caveats

- **`xeddsa_sign_deterministic` uses deterministic nonce** (RFC 8032 style). Real Signal XEdDSA uses synthetic random nonce. Functionally equivalent for verify, but reuse-attack-resistance differs (production randomized version still exists as `xeddsa_sign`).
- **Sender Keys deviates from Signal spec on**: XEdDSA vs Ed25519 (trait shape), AAD-on-wire, bounded `MAX_SKIP=2000`, `libsignal_compat` is test-only. Documented in commit `sender-keys-hax: ...`.
- **AES-GCM is the only unverified primitive on the Signal-core trust set**. libjade has CTR; full GCM needs GHASH.
- **Trust localization in Rocq**: `RustcExec_correct` is a named axiom (not a real theorem). Closing this needs a Rocq model of Rust semantics — Aeneas-style transport is the highest-leverage path.
