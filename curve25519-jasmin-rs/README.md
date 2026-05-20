# curve25519-jasmin

A Rust runtime for the Signal protocol stack built on **verified Curve25519 /
Ed25519 / X25519 primitives**, with bodies emitted from
[Rupicola](https://github.com/mit-plv/rupicola) (Gallina → bedrock2) and
linked to libjade [Jasmin](https://github.com/jasmin-lang/jasmin)
assembly. This crate is the source from which the **`verified-dalek`**
drop-in is carved (Phase 1 of the dalek-replacement plan); it implements
the full Signal stack — X3DH, Double Ratchet, PQXDH, Sender Keys, SPQR —
dalek-free.

> **Verified, not audited.** The cryptographic primitives below (X25519,
> Ed25519 field/scalar arithmetic, SHA-256/512, ML-KEM-768) carry machine-
> checked proofs of functional correctness and (most) constant-time
> guarantees. **No security audit of this crate has been performed.**
> Do not deploy in production without an independent review of the protocol
> compositions, the FFI boundary, and the unverified glue layers
> (currently: AES-GCM, protobuf marshaling, parts of XEdDSA sign).
> See `docs/verification-status-2026-05-13.md` for the per-layer trust
> footprint.

## What this crate is

- **Verified primitives.** X25519, SHA-256, SHA-512, ML-KEM-768 are libjade
  Jasmin assembly, compiled through the EasyCrypt-verified Jasmin compiler
  (formosa-25519 / formosa-mlkem). Ed25519 sign/verify is auto-emitted from
  the verified `rust_cmd_ed` AST in
  `AUCurves/src/Bedrock/End2End/Ed25519/Sign_Verify_RustCmd.v`; the field
  inversion, scalar arithmetic, and Montgomery→Edwards bodies are
  Rocq-Qed-proven (`Fe25519InvertCorrect.v`,
  `Scalar25519FromWideCorrect.v`, `MontToEdwardsCorrect.v`).
- **Signal stack.** X3DH, Double Ratchet, PQXDH, Sender Keys, SPQR — all
  wired through hax-extracted protocol traits onto these verified
  primitives. zkgroups: MUCMZ MAC + Pedersen-KZG commitments + linear
  Sigma proofs over Ristretto255.
- **Production-grade hygiene.** The production tree is **`panic!`-free**
  (lint-enforced via `#![deny(clippy::unwrap_used, clippy::expect_used,
  clippy::panic, clippy::unreachable)]` at the crate root). A Phase J
  constant-time analyser has been run; remaining CT caveats are documented
  in `docs/timing-resistance-2026-05-13.md`.

## Quickstart — Ed25519 sign/verify

```rust
use curve25519_jasmin::ed25519_rustcmd::{ed25519_sign, ed25519_verify, ed25519_pubkey_from_sk};

let sk: [u8; 32] = /* secret key */ [0u8; 32];
let pk = ed25519_pubkey_from_sk(&sk);
let msg = b"hello, signal";

let sig = ed25519_sign(&sk, msg);
assert!(ed25519_verify(&pk, msg, &sig));
```

X25519 (DH), XEdDSA, and the Signal protocol modules expose similarly
shaped functions; see the per-module docstrings.

## Module map

| Module | What it does |
|---|---|
| `ed25519_rustcmd::{sign,verify}` | Ed25519 sign/verify auto-emitted from the verified `rust_cmd_ed` AST |
| `ed25519_rustcmd::leaves` | Field/scalar/curve leaf functions (Jasmin asm + extracted bodies) |
| (top-level X25519 fns) | `x25519_jasmin`, `x25519_cryptopt`, `x25519_hybrid`, `x25519_bedrock2`, `x25519_fiat_c` |
| `xeddsa` | XEdDSA sign/verify (Signal spec) — verify side is fully verified glue |
| `mont_to_edwards` | Montgomery→Edwards conversion (fiat-crypto only, no dalek) |
| `scalar25519` | Scalar arithmetic mod L (curve25519 group order) |
| `symmetric` | SHA-256/512 (libjade), HMAC, HKDF, AES-256-CBC+HMAC-SHA-256 AEAD |
| `x3dh`, `double_ratchet`, `pqxdh`, `sender_keys` | Signal protocol compositions |
| `zkgroup_demo` | Pedersen-KZG + linear Sigma over Ristretto255 |
| `safegcd`, `safegcd_<curve>` | Const-generic Bernstein–Yang CT modular inversion (libsecp256k1 `secp256k1_modinv64` algorithm; EUROCRYPT 2026 δ₀=1/2 framework) instantiated for p25519, secp256k1, P-224/256/384/521, BN254/256/446, BLS12-381, BLS24-509, BW6-761, Pallas, Vesta |
| `ffi_safe` | Single home for all `extern "C"` declarations and `unsafe` blocks |

Auto-emitted IR bodies (Lean RustCmd or Rocq RustCmdToRust) live next to
their hand-coded equivalents and are KAT'd against them:
`fe25519_invert_emitted.rs`, `build_comb_table_emitted.rs`,
`scalar25519_emitted.rs`, `mont_to_edwards_emitted.rs`.

## Build

```bash
# Default build: Ed25519 sign/verify uses the verified rust_cmd_ed path;
# scalarmult leaves fall back to dalek for perf parity.
cargo build --release

# Paper-grade configuration (replaces all curve leaves with framework bodies):
cargo build --release --features "wnaf_comb_leaves tfp25519_limbs xyzt_limb_abi"

# Run the full test suite:
cargo test --release
```

The build script (`build.rs`) shells out to `jasminc`, `as`, and `nasm`.
Set `JASMINC=/path/to/jasminc` if it isn't on `PATH`. The crate links
against vendored libjade .jazz files in `jazz/` and CryptOpt assembly in
`asm/`.

### Key cargo features

| Feature | Effect |
|---|---|
| `dalek_leaves` (default) | Curve leaves backed by `curve25519-dalek` (perf baseline) |
| `decomposed_leaves` | Curve leaves from the framework's decomposed bodies |
| `wnaf_comb_leaves` | Sign through verified comb-table, verify through verified wNAF |
| `tfp25519_limbs` | Typed [u64; 5] limb ABI on the 200-byte XYZT slot |
| `verify_projective_eq` | Skip final inversion in verify (projective equality check) |
| `lean_emitted_*` | Link IR bodies emitted from Lean RustCmd ASTs (KAT'd against hand-coded) |
| `aes_gcm_legacy` | Re-enable the AES-256-GCM AEAD path (default runtime is AES-CBC+HMAC) |
| `aes_gcm_libcrux` | Route legacy AES-GCM through libcrux HACL bindings |

See `Cargo.toml` for the full inventory and the feature-implication graph.

## Test layout — 121+ tests, 197 KAT cross-checks

| File | Coverage |
|---|---|
| `tests/kat_vectors.rs` | 197 KAT cross-tests: byte-equality against `ed25519-dalek` and `x25519-dalek` reference outputs |
| `tests/ed25519_rustcmd_kat.rs` | RFC 8032 §7.1 vectors against the `rust_cmd_ed`-extracted sign/verify path |
| `tests/spec_validation.rs` | Specification-conformance checks (RFC 7748, RFC 8032, Signal XEdDSA) |
| `tests/{x3dh,pqxdh,sender_keys,spqr,double_ratchet}_with_aucurves.rs` | Per-protocol integration tests through the hax-extracted traits |
| `tests/signal_stack_end_to_end.rs` | End-to-end Signal session: handshake → ratchet → message exchange |
| `tests/xeddsa_integration.rs` | XEdDSA sign/verify; KAT against dalek's reference |
| `tests/zkgroup_*.rs` | zkgroup MUCMZ MAC + Pedersen-KZG; Tier A always-on, Tier B byte-cross-check against libsignal-zkgroup under `--features upstream-signal` |

Unit tests inside `src/` add coverage on individual primitives (field
arithmetic, scalar arithmetic, AEAD primitives, Lean-emitted bodies
vs hand-coded round-trips).

## Performance

Measured on Zen 4, `taskset -c 0`, criterion median (per-signature
Ed25519). See `docs/performance-and-panic-freeness-2026-05-13.md` for the
full table and the same-run dalek ratios.

| Configuration | Sign | Verify | vs dalek (sign) |
|---|---:|---:|---:|
| dalek upstream | 13.4 µs | 22.3 µs | 1.0× |
| `wnaf_comb_leaves + tfp25519_limbs + xyzt_limb_abi` (headline) | **29.8 µs** | **103 µs** | 2.2× |
| `+ verify_projective_eq` | 29.8 µs | ~82 µs | 2.2× |

Under load (`load average ~ 8/16`), sign drifts to ~36–40 µs; the
same-run ratio against dalek stays in the 1.7–2.2× band. X25519 (DH),
SHA-256/512, HMAC, HKDF, and ML-KEM-768 are within a few percent of the
best hand-tuned implementations on the same hardware.

Multi-curve modular inversion (Bernstein–Yang divstep) is 4–19× faster
than the constant-time Fermat addition chains shipped by k256, p256,
p384, and pasta_curves, and within 14 % of `blst`'s hand-tuned x86_64
assembly on BLS12-381 Fp. Full table: [benchmark.md](benchmark.md).

## Trust footprint

The **verified** trust set:

- **X25519, SHA-256, SHA-512, ML-KEM-768** — EasyCrypt + jasminc (libjade
  / formosa-25519 / formosa-mlkem).
- **Ed25519 sign/verify** — Rocq Qed (`Sign_Verify_RustCmd.v` +
  `safe_cmd_correct_ed`); 12/12 RFC 8032 KATs.
- **Fe25519 invert, Scalar25519 from-wide, Mont→Edwards** — Rocq Qed
  (algebraic correctness over the field/scalar specs).
- **Protocol compositions** — UC proofs in `SSProve-lean/CatCrypt/`
  for X3DH (`x3dh_uc_secure`), Double Ratchet (`dr_uc_secure`), PQXDH
  (`pqxdh_uc_secure`), Sender Keys (sorries inside), SPQR
  (`spqr_uc_secure`).

The **unverified** glue still in tree:

- **AES-256-GCM** (when `aes_gcm_legacy` enabled) — RustCrypto `aes-gcm`
  0.10. The default runtime AEAD has migrated to AES-256-CBC +
  HMAC-SHA-256 over the verified hash chain (`docs/aes-gcm-to-cbc-hmac-2026-05-13.md`).
- **Protobuf marshaling** (`prost`) — Signal wire format.
- **`RustcExec_correct`** named axiom — single Rocq axiom localizing
  trust in `rustc` itself (Aeneas-style closure is the highest-leverage
  follow-on).
- **XEdDSA sign side** — `ED25519_BASEPOINT_TABLE` scalarmult + compress
  still go through dalek; replacement via decomposed bodies is wired
  but feature-gated.

## Relationship to `verified-dalek`

`verified-dalek` is the **carved, packaged form** of this crate. The
relationship is:

```
curve25519-jasmin/   ──(Phase 1: subset extraction)──>  verified-dalek/
  (this crate)                                            (drop-in)
  - full Signal stack                                     - dalek-API-shaped
  - libjade FFI + IR bodies                               - same verified core
  - protocol modules                                      - no Signal-stack glue
```

The Phase 1 carve preserves the verified field/scalar/curve core
(`ed25519_rustcmd::leaves`, `mont_to_edwards`, `scalar25519`,
`x25519_*`, `symmetric::sha{256,512}`) and re-exposes it under the dalek
API surface so existing `curve25519-dalek` / `ed25519-dalek` consumers can
drop-in upgrade. The Signal-stack modules (`x3dh`, `double_ratchet`,
`pqxdh`, `sender_keys`, `zkgroup_demo`) stay in this crate.

## Cross-references

- **Rocq proofs (primitives + Ed25519 IR):** `AUCurves/src/Bedrock/End2End/Ed25519/`
- **Lean proofs (CatCrypt protocol UCs + RustCmd IR):** `SSProve-lean/CatCrypt/`
- **Verification status (per-layer trust):** `docs/verification-status-2026-05-13.md`
- **Performance:** `docs/performance-and-panic-freeness-2026-05-13.md`
- **Constant-time audit:** `docs/timing-resistance-2026-05-13.md`
- **Dalek-free signing notes:** `docs/dalek-free-signing-2026-05-12.md`
- **AEAD migration (GCM → CBC+HMAC):** `docs/aes-gcm-to-cbc-hmac-2026-05-13.md`
- **Hax-extracted Signal traits:** `signal-hax/{x3dh,pqxdh,sender-keys,doubleratchet}-hax/`,
  `SSProve-lean/signal-spqr-hax/`

## License

Dual-licensed: MIT OR Apache-2.0.
