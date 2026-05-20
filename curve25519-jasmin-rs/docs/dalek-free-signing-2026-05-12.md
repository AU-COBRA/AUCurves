# Dalek-free Ed25519/XEdDSA sign+verify (2026-05-12)

Under `--features "wnaf_comb_leaves tfp25519_limbs verify_projective_eq"`,
the Signal-core runtime call graph is now free of `curve25519-dalek` for:

- `ed25519_rustcmd::sign` / `ed25519_rustcmd::verify` (RFC 8032)
- `xeddsa::xeddsa_sign` / `xeddsa::xeddsa_verify`
- X3DH, Double Ratchet, PQXDH, Sender Keys, SPQR (which compose the above)

## What changed

| Layer | Before | After |
|---|---|---|
| Scalar arithmetic mod L | `dalek::Scalar` (`Scalar::from_bytes_mod_order{,_wide}`, `+`, `*`, `-`) | `scalar25519::Scalar25519` over fiat-crypto `curve25519_scalar_64` |
| `scalar_reduce`, `scalar_muladd` leaves | dalek `Scalar` | `Scalar25519` |
| XEdDSA sign basepoint mult | `ED25519_BASEPOINT_TABLE * Scalar` + `compress` | `ed25519_rustcmd::scalarmult_base_compressed` (verified rust_cmd_ed Window4 body + verified compress) |
| XEdDSA verify Montgomery→Edwards | `MontgomeryPoint::to_edwards(0).compress()` | `mont_to_edwards::mont_u_to_edwards_compressed` (fiat-rust only, hand-coded `p-2` chain) |
| Comb-table init | dalek `EdwardsPoint::mul_base` × 1024 cells | verified `xyzt_add_decomposed` + `xyzt_double_decomposed` × ~4046 ops on a hard-coded `B` constant |
| ML-KEM-768 (PQXDH) | RustCrypto `ml-kem` crate | EasyCrypt-verified `formosa-mlkem` Jasmin |

## Verification trust set (active path)

The runtime path now trusts only:

1. **fiat-crypto** (`curve25519_64` + `curve25519_scalar_64`): machine-checked Rocq correctness theorems for the field+scalar arithmetic.
2. **libjade Jasmin** for `sha512`, `sha256`, `mlkem768`: EasyCrypt-verified compiler + EC proofs.
3. **rust_cmd_ed extraction** for `scalarmult{,_base}`, `xyzt_add`, `xyzt_double`, `xyzt_copy`, `ed25519_compress`, `ed25519_decompress_{R,A}`: Rocq-verified `safe_cmd_correct_ed` + `bridge_complete` + `rs_func_emit`.
4. **Hand-coded 32-byte basepoint constant** `B_COMPRESSED_LE` in `leaves.rs::wnaf_comb_curve_leaves`. Public RFC-8032 constant; KAT'd at every run by the RFC 8032 sign+verify suite.
5. **Hand-coded `p-2` addition chain** in `mont_to_edwards::fe25519_invert`. Standard 254-square + 11-mul recipe; KAT'd against dalek on multiple random inputs in unit tests.
6. **Comb-table init loop** in `leaves.rs::build_comb_table` — ~30 LoC of safe-Rust iteration calling verified leaves. KAT'd by RFC 8032 vectors (any miscomputation would fail KAT immediately).

## What still leans on unverified Rust

| Layer | Status | Notes |
|---|---|---|
| AES-256-GCM | RustCrypto `aes-gcm` 0.10 | Hardware-accelerated (AES-NI). libjade has AES-CTR but not full GCM yet. |
| Protocol composition glue | ~300 LoC safe Rust across `x3dh.rs`, `double_ratchet.rs`, `pqxdh.rs`, `sender_keys.rs` | Optimal next step: extract via rust_cmd_ed (CatCrypt has matching protocol specs). |
| protobuf parsing | `prost` 0.12 | Industry standard. Verified-marshaler alternative would be ~1-2 months of CatCrypt work. |
| `zkgroup_demo.rs` | Still uses `dalek::ristretto` | Not on Signal-core path. Replacing needs verified Ristretto255 (~larger effort). |

## Tests

After all swaps, **119 / 119 tests pass** including:

- 12 RFC 8032 §7.1 KATs (full Ed25519 sign+verify, ProductBytes-identical)
- 14 spec_validation tests (X25519 RFC 7748 v1, XEdDSA, SHAKE-256, Elligator2, Ristretto basepoint multiples)
- 42 KAT-vector tests
- 48 lib tests (incl. mont_to_edwards, scalar25519, sym primitives, end-to-end protocols)
- 3 SPQR-with-AUCurves-primitives tests

## Open path: rust_cmd_ed extraction of composition layer

Per user 2026-05-12 (verbatim): *"remember that we have several extraction
paths both rust and jasmin from fiat. And that we can connect code via
rustcmd, which we have both in rocq and in lean. make sure that we take the
optimal route"*.

The optimal next step for the remaining unverified surface is to express
the composition glue (X3DH key derivation, DR state machine, etc.) as
`rust_cmd_ed` ASTs in `AUCurves/src/Bedrock/End2End/Signal/` and emit
them via `RustCmdToRust.rs_func_emit`. CatCrypt already has DR / X3DH
protocol specs in Lean; bridging via the shared `rust_cmd_ed` IR keeps
the trust chain inside the two verified ecosystems.
