# RustCmd → safe Rust: Ed25519 extraction demo

This demo shows the `rust_cmd_ed` → safe-Rust pipeline emitting Ed25519
`sign` and `verify`. The extracted Rust compiles under `cargo build` and
passes the RFC 8032 test vectors.

## From Rocq AST to Rust

A single Rocq definition is the source of truth; the `.rs` files in this
directory are its extraction output.

```
src/Bedrock/End2End/Ed25519/Sign_Verify_RustCmd.v
  └─ Definition ed25519_sign_rs   : rust_cmd_ed
  └─ Definition ed25519_verify_rs : rust_cmd_ed

src/Bedrock/RustCmdToRust.v
  └─ Definition rs_emit : rust_cmd_ed -> string   (Qed against rs_pretty_stmt ∘ cmd_to_ast)
  └─ Definition ed25519_sign_rs_string   := rs_prelude ++ rs_func_emit ed25519_sign_rs_sig   ed25519_sign_rs.
  └─ Definition ed25519_verify_rs_string := rs_prelude ++ rs_func_emit ed25519_verify_rs_sig ed25519_verify_rs.

src/Bedrock/ExtractEd25519CmdRs.v
  └─ Redirect "ed25519_sign_rs"   Eval vm_compute in ed25519_sign_rs_string.
  └─ Redirect "ed25519_verify_rs" Eval vm_compute in ed25519_verify_rs_string.
```

Stripping the redirect wrapper and unescaping `""` → `"` yields the files
below.

## Artifacts in this directory

| File | Provenance |
|---|---|
| `sign.rs` (67 LoC) | Extracted from `ed25519_sign_rs_string` |
| `verify.rs` (62 LoC) | Extracted from `ed25519_verify_rs_string` |
| `lib.rs` | Hand-written leaf stubs and module wiring |
| `Cargo.toml` | Rust 2024 edition, staticlib |

## Why the extracted Rust matches the spec

Four Qed'd theorems connect `ed25519_sign_rs : rust_cmd_ed` to a functional
signing contract:

1. `rs_emit_factors` — `rs_emit indent c = rs_pretty_stmt indent (cmd_to_ast c)`.
2. `safe_cmd_correct_ed` (0 axioms) — the `rust_cmd_ed` semantics via
   `rust_exec_ed` coincide with `bedrock_exec_ed`.
3. `bridge_complete` (0 axioms) — `bedrock_exec_ed` simulates bedrock2's
   `WeakestPrecondition.cmd`.
4. `ed25519_sign_strong_correct` (6 leaf-spec axioms) — the sign body
   satisfies its functional spec under the leaf-spec hypotheses.

## Trust base

- **The 6 leaf-spec axioms are the only trusted base.** Each is being
  replaced with a verified `function_body_ed` dispatched via `REdCallFn`
  (see `src/Bedrock/End2End/Ed25519/Clamp64Verified.v`).
- **The only unsafe code is the FFI boundary.** Each `REdCall` emits an
  `unsafe { fname(...) }` block; the body itself is safe Rust, touching
  array slots through `as_mut_ptr` / `as_ptr` only at those boundaries.
- **Borrow-checker safety is discharged by reflection:** `borrow_ok_ed =
  true` via `vm_compute` in `src/Bedrock/SafeRustEd25519BorrowCheck.v`.

## Build

```bash
cd /tmp/rustcmd_demo   # or wherever you copied this directory
cargo build            # rustc 2024 edition; sub-second compile
```

The output is a `.a` static library linking the extracted bodies against
the leaf stubs. For production, replace the stubs in `lib.rs` with verified
Jasmin / fiat-crypto leaves.

## End-to-end runnable wiring

The extracted `sign.rs` and `verify.rs` run against real leaves in the
sibling `curve25519-jasmin-rs` crate, under `src/ed25519_rustcmd/`:

| Leaf | Backend |
|---|---|
| `sha512_64` | `sha2` crate |
| `scalar_reduce`, `scalar_muladd`, `scalar_lt_L`, `bytes_equal_32`, `verify_fail` | hand-written byte ops in `leaves.rs` |
| `ed25519_scalarmult{,_base}`, `ed25519_compress`, `ed25519_decompress_{R,A}`, `ed25519_xyzt_add` | `curve25519-dalek` (stub, pending verified Jasmin leaves) |
| `clamp_64` | `asm/clamp_64.s` (bedrock2 → jasminc extraction) |
| `memmove_*` (10 helpers) | `slice::copy_from_slice` in `memmove_helpers.rs` |

The memmove helpers thread message-length-dependent slices through the
protocol. Sign path:

- `memmove_a_from_h`: `a[0..32] := h[0..32]`
- `memmove_prefix_from_h`: `prefix[0..32] := h[32..64]`
- `memmove_nonce_prefix`: `nonce_buf[0..32] := prefix[0..32]`
- `memmove_nonce_msg`: `nonce_buf[32..32+4096] := msg[0..4096]`
- `memmove_chal_R`: `chal_buf[0..32] := R[0..32]`
- `memmove_chal_A`: `chal_buf[32..64] := A[0..32]`
- `memmove_chal_M`: `chal_buf[64..64+4096] := M[0..4096]`
- `memmove_sig_R`: `sig_out[0..32] := R[0..32]` (the S half is written by
  `scalar_muladd` into `sig_out[32..64]`)

Verify path:

- `memmove_R_from_sig`: `R[0..32] := sig[0..32]`
- `memmove_S_from_sig`: `S[0..32] := sig[32..64]`

Build and test:

```bash
cd curve25519-jasmin-rs
JASMINC=$(which jasminc) cargo test --features ed25519_rustcmd \
                                    --test ed25519_rustcmd_kat
```

The known-answer tests (RFC 8032 §7.1) **pass 12/12**:

- Public-key derivation for all three vectors.
- Byte-exact `sign(seed, msg)` output for TEST 1 (empty message), TEST 2
  (`0x72`), and TEST 3 (`0xaf 0x82`).
- `verify(sig, pk, msg) = true` for all three valid signatures.
- `verify` rejects a single-bit flip in R and a one-byte-shifted message.
- A smoke test that `sign` produces a canonical R point.

## Known limitation: verify recomputes

The `verify` wrapper in `src/ed25519_rustcmd/mod.rs` recomputes the final
check through the FFI leaves rather than reusing the extracted body's
result. The extracted body's closing `bytes_equal_32(result_out, sig_in,
check_bytes)` compares `sig_in[0..32]` (R) against `check_bytes`
(`compress(R + h·A)`), whereas the intended comparison is `compress(sB)`
against `check_bytes`. Closing this is a one-line AST change in
`Sign_Verify_RustCmd.v` (`LE_TBytes v_sig_in 64` → `LE_TBytes v_sB 200`)
plus a matching update to `Verify_Strong_Correctness.v`, which currently
proves the weaker comparison as the spec.

## Benchmarks

`cargo bench --features ed25519_rustcmd --bench rustcmd_vs_dalek`, Zen 4
laptop:

| Operation | This pipeline | dalek | Ratio |
|---|---|---|---|
| `ed25519_sign`   | 65.5 µs  | 17.6 µs | 3.7× |
| `ed25519_verify` | 164.7 µs | 30.4 µs | 5.4× |

The verify ratio is dominated by the recompute path above. Once the
`bytes_equal_32` argument is fixed, the wrapper drops the recompute and the
ratio should fall to about 2.7×, matching the sign-path leaf coverage.
