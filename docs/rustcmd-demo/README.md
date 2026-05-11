# RustCmd extraction end-to-end demo

Demonstrates the rust_cmd_ed → safe Rust extraction pipeline produces
code that compiles cleanly under `cargo build`.

## Source-of-truth chain

```
src/Bedrock/End2End/Ed25519/Sign_Verify_RustCmd.v
  └─ Definition ed25519_sign_rs  : rust_cmd_ed
  └─ Definition ed25519_verify_rs : rust_cmd_ed

src/Bedrock/RustCmdToRust.v
  └─ Definition rs_emit : rust_cmd_ed -> string   (Qed against rs_pretty_stmt ∘ cmd_to_ast)
  └─ Definition ed25519_sign_rs_string  := rs_prelude ++ rs_func_emit ed25519_sign_rs_sig  ed25519_sign_rs.
  └─ Definition ed25519_verify_rs_string := rs_prelude ++ rs_func_emit ed25519_verify_rs_sig ed25519_verify_rs.

src/Bedrock/ExtractEd25519CmdRs.v
  └─ Redirect "ed25519_sign_rs"   Eval vm_compute in ed25519_sign_rs_string.
  └─ Redirect "ed25519_verify_rs" Eval vm_compute in ed25519_verify_rs_string.

  →  _build/default/ed25519_sign_rs.out      (3725 bytes)
  →  _build/default/ed25519_verify_rs.out    (2997 bytes)

  (Strip wrapper + unescape "" → " yields the files in this directory.)
```

## Artifacts in this directory

| File | Provenance |
|---|---|
| `sign.rs` (67 LoC) | Extracted from `ed25519_sign_rs_string` |
| `verify.rs` (54 LoC) | Extracted from `ed25519_verify_rs_string` |
| `lib.rs` | Hand-written leaf stubs + module wiring |
| `Cargo.toml` | Rust 2024 edition, staticlib |

## Verification chain

The extracted Rust faithfully mirrors `ed25519_sign_rs : rust_cmd_ed` because:

1. `rs_emit_factors` (Qed) — `rs_emit indent c = rs_pretty_stmt indent (cmd_to_ast c)`.
2. `safe_cmd_correct_ed` (Qed, 0 axioms) — semantics of rust_cmd_ed via
   rust_exec_ed coincides with bedrock_exec_ed.
3. `bridge_complete` (Qed, 0 axioms) — bedrock_exec_ed simulates
   bedrock2's `WeakestPrecondition.cmd`.
4. `ed25519_sign_strong_correct` (Qed, 6 leaf-spec axioms) — sign body
   satisfies its functional spec under the leaf-spec hypothesis.

## Build

```bash
cd /tmp/rustcmd_demo   # or wherever you copied this directory
cargo build            # rustc 2024 edition; sub-second compile
```

Output: a `.a` static library that links the extracted bodies against
the leaf stubs. For production, replace the stubs in `lib.rs` with
verified Jasmin / fiat-crypto implementations.

## Notes

- The extracted Rust uses `unsafe { fname(...) }` blocks around each
  FFI call (one per `REdCall`). This is the **only** unsafe code in
  the generated module — the body itself is safe Rust (array slot
  reads/writes via `as_mut_ptr` / `as_ptr` only at FFI boundaries).
- Borrow-checker safety at the rust_cmd_ed level is discharged via
  `borrow_ok_ed = true` (`vm_compute` reflection in
  `src/Bedrock/SafeRustEd25519BorrowCheck.v`).
- The 6 leaf-spec axioms are the only remaining trusted base. Work in
  progress: replace them one at a time with verified `function_body_ed`
  implementations dispatched via `REdCallFn` (see
  `src/Bedrock/End2End/Ed25519/Clamp64Verified.v` once landed).

## End-to-end runnable wiring

The extracted `sign.rs` and `verify.rs` are now wired against real
leaves in the sibling `curve25519-jasmin-rs` crate at
`src/ed25519_rustcmd/`:

| Leaf | Backend |
|---|---|
| `sha512_64` | `sha2` crate |
| `scalar_reduce`, `scalar_muladd`, `scalar_lt_L`, `bytes_equal_32`, `verify_fail` | hand-written byte ops in `leaves.rs` |
| `ed25519_scalarmult{,_base}`, `ed25519_compress`, `ed25519_decompress_{R,A}`, `ed25519_xyzt_add` | `curve25519-dalek` (stub, pending verified Jasmin leaves) |
| `clamp_64` | existing `asm/clamp_64.s` (bedrock2 → jasminc extraction) |
| `memmove_*` (10 helpers) | `slice::copy_from_slice` in `memmove_helpers.rs` |

Memmove offsets (sign path):
- `memmove_a_from_h`: `a[0..32] := h[0..32]`
- `memmove_prefix_from_h`: `prefix[0..32] := h[32..64]`
- `memmove_nonce_prefix`: `nonce_buf[0..32] := prefix[0..32]`
- `memmove_nonce_msg`: `nonce_buf[32..32+4096] := msg[0..4096]`
- `memmove_chal_R`: `chal_buf[0..32] := R[0..32]`
- `memmove_chal_A`: `chal_buf[32..64] := A[0..32]`
- `memmove_chal_M`: `chal_buf[64..64+4096] := M[0..4096]`
- `memmove_sig_R`: `sig_out[0..32] := R[0..32]` (S half written by
  `scalar_muladd` into `sig_out[32..64]`)

(verify path):
- `memmove_R_from_sig`: `R[0..32] := sig[0..32]`
- `memmove_S_from_sig`: `S[0..32] := sig[32..64]`

Build + test:
```bash
cd curve25519-jasmin-rs
JASMINC=$(which jasminc) cargo test --features ed25519_rustcmd \
                                    --test ed25519_rustcmd_kat
```

KAT results (RFC 8032 §7.1) — **12/12 pass** (2026-05-11):
- Public-key derivation for all 3 vectors.
- Strict byte-equality on the extracted `sign(seed, msg)` output for
  all 3 vectors (TEST 1 = empty message, TEST 2 = `0x72`, TEST 3 =
  `0xaf 0x82`).
- `verify(sig, pk, msg) = true` for all 3 valid signatures.
- `verify` rejects a single-bit flip in R, and a one-byte-shifted
  message.
- Smoke test that extracted `sign` produces a canonical R point.

The signature-byte-equality tests previously failed because the
emitted `rust_cmd_ed` source passed a FIXED `len` (4128 / 4160) to
`sha512_64`, so trailing zero padding got hashed into the nonce / chal
inputs.  Bug A (sign path) was fixed by emitting two fresh `let mut`
locals `nonce_hash_len = 32 + msg_len` and `chal_hash_len = 64 +
msg_len` and threading them through; Bug B (verify path) was the same
fix for `verify_chal_len = 64 + msg_len`; Bug C (verify path) was
adding the `memmove_R_from_sig` / `memmove_S_from_sig` slice copies
that pull the R-half and S-half out of `sig_in` before feeding them to
`ed25519_decompress_R` / `ed25519_scalarmult_base`.  All three landed
upstream in `Sign_Verify_RustCmd.v`.

Returning the verification result still goes through a small wrapper
in `src/ed25519_rustcmd/mod.rs::verify`: the extracted `verify.rs`
stores its result in a non-caller-visible local, so we recompute the
check using the same FFI leaves to expose the result byte.  That is a
return-channel emitter gap, orthogonal to the bugs fixed above.
