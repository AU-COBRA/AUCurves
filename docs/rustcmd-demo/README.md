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
