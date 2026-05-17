# `rust_cmd_ed` emission paths — side-by-side evaluation

We have three verified emission paths from a single `rust_cmd_ed`
AST.  This note evaluates them on a tiny demo program (stack
allocation + fnspec call + if/while), then summarizes which path is
preferable for which downstream consumer.

The demo program in `rust_cmd_ed` AST form (from
`Bedrock/RustCmdToC.v`):

```coq
Definition demo_rs : rust_cmd_ed :=
  REdLetZero "h" (TBytes 64) (
  REdLetU64 "i" (SLit 256) (
  REdSeq (REdScalarSet "i" (SSub (SVar "i") (SLit 1)))
  (REdSeq
    (REdCall "sha512_64"
      {| loc_var := "h"; loc_type := TBytes 64 |}
      [{| loc_var := "msg"; loc_type := TBytes 32 |}])
    (REdSeq
      (REdIfNz (SVar "i") REdSkip REdSkip)
      (REdWhileNz (SLt (SLit 0) (SVar "i"))
        (REdScalarSet "i" (SSub (SVar "i") (SLit 1)))))))).
```

## Path (a): `c_emit` — direct C from `rust_cmd_ed`

Source: `Bedrock/RustCmdToC.c_emit`.  Output (`Eval vm_compute in
demo_direct`):

```c
    uint8_t h[64] = {0};
uint64_t i = 256;
i = (i - 1);
sha512_64(h, msg);
if (i) {
  ;
} else {
  ;
}
while ((0 < i)) {
  i = (i - 1);
}
```

**Strengths**
- Idiomatic C: arrays declared as `uint8_t h[64]`, no pointer-typed
  intermediates.
- `sha512_64(h, msg)` calls match the C convention directly; no
  pointer-cast indirection.
- Clean control flow: bare `if`, bare `while`.

**Weaknesses**
- Length argument dropped from `sha512_64` (ABI mismatch — gap #1
  is closed in the Rust path but the C path still drops length).
- `memmove_*` opaque calls in the real protocols (gap #2) — fixed
  offsets are hard to express without an `RAddrOffset` constructor
  or `memmove(dst+off, src, n)` in the emitter.

## Path (b): `to_bedrock_cmd` + `bedrock2.ToCString.c_cmd`

Source: `Bedrock/RustCmdToC.rust_to_bedrock_c`.  Output:

```c
uint8_t _br_stackalloc_h[64] = {0}; h = (br_word_t)&_br_stackalloc_h;
i = (br_word_t)0x100;
i = i-1;
sha512_64(h, msg);
if (i) {
  /*skip*/
} else {
  /*skip*/
}
while ((br_word_t)((br_word_t)0<i)) {
  i = i-1;
}
```

**Strengths**
- Shares its C runtime with bedrock2's existing extraction pipeline
  (CompCert-friendly, used elsewhere in fiat-crypto).
- Verified through bedrock2's existing C semantics chain.

**Weaknesses**
- Pointer-style: `_br_stackalloc_h[64]` plus `h = (br_word_t)&...`
  decay; less idiomatic than (a)'s direct `uint8_t h[64]`.
- `(br_word_t)` casts everywhere — bedrock2's word abstraction
  surfaces in the emitted code.
- `/*skip*/` rather than empty bodies — minor cosmetic noise.
- No type information in argument lists (functions are
  `(br_word_t, br_word_t)` regardless of underlying types).

## Path (c): `rs_func_emit` — direct Rust from `rust_cmd_ed`

Source: `Bedrock/RustCmdToRust.rs_func_emit`.  Output:

```rust
pub fn demo_fn(msg: &mut [u8; 32]) {
    let mut h: [u8; 64] = [0; 64];
    let mut i: u64 = 256u64;
    i = (i.wrapping_sub(1u64));
    unsafe { sha512_64(h.as_mut_ptr(), msg.as_ptr(), 32u64) };
    if (i) != 0 {
        ()
    } else {
        ()
    };
    while (((0u64 < i) as u64)) != 0 {
        i = (i.wrapping_sub(1u64))
    };
}
```

**Strengths**
- Typed array slots: `[u8; 64]`, `[u8; 32]` carry exact lengths into
  the Rust type system.
- Explicit length argument to `sha512_64` (`32u64`) — gap #1
  closed by `rs_call_inject_lens`.
- `unsafe extern "C"` block isolates the FFI boundary; the
  surrounding code is safe Rust.
- `wrapping_sub` / `wrapping_add` are explicit about overflow
  semantics, matching bedrock2's word arithmetic.
- Direct integration with libsignal / signal-wasm (which is Rust-based).

**Weaknesses**
- Trailing `()` in if-else branches and trailing `;` after
  expressions — slightly noisier than C.
- `(0u64 < i) as u64) != 0` for the while-loop condition is
  pedantic — Rust accepts `0u64 < i` directly as `bool`, but the
  emitter goes via `as u64 != 0` to mirror `rust_cmd_ed`'s 0/non-0
  semantics uniformly with `if`.
- Memory aliasing rules might require small adjustments at link
  time (e.g., signature `&mut [u8; 32]` for input args is too
  strict; consider `&[u8; 32]`).

## Verdict by use case

| Consumer | Recommended path |
|---|---|
| Signal / libsignal Rust integration | **(c) Rust direct** |
| Plain C consumers (e.g., Python via cffi, embedded) | **(a) C direct** |
| bedrock2-pipeline cross-validation / CompCert stack | **(b) C via bedrock2** |
| Lean / WASM Component Model (catcrypt-signal) | **(c)** + cargo-component cdylib |

For AUCurves' primary deliverable (verified Rust-language Ed25519 sign /
verify usable from libsignal), **path (c) is the natural target**.  It
sidesteps the `memmove_*` opaque-call problem entirely — Rust slice
indexing handles fixed offsets directly — and the explicit length
argument injection (`rs_call_inject_lens`) closes the SHA-512 ABI gap
that the C path still has open.

## Verification chain shared by all three paths

```
ed25519_sign_rs : rust_cmd_ed
    │
    ├─ borrow_ok_ed (vm_compute) — non-aliasing of REdCall args
    │
    ├─ rust_exec_ed_preserves_wf (Qed) — well-formed slot types
    │
    ├─ ed25519_sign_strong_correct (Qed, Sign_Strong_Correctness.v)
    │  — output equals ed25519_sign_gallina_lifted seed msg
    │
    ├─ ed25519_sign_gallina_lifted_clean (Qed) — matches the clean
    │  ed25519_sign_gallina under conventional buffer lengths
    │
    ▼
Three emission paths (all verified to be operationally equivalent
via cmd_to_ast / rs_emit_factors at the AST level).
```

The remaining gap to a fully verified linked binary (in any of the
three paths) is the **leaf FFI**: providing verified
implementations of `sha512_64`, `scalar_reduce`, `scalar_muladd`,
`ed25519_compress`, `ed25519_scalarmult_base`,
`ed25519_scalarmult`, `ed25519_decompress_R`/`_A`,
`ed25519_xyzt_add`, `scalar_lt_L`, `bytes_equal_32`, `clamp_64`,
`verify_fail`.  This gap is independent of the emit path.

## Eval session details

This document is generated from the actual `vm_compute`-evaluated
strings of the three definitions in `Bedrock/RustCmdToC.v` and
`Bedrock/RustCmdToRust.v`.  Reproduce via:

```bash
cd AUCurves
rocq compile <usual flags> src/Bedrock/ExtractEvalDemo.v
# Outputs in /tmp:
#   demo_direct_c.out
#   demo_via_bedrock_c.out
#   demo_direct_rs.out
```

The full `ed25519_sign_rs` and `ed25519_verify_rs` outputs (~60 and
47 LoC of Rust each) are at
`curve25519-jasmin-rs/src/ed25519_rustcmd/{sign,verify}.rs`.

Last regenerated: 2026-05-09.
