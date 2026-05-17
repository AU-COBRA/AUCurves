# Wiring `ed25519_rustcmd` to verified leaf implementations

`Sign_Strong_Correctness.ed25519_sign_strong_correct` (Qed) closes
correctness at the rust_cmd_ed layer.  The remaining work for an
end-to-end verified linked binary is providing each leaf callee
from a verified source.  This document inventories what's already
available across the sibling repositories and maps each leaf to its
intended supplier.

## Leaf callees (10 callees + 10 memmove helpers)

| Symbol | Type | Source | Status |
|---|---|---|---|
| `sha512_64` | hash | `libjade/proof/crypto_hash/sha512/amd64/ref/` (Jasmin, EasyCrypt-verified) | **available** |
| `clamp_64` | bit-twiddle | already in `curve25519-jasmin-rs` (Jasmin via `clamp_64` in `bedrock2_jasmin` module) | **available** |
| `scalar_reduce` | mod-L reduction | candidate: `libcrux-specs-hax/src/ed25519.rs` or hand-Jasmin in libjade scalar dir | **needs verification** |
| `scalar_muladd` | mod-L `r + k·a` | same as above | **needs verification** |
| `ed25519_compress` | XYZT → 32B | candidate: AUCurves `EdwardsCompressDecompress.v` (4 admits closed) | **AUCurves work-in-progress** |
| `ed25519_decompress_R/_A` | 32B → XYZT | candidate: same AUCurves file | **work-in-progress** |
| `ed25519_scalarmult_base` | scalar·B | candidate: Sign_Verify_RustCmd's R10 path (Sign.v Axiom; needs the bedrock2 bridge) | **AUCurves Axiom + bridge gap** |
| `ed25519_scalarmult` | scalar·P | candidate: extension of R10 | **bridge gap** |
| `ed25519_xyzt_add` | XYZT add | AUCurves `EdwardsXYZT64.v` | **available (Qed pieces)** |
| `scalar_lt_L` | scalar comparison | trivial; hand-verified or from libcrux | **trivial** |
| `bytes_equal_32` | constant-time compare | trivial; can use `subtle` crate or hand-verified | **trivial** |
| `verify_fail` | sentinel callback | hand-defined no-op | **trivial** |

The 10 `memmove_*` helpers are already provided as pure safe-Rust
slice copies in `curve25519-jasmin-rs/src/ed25519_rustcmd/memmove_helpers.rs`.

## Recommended wiring strategy (in order of confidence)

### Phase 1 — Reuse what's already linked

`curve25519-jasmin-rs` already includes Jasmin-compiled
`clamp_64` (5-limb Solinas variant).  Confirm the FFI ABI matches
our `extern "C" fn clamp_64(sk: *mut u8)` declaration; minor
adapter shim if not.  Drops: 1 leaf.

### Phase 2 — SHA-512 from libjade

libjade's amd64-ref SHA-512 is Jasmin source compiled to
amd64 assembly via the EasyCrypt-verified jasminc backend.  Build
artifact in `catcrypt-bench/build/jade_sha512.o`.  Add to
`build.rs` as an `as`-compiled object alongside the existing
Jasmin field ops.  ABI:

```c
void jade_hash_sha512_amd64_ref(uint8_t* h, const uint8_t* m, uint64_t mlen);
```

Adapter in `memmove_helpers.rs`:

```rust
extern "C" {
    fn jade_hash_sha512_amd64_ref(h: *mut u8, m: *const u8, mlen: u64);
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn sha512_64(h: *mut u8, m: *const u8, mlen: u64) {
    unsafe { jade_hash_sha512_amd64_ref(h, m, mlen) }
}
```

Drops: 1 leaf, the most heavyweight.

### Phase 3 — Ed25519 group ops via AUCurves bedrock2 chain

`ed25519_xyzt_add` is the cheapest: `EdwardsXYZT64.v` already has
the addition fn body verified.  Extract via the standard bedrock2
ToCString or via Jasmin (`AUCurves/src/Jasmin/`'s pipeline) and
link as a verified .o.

`ed25519_compress` / `ed25519_decompress_R/_A` use the
sqrt-of-(u/v) inversion path — `EdwardsCompressDecompress.v` has
4 admits closed already; pull the bedrock2 body from there.

`ed25519_scalarmult_base` and `ed25519_scalarmult` are the
hardest — they need R10 (`Bedrock/End2End/Ed25519/Scalarmult.v`)
to close.  Currently Axiom; the strong correctness chain
(`ed25519_sign_strong_correct` Qed) covers them at the
rust_cmd_ed layer, but the bedrock2-WP form is still Axiom
pending the bedrock2-side bridge.

**For an immediate first-cut linked binary**, use libcrux's
`Ed25519` Rust crate as a temporary leaf shim:

```rust
extern "C" fn ed25519_scalarmult_base(out: *mut u8, scalar: *const u8) {
    use libcrux_ed25519::secret_to_public;
    let scalar_bytes = unsafe { core::slice::from_raw_parts(scalar, 32) };
    let mut public = [0u8; 32];
    secret_to_public(&mut public, scalar_bytes.try_into().unwrap());
    // Note: secret_to_public produces compressed 32B, but our slot expects XYZT 200B.
    // Need an additional decompress step here.  Defer to Phase 4 verification.
    unsafe { core::ptr::copy_nonoverlapping(public.as_ptr(), out, 32) };
}
```

This is a **trust shim** — libcrux is hax-verified against an F*
spec, but using it as a leaf in our chain doesn't preserve the
end-to-end AUCurves verification.  Documented as such in the
crate's status.

### Phase 4 — Replace shims with AUCurves-verified leaves

As R10 closes (and the bedrock2-WP bridge for
`ed25519_sign_strong_correct → ed25519_sign_correct` lands),
swap the libcrux shims for AUCurves-extracted equivalents.
Each swap is a one-line change in `memmove_helpers.rs`'s
extern declarations.

### Phase 5 — Cross-language packaging via signal-wasm

Once all leaves are verified, drop `curve25519-jasmin-rs` as a
path-dep into `signal-wasm/component/Cargo.toml` and re-export
`ed25519_rustcmd::{sign, verify}` through the WASI Component
Model bindings.  signal-wasm already follows this pattern for
X25519 + SHA-256 + HMAC + HKDF (Lean-emitted via `RustEmit.lean`).

## Minimum viable wiring (non-verified leaves OK)

For a `cargo build --features ed25519_rustcmd` that **links**
(without claiming end-to-end verification of the leaves):

1. Add `subtle = "2.5"` for `bytes_equal_32`.
2. Add `libcrux-ed25519` or `ed25519-dalek` as a temp dep.
3. Implement leaf shims in `memmove_helpers.rs` per Phase 3 box.
4. Run RFC 8032 KAT vectors as integration tests.

This makes the *pipeline* end-to-end testable while the
verification chain catches up with the bedrock2-WP bridge work.

## Cross-references

- `Bedrock/End2End/Ed25519/Sign_Strong_Correctness.v` — Qed proof
  of rust_cmd_ed-level correctness.
- `Bedrock/End2End/Ed25519/Sign.v` — bedrock2 Axiom + `Theorem
  ed25519_sign_strong_correct_alias` re-export.
- `curve25519-jasmin-rs/src/ed25519_rustcmd/` — generated Rust.
- `SSProve-lean/scripts/extract_ed25519_rust.sh` (sibling repo) —
  upstream Phase-3 build pipeline.

Last updated: 2026-05-09.
