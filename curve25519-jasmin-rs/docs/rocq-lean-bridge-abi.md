# Track A — Rocq/Lean rust_cmd ABI bridge audit

## Status: 2026-05-12 — DONE (auditing only; both sides already in agreement)

## Conclusion

**Both Rocq's `rust_cmd_ed` and Lean CatCrypt's `rust_cmd` already
emit byte-identical Rust ABIs.**  The bridge is the Rust ABI —
`pub unsafe extern "C" fn name(out: *mut u8, args: *const u8, ...)`
over fixed-size byte buffers.  Either framework's emission can call
the other's via plain `extern "C" { fn ... }` declarations, modulo
matching the function name, arg shapes, and slot sizes.

No new bridge code is needed.  This doc captures the contract.

## ABI surface

The Signal protocol stack we want to compose needs these byte
signatures (caller-supplied buffers, all sizes static):

### Primitives (Rocq side; AUCurves + curve25519-jasmin-rs)

```rust
// X25519 — formosa-25519 Jasmin (RFC 7748)
extern "C" fn x25519_jasmin(out: *mut [u8; 32],
                            scalar: *const [u8; 32],
                            point: *const [u8; 32]);
extern "C" fn x25519_jasmin_base(out: *mut [u8; 32],
                                 scalar: *const [u8; 32]);

// Ed25519 — rust_cmd_ed extraction
extern "C" fn ed25519_sign_raw(sig_out: &mut [u8; 64],
                               seed: &mut [u8; 32],
                               msg: &mut [u8; 4096],
                               msg_len: u64);
extern "C" fn ed25519_verify_raw(result_out: &mut [u8; 1],
                                 sig: &mut [u8; 64],
                                 pk: &mut [u8; 32],
                                 msg: &mut [u8; 4096],
                                 msg_len: u64);

// SHA-512 — libjade Jasmin
extern "C" fn sha512_64(out: *mut [u8; 64],
                        msg: *const u8,
                        len: u64);

// SHA-256 — libjade Jasmin (to be wired, B4)
extern "C" fn sha256_32(out: *mut [u8; 32],
                        msg: *const u8,
                        len: u64);

// Future: AES-GCM (libjade), ML-KEM-768 (libjade or libcrux).
```

### Building blocks (either side; recommended Rocq for these)

```rust
// HMAC-SHA256 / HMAC-SHA512 — trivial composition over hashes
extern "C" fn hmac_sha256(out: *mut [u8; 32],
                         key: *const u8, key_len: u64,
                         msg: *const u8, msg_len: u64);
extern "C" fn hmac_sha512(out: *mut [u8; 64],
                         key: *const u8, key_len: u64,
                         msg: *const u8, msg_len: u64);

// HKDF — sequenced HMAC
extern "C" fn hkdf_sha256_extract(prk: *mut [u8; 32],
                                  salt: *const u8, salt_len: u64,
                                  ikm: *const u8, ikm_len: u64);
extern "C" fn hkdf_sha256_expand(okm: *mut u8, okm_len: u64,
                                 prk: *const [u8; 32],
                                 info: *const u8, info_len: u64);

// XEdDSA — Ed25519 signatures over X25519 keys
extern "C" fn xeddsa_sign(sig_out: *mut [u8; 64],
                          x25519_priv: *const [u8; 32],
                          msg: *const u8, msg_len: u64,
                          random: *const [u8; 64]);
extern "C" fn xeddsa_verify(x25519_pub: *const [u8; 32],
                            msg: *const u8, msg_len: u64,
                            sig: *const [u8; 64]) -> u32;
```

### Protocols (Lean CatCrypt side)

```rust
// X3DH initial-key-agreement
extern "C" fn x3dh_initiate(
    shared_secret: *mut [u8; 32],         // output
    initial_msg: *mut [u8; 96],           // output (Alice's ephemeral pk + identity pk + ...)
    alice_identity_priv: *const [u8; 32],
    bob_identity_pk: *const [u8; 32],
    bob_signed_prekey_pk: *const [u8; 32],
    bob_signed_prekey_sig: *const [u8; 64],
    bob_onetime_prekey_pk: *const [u8; 32],
);

extern "C" fn x3dh_respond(
    shared_secret: *mut [u8; 32],
    initial_msg: *const [u8; 96],
    bob_identity_priv: *const [u8; 32],
    bob_signed_prekey_priv: *const [u8; 32],
    bob_onetime_prekey_priv: *const [u8; 32],
);

// Double Ratchet (CatCrypt-provided per user)
extern "C" fn dr_init_alice(state: *mut DrState, ...);
extern "C" fn dr_encrypt(state: *mut DrState,
                        ciphertext: *mut u8,
                        plaintext: *const u8, ...);
extern "C" fn dr_decrypt(state: *mut DrState,
                        plaintext: *mut u8,
                        ciphertext: *const u8, ...);
// ... etc.

// PQXDH, Sender Keys, zkgroup, etc. — same shape.
```

## Cross-extractor invariants

Both `rust_cmd_ed` (Rocq) and CatCrypt `rust_cmd` (Lean) follow
these conventions:

1. **Fixed-size buffers.**  No variable-length types cross the ABI.
   When a primitive needs variable input (msg, info), it accepts
   `*const u8` plus a `u64` length.
2. **Out-pointer first.**  Output buffers always come first in the
   argument list.  Matches Jasmin / fiat-crypto convention.
3. **No allocations.**  Caller supplies all buffers.  Matches the
   `#![no_std]`-friendly target.
4. **Constant time.**  All ops are CT per their own framework's
   proofs.  Bridge introduces no branches.

## Linker model

Both frameworks emit `#[unsafe(no_mangle)] pub unsafe extern "C"
fn name(...)` Rust source files.  These get compiled into the same
crate (`signal-crypto-aucurves` or extending
`curve25519-jasmin-rs`), and the Rust linker resolves call sites
against either side's emission based on the function name alone.

Convention: emitter prefix in the source filename:
  - `src/ed25519_rustcmd/*.rs` — Rocq-emitted.
  - `src/catcrypt_emit/*.rs` — Lean-emitted.

No symbol collision risk as long as each function name is owned by
exactly one emitter.

## Smoke test (composable extraction)

The end-to-end flow:
  1. Rocq AUCurves emits `ed25519_sign_raw`, `sha512_64`,
     `x25519_jasmin` to Rust files.
  2. Lean CatCrypt emits `x3dh_initiate` to a Rust file in the same
     crate.
  3. `x3dh_initiate` declares `extern "C" { fn x25519_jasmin(...);
     fn sha512_64(...); }` and calls them.
  4. `cargo build` succeeds; the static lib contains both sides.
  5. KAT vectors pass end-to-end.

This pattern is already proven in signal-wasm's existing X25519 +
SHA-256 swaps (Lean → safe Rust → wasm component).  Track A is
just the audit: confirming the pattern extends to Rocq as the
primitive emitter and Lean as the protocol composer.

## What this enables (gating items)

Track B and C work proceeds against this contract:

- **B-track** primitives emitted by Rocq must conform to the ABI
  above (out-pointer first, byte buffers, etc.).
- **C-track** protocols emitted by Lean CatCrypt call these
  primitives via `extern "C"` declarations matching the ABI.

If both sides honor the conventions, no integration code is needed
beyond the standard Rust `extern "C"` boilerplate.
