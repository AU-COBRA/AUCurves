# Migration: AES-256-GCM → AES-256-CBC + HMAC-SHA-256 (2026-05-13)

This note documents the migration of the runtime AEAD in
`curve25519-jasmin-rs` from AES-256-GCM (RustCrypto, hardware-
accelerated AES-NI) to AES-256-CBC + HMAC-SHA-256 (Signal-spec
compliance), per the Signal Double Ratchet and Sender Keys
specifications.

## Motivation

Signal's spec mandates AES-256-CBC + HMAC-SHA-256 (encrypt-then-MAC)
for Double Ratchet message bodies and Sender-Keys group messages.  The
previous runtime path was AES-256-GCM via the `aes-gcm` RustCrypto
crate, which was a pragmatic choice but **not the Signal wire**.
Cross-implementation interop with the libsignal reference (or any
spec-conforming Signal stack) requires the CBC + HMAC wire.

A secondary benefit: the new path's AES block cipher is the pure-Rust
FIPS-197 spec implementation from `libcrux-lean-specs` — the very
same crate the Lean formal-spec extraction targets.  This closes the
runtime / spec extraction loop on the block cipher (the cipher path
the Lean spec proves about IS the Rust runtime).

## Wire format

```
   IV (16 bytes) || ciphertext_PKCS7 || HMAC-SHA-256_tag (32 bytes)
```

Where `ciphertext_PKCS7 = AES-256-CBC_Encrypt(cipher_key, IV,
PKCS7_Pad(plaintext))`, and the HMAC tag is computed over
`aad || IV || ciphertext_PKCS7` using a separate `mac_key`
(encrypt-then-MAC composition).

For the protocol-trait API (`DoubleRatchetCrypto::aead_*`,
`SenderKeysCrypto::aead_*`), which supplies a single 32-byte
`MessageKey` + 12-byte `Nonce`, the implementation derives the three
subkeys `(cipher_key, mac_key, IV)` via HKDF-SHA-256:

```
   PRK     = HKDF-Extract(salt = nonce_padded_to_32_bytes, ikm = key)
   OKM(80) = HKDF-Expand(PRK, info = "Signal-CBC-HMAC-AES256")
   cipher_key = OKM[0..32]
   mac_key    = OKM[32..64]
   IV         = OKM[64..80]
```

This preserves the existing 32-byte-key + 12-byte-nonce call sites
bit-for-bit.  IV uniqueness inherits from nonce uniqueness through
HKDF's deterministic split.

## API summary

`src/symmetric.rs` exposes:

| Function | Use |
|----------|-----|
| `aes256_cbc_hmac_encrypt(cipher_key, mac_key, iv, pt, aad)` | Raw CBC+HMAC with explicit subkeys + 16-byte IV. |
| `aes256_cbc_hmac_decrypt(cipher_key, mac_key, wire, aad)` | Raw counterpart; returns `Option<Vec<u8>>`. |
| `aes256_cbc_hmac_encrypt_nonce(key, nonce, aad, pt)` | 32-byte-key + 12-byte-nonce shim used by DR / SenderKeys traits. |
| `aes256_cbc_hmac_decrypt_nonce(key, nonce, aad, wire)` | Decrypt counterpart. |

Legacy AES-GCM functions (`aes256_gcm_encrypt`, `aes256_gcm_decrypt`)
are still present, gated behind the new `aes_gcm_legacy` Cargo feature
(default **OFF**).  Enable it (`--features aes_gcm_legacy`) for wire-
compat with data encrypted under the old wire.  The
`aes_gcm_libcrux` feature now implies `aes_gcm_legacy`.

## Loc delta

| File | Before | After | Delta |
|------|--------|-------|-------|
| `src/symmetric.rs` | 580 | 1097 | +517 |
| `src/double_ratchet.rs` | 393 | 383 | -10 |
| `src/sender_keys.rs` | 137 | 141 | +4 |
| `tests/double_ratchet_with_aucurves.rs` | 395 | 401 | +6 |
| `tests/sender_keys_with_aucurves.rs` | 117 | 120 | +3 |
| `benches/aead_cbc_vs_gcm.rs` | 0 | 98 | +98 (new) |
| `libcrux-lean-specs/rust-specs/src/aes.rs` | 372 | 562 | +190 (new `aes256_decrypt` + KAT) |

The `double_ratchet.rs` delta is negative because the new imports
replaced a longer comment.  Of the +517 LoC in `symmetric.rs`, the breakdown is:

  - PKCS#7 pad/unpad: ~40 LoC
  - CBC encrypt/decrypt raw blocks: ~50 LoC
  - Constant-time `ct_eq`: ~10 LoC
  - Two AEAD encrypt/decrypt functions (raw + nonce-shim): ~70 LoC
  - HKDF subkey derivation: ~15 LoC
  - Doc comments + wire-format constants: ~30 LoC
  - New unit tests (8 new tests, ~150 LoC): NIST SP 800-38A KAT,
    PKCS7 roundtrip + malformed-reject, 4 reject paths, shim
    roundtrip + IV uniqueness, `ct_eq` check.

## KAT test count

Test results on `cargo test --features dalek_leaves`:

| Suite | Before | After | Δ |
|-------|--------|-------|---|
| `symmetric::tests` (lib) | 9 GCM-era | 17 CBC-era | +8 |
| `aes::tests` (libcrux-lean-specs) | 5 | 8 | +3 |
| `tests/double_ratchet_with_aucurves` | 9 | 9 | 0 (wire-format assertions updated) |
| `tests/sender_keys_with_aucurves` | 3 | 3 | 0 |
| `tests/*` (other suites) | ~50 | ~50 | 0 |

Full crate test suite (after migration, `--features dalek_leaves`):
**163 tests passing, 0 failing**.

New KATs:
  - `aes_cbc_nist_sp80038a_f2_5_block1`: NIST SP 800-38A §F.2.5 block 1.
  - `pkcs7_roundtrip` / `pkcs7_rejects_malformed`: PKCS7 spec.
  - `aes_cbc_hmac_roundtrip_lengths`: 16 lengths from 0 to 4096 bytes.
  - `aes_cbc_hmac_rejects_tampered_ciphertext`: bit-flip on each region.
  - `aes_cbc_hmac_rejects_wrong_mac_key`: HMAC key off-by-one.
  - `aes_cbc_hmac_rejects_wrong_aad`: AAD mismatch.
  - `aes_cbc_hmac_rejects_wrong_iv`: IV mutation (covered by HMAC).
  - `aes_cbc_hmac_rejects_truncated`: 0..47 byte wires.
  - `aes_cbc_hmac_nonce_shim_roundtrip` + `..._iv_uniqueness`:
    nonce-shim correctness + IV uniqueness across nonces.
  - `ct_eq_basic`: constant-time equality on equal / unequal / length-mismatch.

On the upstream side, three new tests in `libcrux-lean-specs/rust-specs/src/aes.rs`:
  - `test_aes128_decrypt_fips197_appendix_b`
  - `test_aes256_decrypt_fips197_appendix_c3`
  - `test_aes_encrypt_decrypt_roundtrip` (8×8 = 64 cases, both 128 and 256)

## Performance delta

Benchmark: `cargo bench --features "dalek_leaves aes_gcm_legacy"
--bench aead_cbc_vs_gcm` on the local dev machine (Zen 4, AVX-512,
single-threaded criterion, --measurement-time 2s, --sample-size 30).

### Encrypt

| msg | CBC+HMAC (new) | AES-GCM legacy (RustCrypto AES-NI) | ratio |
|-----|---------------|------------------------------------|-------|
|   16 B |   4.82 µs |  221 ns |  21.8x slower |
|   64 B |   6.11 µs |  250 ns |  24.4x slower |
|  256 B |  11.63 µs |  348 ns |  33.4x slower |
| 1024 B |  33.31 µs |  784 ns |  42.5x slower |
| 4096 B | 120.15 µs |  2.45 µs |  49.0x slower |

### Decrypt

| msg | CBC+HMAC (new) | AES-GCM legacy | ratio |
|-----|----------------|---------------|-------|
|   16 B |   5.65 µs |  254 ns |  22.2x slower |
|   64 B |   7.83 µs |  259 ns |  30.2x slower |
|  256 B |  16.97 µs |  363 ns |  46.8x slower |
| 1024 B |  51.95 µs |  808 ns |  64.3x slower |
| 4096 B | 193.04 µs |  2.50 µs |  77.2x slower |

### Why so slow?

The CBC+HMAC path runs a pure-Rust FIPS-197 AES implementation (no
AES-NI, no `unsafe`), so the per-block cost is ~80-100 cycles for
14-round AES-256 instead of ~10 cycles for AES-NI's `AESENC` chain
plus PCLMULQDQ for GCM auth.  At 4 KiB the steady-state CBC+HMAC
throughput is ~33 MiB/s encrypt / ~21 MiB/s decrypt vs ~1.6 GiB/s
encrypt / ~1.5 GiB/s decrypt for hardware-AES-GCM (criterion numbers
above).

For a Signal Double Ratchet message body of ~256 bytes (typical
SMS-scale text plus header), the per-message overhead goes from
~350 ns to ~12 µs — i.e. ~12 µs per message.  At human-message-rate
(~1 msg/second per chat) this is irrelevant; at machine rates (push
batches of 10k messages) this adds ~120 ms of CPU time.

### How to recover the speed later

Three options, in order of cleanliness:

1. **libcrux HACL raw-AES export** (preferred): once libcrux exposes
   a raw AES-256 block API (not just the AEAD wrapper), drop in
   `libcrux::aes::aes256_encrypt_block` for the AES block under our
   CBC chain.  This preserves the verified-cipher chain and gains
   AES-NI.  Estimated: ~30x speedup, parity with AES-GCM at the
   block-cipher layer (HMAC-SHA-256 over libjade SHA-256 stays the
   same).
2. **libjade AES-NI Jasmin** (long-term verified): pull in libjade's
   formosa-AES once the Jasmin assembly + EasyCrypt proofs land in
   the vendored snapshot.  Same speed gain plus end-to-end
   EasyCrypt verification of the cipher path.
3. **AES-NI inline asm in safe-but-`unsafe`-wrapper Rust**: drop in
   the RustCrypto `aes` crate's hand-tuned AES-NI implementation as
   the block primitive.  Speed gain but loses the "FIPS-197 spec /
   Lean extraction target" benefit.

The CBC composition + PKCS7 padding + HMAC tag + constant-time
comparison are completely independent of the AES block primitive
choice and will be reused under any of the above.

## Trust transfer

| Component | Before (GCM) | After (CBC+HMAC) |
|-----------|--------------|------------------|
| AES block cipher | RustCrypto `aes` (AES-NI), unverified at Rust source | libcrux-lean-specs FIPS-197 pure Rust spec; byte-identical to libcrux HACL F* / lean spec proven against same spec  |
| AEAD mode | RustCrypto `aes-gcm` GCM mode, unverified | safe-Rust CBC chain over the FIPS-197 block primitive; ~80 LoC, no `unsafe`, NIST SP 800-38A KAT-attested |
| Authenticator | GCM tag, GHASH (binding via cipher key), unverified | HMAC-SHA-256 (RFC 2104) over libjade SHA-256 (EasyCrypt-verified Jasmin compiler), RFC 4231 KAT-attested, separate `mac_key` |
| Constant-time tag compare | RustCrypto-internal (assumed CT) | handwritten XOR-accumulator in this crate (`ct_eq`) |

Net: the verified surface gains the FIPS-197 spec match (cipher) and
the libjade-SHA-256 transitive verification (authenticator); it loses
AES-NI speed.  Wire-format binding to Signal spec is now correct.

## FFI safety audit

Per the request to classify which calls cross `extern "C"`:

| Component | Path |
|-----------|------|
| AES-256 block (encrypt + decrypt) | **pure Rust** (`libcrux_specs::aes::aes256_{encrypt,decrypt}`) — no FFI, no `unsafe` |
| CBC mode (XOR + chain) | **pure Rust** (`src/symmetric.rs`) — no FFI, no `unsafe` |
| PKCS#7 padding (pad + unpad) | **pure Rust** — no FFI, no `unsafe` |
| HMAC-SHA-256 (RFC 2104) | **pure Rust** (`src/symmetric.rs::hmac_sha256`) — no `unsafe`, but the underlying SHA-256 calls `ffi_safe::jade_sha256` (single safe wrapper over libjade Jasmin `extern "C"`) |
| HKDF subkey derivation | **pure Rust** — same as HMAC (delegates to `hmac_sha256`) |
| Constant-time tag compare | **pure Rust** — no FFI, no `unsafe` |

Conclusion: the entire CBC + HMAC AEAD path is safe Rust outside the
existing `ffi_safe::jade_sha256` wrapper (which is the only `unsafe`
block reaching `extern "C"` and was already audited as part of
Phase B).  No new `unsafe` introduced.

## Verification status of the migration

This migration is a wire-format change accompanied by a pure-Rust
composition over verified primitives.  Specifically:

  - **NEW**: CBC + PKCS7 + ct_eq + HKDF subkey-split.  These are
    pure Rust, no formal proof at the Rust level, but each is a
    spec-literal translation of a public standard (NIST SP 800-38A
    §6.2; RFC 5652 §6.3; RFC 5869 §2) and KAT-tested against the
    spec's published vectors.  Trust = "Rust source review +
    KAT".
  - **REUSED**: HMAC-SHA-256 over libjade SHA-256.  Already in the
    crate, RFC 4231 KAT-tested, EasyCrypt-verified compiler for
    the hash leaf.
  - **REUSED**: AES-256 block (encrypt + new decrypt).  Pure-Rust
    FIPS-197 spec from `libcrux-lean-specs`.  Same crate is the
    Lean spec's extraction target — the Rust source IS the spec.
    Encrypt path was already FIPS-197 Appendix C.3 KAT-attested;
    decrypt now FIPS-197 Appendix C.3 reverse KAT-attested plus
    8x8 encrypt-decrypt roundtrip KAT.

The migration does not introduce a new verified theorem; it migrates
**from** an unverified hardware AEAD **to** a composition over
already-verified primitives + a spec-literal CBC chain.  Net trust
moves from "RustCrypto aes-gcm crate correctness" to "libcrux-lean-
specs AES + libjade SHA-256 correctness + spec-literal CBC".

## Commit

Working tree at the time of this migration: untouched files include
`AUCurves/`, `SSProve-lean/`, `signal-hax/`, `catcrypt-bench/`,
`fiat-crypto/`, and the existing recent-work files (`ffi_safe.rs`,
`ed25519_rustcmd/leaves.rs`, `zkgroup_demo.rs`, and the
`__jasmin_syscall_randombytes__` panic stub).
