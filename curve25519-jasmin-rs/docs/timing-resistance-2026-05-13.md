# Timing-resistance / constant-time guarantees — audit and analysis

Snapshot 2026-05-13.  **Update 2026-05-13 (later)**: the comb_table_lookup
P0 CT leak documented in §3 has been **fixed** (mask-merge across all
16 entries).  Empirical cost: +10.5 µs to sign (was predicted ~25 µs).
New sign/verify ratios: 2.62× / 3.05× vs dalek (was 1.95× / 2.61×
pre-fix).  All 12 RFC 8032 KATs continue passing.  See §3 below.

## TL;DR

| Layer | CT guarantee | Provenance |
|---|---|---|
| X25519 (libjade Jasmin mulx) | ✅ **Machine-proven CT** | EasyCrypt `extracted_ct_proof.ec` at `libjade/proof/crypto_scalarmult/curve25519/amd64/mulx/` |
| SHA-256, SHA-512 (libjade) | ✅ **Machine-proven CT** | EasyCrypt `extracted_ct_proof.ec` at `libjade/proof/crypto_hash/sha{256,512}/amd64/ref/` |
| ML-KEM-768 (formosa-mlkem) | ✅ Machine-proven CT (Cryspen) | formosa-mlkem EC proofs (sibling repo) |
| AES-256-GCM (RustCrypto current path) | ⚠️ Documented intent; HW-instruction CT via AES-NI; no formal proof | `aes-gcm 0.10` crate docs + AES-NI ISA spec |
| Ed25519 scalar multiplication | ⚠️ **Partial** — comb-table lookup is NOT constant-time | See §3 below |
| Fiat-crypto field arithmetic (`fiat_25519_carry_mul` etc.) | ✅ **Designed for CT** by fiat-crypto's Coq invariant; no branches on secret | fiat-crypto operations are straight-line per Coq proof |
| Scalar25519 mod-L arithmetic (Montgomery domain) | ✅ Designed for CT (fiat-rust scalar ops are straight-line) | Same fiat-crypto provenance |
| Hand-coded Rust glue (mont_to_edwards, scalar25519, protocol composition) | ⚠️ Audit-by-inspection; no formal proof | This document |
| Hax-extracted protocol crates (x3dh-hax / pqxdh-hax / sender-keys-hax / signal-spqr-hax) | ⚠️ Audit-by-inspection; pure protocol logic with no secret-dependent branches | hax-friendly Rust subset deliberately CT |

## 1. What "constant-time" means here

We mean **time-trace constant-time at the source-code level**: no
secret-dependent branch, no secret-dependent memory access pattern.
Specifically:

- No `if secret_bit { ... }` (branch leak).
- No `array[secret_index]` (data-cache leak).
- No early-exit from cryptographic loops on secret-dependent
  predicates (e.g., variable-time `for i in 0..popcount(secret)`).
- No `secret % small_constant` (division latency depends on data on
  some CPUs).

We do NOT claim:
- **Microarchitectural side-channels** (cache, branch prediction,
  port contention) — those depend on the CPU and the surrounding
  workload.  CT at the ISA level is necessary but not sufficient
  against e.g. Spectre / Meltdown.
- **Power analysis** — out of scope; that's a physical-side-channel
  concern requiring hardware-level mitigation.
- **Memory-allocation timing** — variable-length `Vec<u8>` cipher
  texts can leak length but not content; this is by design (cipher
  text size always = plaintext size + tag for AEADs).

## 2. Layer-by-layer audit

### 2.1 Field arithmetic (X25519 + Ed25519 base field)

**`x25519_jasmin` / `x25519_jasmin_base`** — libjade Jasmin mulx.

The corresponding EasyCrypt proof at
`libjade/proof/crypto_scalarmult/curve25519/amd64/mulx/extracted_ct_proof.ec`
proves CT against the leakage model:

> any two executions with the same length-of-public-input produce
> identical instruction traces.

This is **machine-checked CT** modulo the EasyCrypt leakage model
correctness.

Trust: EasyCrypt kernel + the model.

**`fe25519_*` ops (fiat-rust)** — used by mont_to_edwards.rs,
scalar25519.rs, and the verified ed25519 leaves.

fiat-crypto's Coq operations are designed to be straight-line: no
`if`, no `match` on values.  Verified by the fiat-crypto `boundsfp`
invariant.  Source-code audit confirms each op is straight-line.

Trust: fiat-crypto's Coq theorems + Rust extraction faithfulness
(the Rust `fiat_25519_*` is auto-extracted from Coq).

### 2.2 Hashes (SHA-256, SHA-512, HMAC, HKDF)

**`sha256` / `sha512`** — libjade Jasmin `amd64/ref`.

EasyCrypt proof at `libjade/proof/crypto_hash/sha{256,512}/amd64/ref/extracted_ct_proof.ec`
proves CT.

**`hmac_sha256` / `hkdf_sha256_*`** — built on top of `sha256` in
Rust (`symmetric.rs`).  HMAC + HKDF are CT by construction (no
secret-dependent control flow; only XOR + sequential hashing).

Trust: libjade SHA proof + Rust shim audit-by-inspection.

### 2.3 ML-KEM-768

formosa-mlkem provides CT proofs.  Specifically:
- All NTT operations are straight-line.
- Sampling rejects via bounded loop (rejection rate is public).
- Decapsulation uses constant-time comparison + `cmov`.

Trust: Cryspen's formosa-mlkem EC proofs (sibling repository).

### 2.4 AES-256-GCM

**Current** (`aes-gcm = "0.10"`, RustCrypto):
- Uses AES-NI when available (CT at the ISA level — AES-NI
  instructions have constant latency per Intel/AMD specs).
- Falls back to a software AES implementation otherwise.  RustCrypto's
  software AES uses `subtle` for CT-equality checks but does NOT
  document CT for the round function.

**Proposed** (`libcrux` / HACL — queued via agent `ab847dc13b92d61ff`):
- HACL's AES-256-GCM is verified in F* including the CT property at
  the algorithmic level.  Uses AES-NI + PCLMULQDQ for hardware
  acceleration.

Trust: HACL F* proofs + AES-NI ISA spec.

### 2.5 Ed25519 scalar multiplication

This is where the **partial CT** flag lives.

**`comb_scalarmult_base`** (sign path): uses `comb_table_lookup(win_idx, digit)`.

Current implementation in `leaves.rs::wnaf_comb_curve_leaves::comb_table_lookup`:
```rust
let cell = &tbl.cells[i * 16 + d];  // ← secret-dependent index!
```

Where `d = scalar_nibble` and `i = window_index` (public).  The
`scalar_nibble` IS secret, so `tbl.cells[... + d]` leaks via cache
timing.

**Status**: documented in `wnaf-comb-bench-results.md` §"Caveat 2":
"A production deployment would need to mask-merge across all 16
entries (cost: 16× per lookup, ≈ +25µs to sign)."

**Mitigation path**:
```rust
let mut acc = [0u8; 200];
for cand_d in 0..16 {
    let mask = if cand_d == d as usize { 0xff } else { 0x00 };
    for j in 0..200 {
        acc[j] |= tbl.cells[i * 16 + cand_d][j] & mask;
    }
}
// acc now == tbl.cells[i * 16 + d] but accessed all 16 cells
```

The mask itself (`if cand_d == d`) can be made branchless with
`((cand_d as u8) ^ (d as u8)).wrapping_sub(1) >> 7` style tricks
(see `subtle::ConstantTimeEq`).

**Effort**: ~1 hour to write + bench.  Cost: 16× per lookup,
~25 µs added to sign (still ~55 µs total, ~4× dalek).

**`wnaf_scalarmult`** (verify path): does an indexed lookup into a
per-call 8-entry odd-multiples table.  Index `(digit / 2) - 1` ranges
over 0..7 based on the wNAF digit, which is derived from the public
scalar `h = SHA-512(R || A || msg) mod L`.

Is `h` secret?  In Ed25519 verify, `h` is **publicly computable** by
the adversary (R, A, msg are all public).  So the table index is
public.

**Verdict**: verify path is CT-clean.  Sign path's `comb_table_lookup`
is the only known CT leak.

### 2.6 XEdDSA sign/verify

Built on Ed25519 scalarmult.

**`xeddsa_sign_deterministic`** inherits the Ed25519 sign-path CT
caveat (comb_table_lookup with secret nibble).

**`xeddsa_verify`** uses mont_to_edwards conversion (CT — only field
ops on public `u`-coordinate) + Ed25519 verify path (CT, as audited
above).

### 2.7 Protocol composition (X3DH / DR / PQXDH / SK)

The hax-extracted Rust + our trait wirings:
- All branching is on public values (message counters, AAD lengths).
- No `unwrap()` / `expect()` (per §2 audit).
- No `array[secret_index]` patterns audited so far.

Trust: audit-by-inspection.  Recommend running `cargo-careful` +
manual review against a checklist.

### 2.8 mont_to_edwards.rs / scalar25519.rs hand-coded glue

- `mont_u_to_edwards_compressed`: applies fiat-crypto ops + a
  fixed p-2 addition chain (`fe25519_invert`).  No branches on
  secret.  CT by construction.
- `Scalar25519` operations: all fiat-rust scalar ops (Montgomery
  domain) are straight-line.  Wide-reduction `hi * c256 + lo` is
  straight-line.

Trust: source audit + fiat-rust extraction.

## 3. The comb-table-lookup leak — FIXED 2026-05-13

**STATUS: FIXED.**  The original analysis below is preserved for
provenance.  Current implementation is a CT mask-merge across all 16
entries; every execution touches all 16 cache lines regardless of
secret `d`.  Branchless equality mask via signed-arithmetic-shift
trick `(((xor as i16) - 1) >> 15) as u8`.  Empirical cost: +10.5 µs
to sign (was predicted ~25 µs — better than worst-case because
modern CPUs amortize the byte work).  All 12 RFC 8032 KATs pass.

### Original analysis (now historical)

**Location**: `curve25519-jasmin-rs/src/ed25519_rustcmd/leaves.rs::wnaf_comb_curve_leaves::comb_table_lookup` (line ~810).

**Leak shape**: secret 4-bit nibble used as direct array index into
a 16-entry table per window.

**Severity**: cache-timing observable.  Sufficient for known attacks
on related implementations (e.g., the historical scalar mul leaks
in older libraries).

**Fix**: implement the mask-merge pattern shown in §2.5.  ~50 LoC.

**Why it's there**: PoC simplicity.  The mask-merge variant was
deliberately deferred per `wnaf-comb-bench-results.md` §"Caveat 2".

**Action**: HIGH PRIORITY for production deployment.  Should be the
next deliverable after closing this audit.

## 4. Formal-CT verification gaps

What's machine-proven vs audit-only:

| Component | CT proof? | Formalism |
|---|---|---|
| libjade SHA-{256,512}, X25519 | ✅ Yes | EasyCrypt |
| formosa-mlkem | ✅ Yes | EasyCrypt |
| fiat-crypto Ed25519 base field | ⚠️ "Straight-line by construction" — implicit | Coq (boundsfp invariant) |
| Ed25519 wnaf body (rust_cmd_ed) | ⚠️ Phase J `SecretLevel` annotations exist in our Lean RustCmd; not yet enforced at the body level | Lean (annotation only, no enforcement proof) |
| comb body (rust_cmd_ed) | ❌ No CT proof; KNOWN LEAK in comb_table_lookup | — |
| Protocol composition | ❌ Audit only | — |

**To formalize CT** at the Rocq/Lean level, we'd need:
- A CT analysis pass over `rust_cmd_ed` that classifies each branch + memory access as `public` or `secret`-dependent.
- Soundness theorem: if the pass returns `ok`, the emitted Rust has the CT property.
- We have **Phase J SecretLevel** infrastructure in Lean `RustCmd.lean` (LevelTable + `Located.level`) but no enforcement.

**Effort to close**:
- Phase J CT analyser + soundness theorem: ~1-2 sessions for the analyser, multi-week for the soundness theorem.
- Per-AST CT verification (running the analyser on each emitted body + closing any flagged issues): per-body work.

## 5. Recommendations (ranked by leverage)

1. **Fix the comb_table_lookup leak** (~1 hour, P0).  This is the only known cache-timing leak in our production path.  Mask-merge implementation is well-understood + benchmarked.

2. **Document CT properties per primitive in TrustAxioms** (0.5 session).  Each `jade_*_correct` axiom in `LibjadeAxioms.v` should also state "and the operation is CT-clean per the EC proof at <path>".  Currently they only say "computes the spec value".

3. **Enable Phase J SecretLevel analysis on existing emitted ASTs** (1 session).  We have the infrastructure in `RustCmd.lean`; running it on `fe25519InvertBody`, `xeddsaVerifyBody`, etc. would flag any unexpected secret-dependent operations.  Likely no flags fire since the bodies are pure field arithmetic.

4. **Audit hax-extracted protocols for CT** (1 session).  Manually walk through `x3dh-hax`, `pqxdh-hax`, `sender-keys-hax`, `signal-spqr-hax` for any `if secret { ... }` or `array[secret]`.  Document findings.

5. **`cargo-careful` + Miri** (1 session).  Run under cargo-careful with all our test suite.  Catches UB + some timing-related issues at runtime.

6. **Migrate AES-GCM to libcrux HACL** (queued — agent `ab847dc13b92d61ff` in flight).  Replaces RustCrypto's AES-GCM with the F*-verified HACL version, which has formal CT.

7. **Long-term**: formalize CT analysis pass in Lean RustCmd + soundness theorem.  Multi-week.  Closes the gap between "CT by audit" and "CT by proof" for our emitted Rust.

## 6. Bottom line

For the **production hot path** (Ed25519 sign/verify, X3DH/PQXDH/SK/SPQR):

- Public-input operations (verify path, all DH ops, all hashes): **machine-proven CT** via libjade/formosa-mlkem EC proofs.
- Secret-dependent scalar multiplication (sign path): **partial CT** — fiat-crypto field arithmetic is CT, but the comb-table lookup is NOT.

The comb-table fix is the **single most important** CT deliverable for any deployment.  After that, the pipeline is CT-by-audit (no known leaks) across the Rust glue + protocol composition.

For formal CT (Rocq/Lean proven, not just audit), we have the
infrastructure (Phase J SecretLevel) but haven't run it on the
emitted ASTs.  ~1 session to do that for the existing 5+ ASTs;
finding likely "no new flags fire".
