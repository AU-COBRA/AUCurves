# Signal-relevant verified primitives — inventory & perf

Survey of what we have in tree, where each fits in Signal's protocol
stack, and whether it's fast enough for production.

## Signal protocol stack — where each primitive appears

| Phase | Primitives invoked | Frequency |
|---|---|---|
| **Registration / device link** | Ed25519 sign, X25519 keypair gen, Curve25519 → Ed25519 transform | once per device |
| **Prekey upload** | Ed25519 sign (of signed prekey), SHA-256/HKDF | weekly per device |
| **X3DH session setup** | 4× X25519 DH, 1× Ed25519 verify (signed prekey), SHA-256/HKDF | once per new contact |
| **Double Ratchet message** | 0-1× X25519 DH (ratchet step), HMAC-SHA256, AES-GCM | per message |
| **PQXDH session setup** (newer) | + ML-KEM-768 encaps, ML-DSA sig (planned) | once per new contact |
| **zkgroup ops** | Pedersen commitments over Ristretto255, Schnorr/Poksho proofs | per group action |
| **Safety-number verification** | Hash + Ed25519 verify, ristretto encoding | user-triggered |

The latency-sensitive paths are the **message path** (HMAC + AES + occasional DH) and **session setup** (multiple X25519 + 1 Ed25519 + hash). Group ops are background, not user-facing.

## Per-primitive status

### X25519 — Diffie-Hellman key exchange ⭐ Star primitive

**Where used:** every X3DH session (4×), every Double Ratchet step (occasional), every PQXDH PQ-mix step (1×).

**Our implementations** (in `curve25519-jasmin-rs`):

| Backend | Source | µs/op | KAT | Notes |
|---|---|---|---|---|
| `x25519_jasmin` | formosa-25519 mulx (Jasmin) | **26** | ✅ RFC 7748 | EasyCrypt-verified compiler |
| `x25519_cryptopt` | CryptOpt-tuned (NASM) | **16** | ✅ | Superoptimized scalar |
| `x25519_bedrock2` | bedrock2 → C → cc | ~45 | ✅ | Verified extraction |
| `x25519_fiat_c` | fiat-crypto C | ~45 | ✅ | Verified reference |
| dalek serial | upstream | 45-50 | ref | comparison |
| dalek AVX2 | upstream | 25-35 | ref | comparison |

**Verdict: FAST ENOUGH — in fact, fastest available.** Our formosa-Jasmin path at 26 µs beats dalek's serial backend by ~2× and is within ~10% of dalek's AVX2. Production-ready.

### Ed25519 — Signatures

**Where used:** prekey signing (server-side, ~1/week/device), prekey verification (client-side, ~1/new-contact).

**Implementation:** `rust_cmd_ed` extraction → safe Rust. Today's config:

| Op | Framework | Dalek | Ratio | Status |
|---|---|---|---|---|
| sign | 50 µs | 22 µs | 2.2× | KAT ✅ |
| verify | 107 µs | 39 µs | 2.7× | KAT ✅ |

**Verdict: FAST ENOUGH.** Per the perf analysis (`docs/perf-gap-analysis.md`), Signal does ~1-10 ed25519 verifies/day per active user. At 107 µs, that's invisible vs the 100-1000 ms session-setup network RTT. Server-side prekey verify load (~1k/sec peak): 1 CPU core handles all of Signal at 3× the dalek-native speed.

### XEdDSA — X25519-key signatures

**Where used:** sender keys, group-message signing (one X25519 key serves both DH and signing).

**Spec:** `AUCurves/src/Spec/XEdDSA_Curve25519.v`. `sign_verify_correct_25519` Qed under 1 axiom (`B_order : l · basepoint = 0` — provable via Edwards-Montgomery transport, currently axiomatized).

**Implementation:** uses our X25519 + Ed25519 stack. Perf ≈ Ed25519 + a few µs Curve25519 → Edwards transform.

**Verdict: SPEC FAST ENOUGH; needs Rust wiring.** The signature math is verified; the actual Rust API (`sign_with_x25519_key`) needs ~50 LoC of plumbing. Tracked.

### SHA-512 — Used in Ed25519 (challenge hash) + X3DH/HKDF

**Implementation:** libjade Jasmin (`jazz/sha512.jazz`). EasyCrypt-verified compiler; bit-equivalent to standard SHA-512.

**Perf:** ~3 µs for typical Signal-sized inputs (64-byte challenge), ~5-8 µs for 4 KB messages. Matches libjade reference. dalek's `sha2` crate is similar speed.

**Verdict: FAST ENOUGH** ✅.

### SHA-256 — Used in HKDF, HMAC, Ristretto encodings

**Implementation:** We rely on the `sha2` crate (industry-standard, RustCrypto). No verified replacement in our tree yet.

**Future:** a libjade-style verified SHA-256 would mirror the SHA-512 wiring.

**Verdict: FAST ENOUGH (unverified)**. For a fully-verified chain, would need to add a libjade SHA-256 path.

### Keccak / SHAKE-128 / SHAKE-256 — XOF for hash-to-curve

**Where used:** Lizard encoding (Signal's hash-to-Ristretto), hash-to-BLS-G2 (research), some PQ schemes.

**Implementation:** Spec in `AUCurves/src/Spec/Keccak.v` (3 Admitted lemmas in shake256_squeeze_64_ok per memory note). Rust uses `sha3` crate.

**Perf:** ~100 ns/byte for SHAKE-256 (sha3 crate). Negligible for ≤1 KB inputs.

**Verdict: FAST ENOUGH (unverified Rust path; spec partial)**. Signal-ready.

### AES-256-GCM — Symmetric AEAD

**Where used:** every Double Ratchet message body.

**Implementation:** standard `aes-gcm` crate (RustCrypto). Hardware-accelerated on x86 (AES-NI), ARM (ARMv8 crypto), and most modern CPUs.

**Perf:** ~1-3 GB/s on modern x86. Encrypting a 200-byte Signal message: ~70 ns.

**Verdict: FAST ENOUGH (unverified; hardware-accelerated).** No verified replacement is needed for production — every major Signal-equivalent stack uses the same underlying hardware path.

### HMAC-SHA256 — Per-message MAC

**Where used:** Double Ratchet message-key derivation + per-message MAC.

**Implementation:** standard `hmac` + `sha2` crates.

**Perf:** ~1 µs for 32-byte inputs (the Double Ratchet's typical use).

**Verdict: FAST ENOUGH (unverified)** ✅.

### Pedersen-KZG commitment over Ristretto255

**Where used:** zkgroup (Signal's private group memberships).

**Implementation:** `AUCurves/Commitments/theories/Pedersen_Ristretto.v`, `Pedersen_KZG.v`. **4 main theorems Qed**: CORRECTNESS, EVAL_BIND, POLY_BIND, HIDING. **0 admits in KZG_Pedersen.v** per memory note.

**Rust:** uses curve25519-dalek's Ristretto + scalar API. Perf ≈ dalek's `RistrettoPoint::vartime_multiscalar_mul`.

**Verdict: SPEC FULLY PROVED, Rust FAST ENOUGH** ✅.

### Schnorr / Poksho — Sigma protocols

**Where used:** zkgroup selective-disclosure proofs.

**Implementation:** `Commitments/theories/Schnorr_Ristretto.v`, `Poksho.v`, `Poksho_Security.v`. **n-dim Schnorr special soundness Qed** (2026-04-21). `linear_EUF_CMA` still True-placeholder (forking lemma gap).

**Rust:** dalek's `Scalar` and `RistrettoPoint` operations. ~few hundred µs per Schnorr proof — comparable to libzkgroup reference.

**Verdict: PROOFS MOSTLY DONE; PERF FAST ENOUGH** ✅. Forking lemma is a research closure, not a perf gate.

### Ristretto255 — Prime-order group on Curve25519

**Where used:** zkgroup, Lizard encoding.

**Implementation:** spec in `AUCurves/fiat-crypto/src/Spec/Ristretto255.v`, encoded operations in `Commitments/theories/Ristretto255_finGroup.v` and `Ristretto255_SSProve.v`. Rust uses `curve25519-dalek::ristretto`.

**Perf:** dalek's serial backend at ~50 µs/scalarmul, AVX2 at ~25 µs.

**Verdict: SPEC DONE; RUST FAST ENOUGH** ✅. Verified Rust replacement would mirror the Ed25519 work.

### Lizard encoding — Hash-to-Ristretto

**Where used:** Signal's deterministic encoding of identifiers to group elements (replaced Elligator2 for some flows).

**Implementation:** `AUCurves/src/Spec/Lizard.v` with 2 cryptographic Hypotheses (SHA-256 CR + at_most_one_valid). Rust crate uses SHAKE-256 (signed test vectors against go-ristretto).

**Verdict: SPEC PARTIAL (intrinsic crypto assumptions); RUST FAST ENOUGH** ✅.

### Elligator2 — Hash-to-Curve25519

**Where used:** X25519 hash-to-curve in some flows.

**Implementation:** `AUCurves/src/Spec/Elligator2.v` with `elligator2_inverse_complete` axiom (provable via native_compute on GF(2^255-19), ~50 LoC).

**Verdict: SPEC PARTIAL; RUST USES DALEK** ✅.

### ML-KEM-768 (Kyber) — Post-quantum KEM

**Where used:** PQXDH session setup (Signal's newer post-quantum-augmented X3DH).

**Implementation:** NOT in our tree. Signal currently uses libcrux's verified Kyber (via hax+F*). Tracked as L2 in our NEXT.md ("ML-KEM-768 via the Jasmin source extractor", deferred ~2 weeks pending the extractor work).

**Verdict: NOT FAST ENOUGH (we don't have it; libcrux is the production option)**. Future Phase L2 work would land a verified path from our extraction infrastructure.

### BLS12-381 pairing — Used in advanced ZK / SNARK protocols

**Where used:** NOT directly in Signal protocol, but available for research projects on top.

**Implementation:** AUCurves BLS12-381 pairing — **0 admits, all Qed**. `bls12-jasmin-rs` crate ships at 1.95 ms/pairing.

**vs reference:** blst (the standard high-perf library) at 1.5 ms.

**Verdict: VERIFIED; PERF WITHIN 1.3× OF BLST** ✅. Available for use.

## Bottom line by category

| Category | Verified status | Perf vs reference | Production-ready for Signal |
|---|---|---|---|
| **X25519** | ✅ multi-path (Jasmin + bedrock2 + CryptOpt) | **2× faster than dalek serial** | ✅✅ |
| **Ed25519** | ✅ rust_cmd_ed extraction | 2.2× sign, 2.7× verify behind dalek | ✅ (off hot path) |
| **XEdDSA** | ✅ spec Qed | inherits Ed25519 | ⚠️ needs Rust API wiring |
| **SHA-512** | ✅ libjade Jasmin | matches dalek | ✅ |
| **SHA-256** | unverified in tree (uses sha2 crate) | industry-standard | ✅ |
| **Keccak/SHAKE** | partial spec | sha3 crate | ✅ |
| **AES-GCM** | unverified (industry standard) | hardware-accelerated | ✅ |
| **HMAC-SHA256** | unverified | fast | ✅ |
| **Pedersen-KZG** | ✅ 4 theorems Qed | matches dalek | ✅ |
| **Schnorr/Poksho** | ✅ soundness Qed | matches reference | ✅ |
| **Ristretto255** | spec done; Rust uses dalek | matches dalek | ✅ |
| **Lizard** | partial spec | RustCrypto-grade | ✅ |
| **ML-KEM** | ❌ not in tree | n/a | use libcrux |

## Honest framing for Signal production

**Hot path** (per-message): AES-GCM + HMAC + occasional X25519. All FAST ENOUGH, dominated by our 26 µs X25519 (which is *faster* than dalek-serial).

**Warm path** (per-session): X3DH = 4 × X25519 + 1 × Ed25519 verify + SHA-512 + HKDF. **~200 µs total** with our stack vs ~150 µs with all-dalek. Network RTT for session establishment is 50-500 ms — the 50 µs delta is invisible.

**Cold path** (per-device): registration / linking. One-shot operations, perf irrelevant.

**Group operations** (zkgroup): Pedersen + Schnorr proofs over Ristretto. Perf matches reference; verified soundness is the value-add.

**Post-quantum** (PQXDH): ML-KEM not yet in tree. **Gap.** Signal currently uses libcrux; we'd compose if/when we add ML-KEM via the L2 Jasmin-source-extractor work.

The bottom line: **everything Signal touches today on the hot or warm path is fast enough in our framework. Ed25519's 2.7× verify gap is the most visible perf shortfall but happens on a path that already costs 100-500 ms in network latency.** The post-quantum upgrade is the legitimate near-term gap, but it's a roadmap item, not a regression.
