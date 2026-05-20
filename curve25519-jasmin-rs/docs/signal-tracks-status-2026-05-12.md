# Tracks XEdDSA / B7 / C2 / C3-C5 / Protobuf — status & path forward

Consolidated answers + concrete next steps for the Signal end-to-end
plan items the user asked about.

## 1. Protobuf: how hard is verified?

**Three options, ordered by feasibility:**

### Option A — Use unverified `prost` (today)
Industry standard, well-maintained, ~5 µs serialization for typical
Signal message sizes.  Same approach libsignal uses.  **Verified-
chain status:** protocol layer verified, wire format unverified.
Matches libsignal's own verification posture.  **Effort: 0.**

### Option B — Hand-verified marshalers per message type (~2 weeks)
For Signal's specific schema (≈20 message types: `PreKeyMessage`,
`SignalMessage`, `SenderKeyMessage`, `SenderKeyDistributionMessage`,
`KEMCiphertext`, etc.), hand-author Rust marshalers AND
serialization-correctness proofs (in Rocq or Lean).  Per message
type: ~50 LoC marshaler + ~30 LoC functional-correctness theorem.
Could co-locate in CatCrypt (Lean) with the protocol formalizations
that consume them.

What's verified: "serialize then deserialize is identity",
"serialize is injective on well-formed messages".  These are
mechanical proofs over a fixed-schema decoder.

**Trust shrinks** from "trust prost" to "trust our hand-written
marshalers" — small win unless the hand-written code is itself
verified (which it could be in Lean).

### Option C — General verified protobuf parser (~6+ months)
Full protobuf spec support (varint encoding, recursive nesting,
unknown fields, length-prefixed strings).  Multiple papers exist
(Tezos's proto-verified work, F* Project Everest sub-projects).
Not on Signal's critical path.

### Honest recommendation
**Option A for shipping**, Option B if the verification narrative
needs to extend to wire-format byte-exact behavior.  Protobuf is
not where Signal security issues live; it's where Signal performance
and ABI compatibility issues live.

## 2. What's missing from XEdDSA?

The current `xeddsa_verify` in `src/xeddsa.rs:87-114` is a documented
placeholder:

```rust
// Simplified x-coordinate check (not fully correct for general inputs)
// Full verification needs Edwards point addition
s_g == r_bytes || s_g == e_a // placeholder comparison
```

**What's actually needed for proper XEdDSA verify:**

1. **Curve25519 → Edwards conversion.**  Given X25519 pubkey `K` (32
   bytes, Montgomery u-coord), derive the corresponding Ed25519
   verify-key `A` (Edwards y-coord + parity bit):

   ```
   y = (u - 1) / (u + 1)  mod p
   A = encode_edwards(y, sign=0)
   ```

   Requires field-element invert (`(u+1)^(-1) mod p`) — same chain as
   in our compress/decompress.  ~30 LoC over `fe25519_portable` or a
   limb-format equivalent.

2. **Standard Ed25519 verify** with that derived key.  Reuse our
   working `ed25519_rustcmd::verify`.

3. **XEdDSA-specific nonce derivation.**  XEdDSA-sign uses
   `SHAKE-256(K || nonce_input)` for synthetic nonces (not Ed25519's
   `SHA-512(seed || msg)` style).  Verify side doesn't care about
   nonce, only the standard Schnorr equation check.

**Effort:**
- Step 1 (u→y conversion): half-day Rust + a Rocq/Lean correctness
  proof can defer to PoC level.
- Step 2: drop-in.
- Step 3: not needed for verify, only sign-side compatibility.

**Total: 1 day** to make `xeddsa_verify` produce correct results.
Once done, X3DH switches from "Bob has separate Ed25519 key" to the
Signal-spec-compliant "Bob's X25519 identity key doubles as XEdDSA
verify-key".

## 3. Track B7 — AES-GCM

### libjade status (this tree)
**Not present.**  Our vendored libjade snapshot has SHA-256, SHA-512,
SHA-3, Poly1305, X25519, but no AES-GCM.  Upstream libjade has
ongoing AES-GCM work but it isn't in our local copy.

### Pragmatic path forward
**Use RustCrypto `aes-gcm` crate.**  This is what libsignal currently
uses; it's hardware-accelerated via `aes` crate (AES-NI on x86,
ARMv8 crypto on aarch64).  Add a thin wrapper in our `symmetric`
module exposing the bridge ABI:

```rust
pub fn aes256_gcm_encrypt(
    key: &[u8; 32], nonce: &[u8; 12], aad: &[u8], plaintext: &[u8],
) -> Vec<u8>;
pub fn aes256_gcm_decrypt(
    key: &[u8; 32], nonce: &[u8; 12], aad: &[u8], ciphertext: &[u8],
) -> Result<Vec<u8>, ()>;
```

**Effort: half-day** for the wrapper + 100-byte KAT against NIST CAVS
vectors.

### Verified replacement
Drop-in when libjade AES-GCM stabilizes.  Same ABI shape; only the
implementation changes.  Estimated **~1 week vendor + wire** at that
point.

Alternative for sooner: lift Jasmin's compiler-test AES code
(`jasmin/compiler/tests/success/x86-64/aes.jazz`) into a full
AES-GCM body.  Significant authoring work (the test only covers
single AES rounds), but mechanically straightforward.  **~2 weeks.**

## 4. Track C2 — Double Ratchet wiring

### What CatCrypt has (per `SSProve-lean/CatCrypt/Crypto/Signal/`)
**56 protocol files**, including:

| File | What |
|---|---|
| `DoubleRatchet.lean` | Core DR formalization |
| `DoubleRatchet_UC.lean` | Universal-Composability proof |
| `DoubleRatchet_CKA.lean` | Connection to CKA (continuous key agreement) |
| `DoubleRatchet_Quantum.lean` | PQ-secure DR variant |
| `DoubleRatchetStatefulConcrete.lean` | Concrete stateful executable form |
| `DoubleRatchetPipelineUC.lean` | UC composition pipeline |
| `DoubleRatchet_Quantum_Concrete.lean` | Concrete PQ form |
| `TripleRatchet.lean` (+ variants) | Triple-ratchet (newer Signal variant) |
| `SymmRatchet.lean` (+ examples) | Symmetric ratchet building block |
| `KEM_Signal.lean` | KEM-based Signal variant |
| `FSAEAD.lean` | Forward-secure AEAD (DR's encryption layer) |

### Hax-extracted Rust skeletons (already in tree)
- `SSProve-lean/doubleratchet-hax/` — hax-emitted Rust from CatCrypt's DR formalization.
- `SSProve-lean/signal-spqr-hax/` — Signal SPQR (sparse post-quantum ratchet) extraction.

### Wiring approach
The signal-spqr-hax `Cargo.toml` currently uses `ml-kem`, `hkdf`,
`sha2`, `rand` as dev-dependencies — i.e., it uses RustCrypto crates
for its primitives.  **The wiring step is**: change those
dev-deps' implementations to point at our verified primitive crate
(`curve25519-jasmin`), keeping the hax-emitted Rust file structure
intact.

Concrete steps:

1. Add `curve25519-jasmin` (this crate) as a dependency to
   `signal-spqr-hax` and `doubleratchet-hax`.
2. Replace `use hkdf::*` with `use curve25519_jasmin::symmetric::hkdf_sha256`.
3. Replace `use sha2::Sha256` with our `sha256` wrapper.
4. Replace `use ml_kem::*` with either:
   - libcrux's ML-KEM (verified via hax+F*) — shippable today, or
   - a future libjade ML-KEM (track L2).
5. Run hax's test suite to confirm no behavioral regression.

**Effort: ~1 week** per ratchet variant (Double, Triple, Quantum).
Mostly mechanical, no proof work.

### What we DON'T need to do
- Re-implement DR in Rust — hax already did.
- Re-prove DR in our framework — CatCrypt already has the proofs.
- Build a state machine — `DoubleRatchetStatefulConcrete.lean` provides one.

**Net Track C2: ~1 week of wiring** if signal-spqr-hax / doubleratchet-hax
are already in usable shape; we add the verified-primitive backend.

## 5. Tracks C3 (PQXDH), C4 (Sender Keys), C5 (zkgroup)

### C3 — PQXDH
**CatCrypt has it.**  Files:
- `PQXDH.lean`
- `PQXDHPipelineUC.lean`
- `PQXDHPipelineUCConcrete.lean`
- `PQXDHReduction.lean`

Same wiring approach as C2: route CatCrypt's primitive calls
(X25519, ML-KEM, SHA-256, HKDF) at our verified backends.

**Effort: ~1 week** for the X25519 / SHA / HKDF rewiring; ML-KEM
inherits from C2's decision (libcrux today, libjade future).

### C4 — Sender Keys
**Approximated by CatCrypt's `SymmRatchet`** (group messaging is a
symmetric-ratchet protocol; the sender-key naming is libsignal's).
Files:
- `SymmRatchet.lean`
- `Examples/SymmRatchet.lean`
- `Examples/SymmRatchet_UC.lean`

Signal's `GroupCipher` and `GroupSessionBuilder` map to this.

**Effort: ~3 days** wiring (HMAC + AES-GCM are the only primitive
deps).

### C5 — zkgroup
**CatCrypt has Zkgroup directory.**  Plus our existing primitives:
- `Commitments/theories/Pedersen_Ristretto.v` + `Pedersen_KZG.v`
  (Rocq, 4 theorems Qed).
- `Commitments/theories/Poksho.v` + `Poksho_Security.v` (n-dim
  Schnorr soundness Qed).

The wiring connects CatCrypt's Lean Zkgroup protocol with our
Rocq-verified primitives, via the bridge ABI.

**Caveat:** zkgroup credential ISSUANCE is server-side; client-side
verification is what we'd typically deploy.  Server-side issuance
needs separate handling (Signal runs the issuer; we'd compose
client-side only or build a separate verified-issuer crate).

**Effort: ~2 weeks** for client-side composition.

## 6. Revised total session burn-down

| Item | Effort | Status |
|---|---|---|
| Bridge ABI audit | done | ✅ |
| SHA-256 wiring | done | ✅ |
| HMAC + HKDF | done | ✅ |
| XEdDSA Rust API | partial — sign works, verify is placeholder | ⚠️ |
| X3DH self-consistency | done (uses Ed25519 for SPK; needs XEdDSA verify) | ✅ partial |
| AES-GCM | RustCrypto for now; libjade gap documented | ⚠️ |
| Double Ratchet wiring | CatCrypt + hax extraction available; concrete wiring is ~1 wk | docs only |
| PQXDH wiring | CatCrypt has it; ~1 wk after C2 | docs only |
| Sender Keys wiring | CatCrypt SymmRatchet; ~3 days | docs only |
| zkgroup wiring | CatCrypt Zkgroup + our Pedersen/Poksho; ~2 wks client-side | docs only |
| Protobuf | recommended unverified prost; verified hand-marshalers ~2 wks | docs only |

## Concrete next-up plan

Order of operations to reach a **fully wired Signal stack PoC**:

1. **Fix XEdDSA verify** (1 day) — unblocks Signal-spec-compliant X3DH.
2. **AES-GCM RustCrypto wrapper** (0.5 day) — unblocks DR's AEAD layer.
3. **Wire signal-spqr-hax / doubleratchet-hax to our crate** (1 wk) — first
   end-to-end DR with our verified primitives.
4. **PQXDH on top of C2 + libcrux ML-KEM** (1 wk).
5. **Sender Keys via CatCrypt SymmRatchet** (3 days).
6. **Protobuf wire format via prost** (1 day) — pragmatic, matches
   libsignal.

**Total ~3 weeks** to a Signal-protocol-compatible stack running on our
verified primitive backends.  Plus wasm-component integration (track D)
~1 week if signal-wasm's existing X25519+SHA swap pattern extends.
