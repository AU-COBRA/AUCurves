# Plan: full Signal stack via Rocq primitives + CatCrypt protocols

## Architecture

```
┌──────────────────────────────────────────────────────────────┐
│ signal-wasm component (TCB-contained)                        │
│  ├── X3DH        ─┐                                          │
│  ├── Double Ratchet├── Lean CatCrypt (protocol layer)        │
│  ├── PQXDH        │   - state machines + sec proofs           │
│  ├── Sender Keys  │   - emits rust_cmd → safe Rust            │
│  ├── zkgroup     ─┘                                          │
│  │                                                            │
│  ├── XEdDSA      ─┐                                          │
│  ├── HKDF-SHA*    ├── building-block layer (either side)     │
│  ├── HMAC-SHA*   ─┘                                          │
│  │                                                            │
│  ├── X25519      ─┐                                          │
│  ├── Ed25519      │── Rocq AUCurves (primitive layer)         │
│  ├── SHA-256/512  │   - algebraic correctness                 │
│  ├── AES-GCM      │   - rust_cmd_ed → safe Rust               │
│  ├── ML-KEM-768   │   - jasminc-backed asm where applicable   │
│  ├── Ristretto255│                                            │
│  └── Pedersen-KZG─┘                                          │
└──────────────────────────────────────────────────────────────┘
```

Both extractor pipelines (Rocq's `rust_cmd_ed`, Lean's CatCrypt
`rust_cmd`) emit **safe Rust** into a shared crate
(`signal-crypto-aucurves` or extending `curve25519-jasmin-rs`).  The
Rust ABI is the trust boundary between the two formal frameworks —
both produce `pub unsafe extern "C" fn` with byte-array signatures,
and the Rust compiler is the meeting point.

## Prior art (existing in tree)

- **signal-wasm verified swaps** (per `project_signal_x25519.md`,
  NEXT.md track L):
    - X25519 from Lean DSL → safe Rust ✅
    - SHA-256 from Lean Jasmin AST → safe Rust (via
      `JasminToRustEmit.lean`) ✅
    - libcrux-free in wasm TCB for these two ✅
- **Track L open items** (NEXT.md): XEdDSA, ML-KEM, HKDF.
- **curve25519-jasmin-rs**: X25519 + Ed25519 + SHA-512 wired
  through rust_cmd_ed extraction.
- **AUCurves Commitments + Signal repos**: XEdDSA security proof,
  Poksho special soundness, Pedersen-KZG 4 theorems Qed.

## Tracks

### Track A — Rocq ↔ Lean ABI bridge (~3 days)

The bridge is the Rust ABI; both frameworks emit it.  Work items:

- **A1.** Confirm byte-identical ABIs: Rocq `rust_cmd_ed` and Lean
  CatCrypt `rust_cmd` both emit `pub unsafe extern "C" fn` over
  `*mut u8` / `*const u8` pointers.  Audit signatures of each
  primitive.
- **A2.** Define a shared crate (`signal-crypto-aucurves` or extend
  `curve25519-jasmin-rs`) with `extern "C"` declarations for every
  primitive surface, regardless of which side emits the
  implementation.
- **A3.** Build-time symbol resolution test: link both
  Rocq-emitted and Lean-emitted Rust source into one staticlib,
  verify no symbol collisions, run a smoke KAT.

**Owner:** integration engineer.  **Output:** documented bridge
crate with both sides' emissions composable.

### Track B — Primitive layer (~3 weeks)

Most are done or near-done.

| # | Primitive | Status | Effort | Owner |
|---|---|---|---|---|
| B1 | **X25519** (Jasmin formosa, 26 µs) | ✅ DONE | — | Rocq |
| B2 | **Ed25519 sign/verify** (rust_cmd_ed) | ✅ DONE (2.7× dalek) | — | Rocq |
| B3 | **SHA-512** (libjade Jasmin) | ✅ DONE | — | Rocq |
| B4 | **SHA-256** (libjade Jasmin) | infra exists | 2 days | Rocq |
| B5 | **HMAC-SHA256** | not in tree | 1 day | Rocq or Lean |
| B6 | **HKDF-SHA256** | not in tree (track L3) | 0.5 day | Rocq or Lean |
| B7 | **AES-GCM** (libjade Jasmin) | not in tree | 1 week | Rocq |
| B8 | **XEdDSA** | spec Qed (1 axiom), needs Rust API | 2 days | Rocq |
| B9 | **Ristretto255** | spec done; Rust uses dalek | 1 week (dalek-free) | optional |
| B10 | **Pedersen + Poksho** | 4 theorems Qed; uses dalek | included with B9 | optional |
| B11 | **ML-KEM-768** | NOT IN TREE | see Track A1 | Lean Jasmin or libcrux |

**B11 sub-decision** (per your earlier observation): libcrux or
Jasmin libjade.  Recommend **libcrux for immediate ship + Jasmin for
long-term parity**.  Both have rust_cmd-style emissions; both fit
behind the same `KemBackend` trait in the bridge crate.

### Track C — CatCrypt protocol layer (~6-8 weeks)

This is the meat of the plan.  Each Signal protocol becomes a Lean
CatCrypt module that emits rust_cmd → safe Rust.

| # | Protocol | Inputs | What it does | Effort |
|---|---|---|---|---|
| C1 | **X3DH** | B1, B2, B6, B8 | session setup, 4× DH + signed prekey verify | 1 week |
| C2 | **Double Ratchet** | B1, B5, B6, B7 (AES) | per-message keys, FS, PCS | 3 weeks |
| C3 | **PQXDH** | C1, B11 | PQ-augmented X3DH | 1 week (on top of C1) |
| C4 | **Sender Keys** | B5, B7 | group messaging | 1 week |
| C5 | **zkgroup** | B9, B10 | anonymous group credentials | 2 weeks |
| C6 | **MLS** (optional) | C2's primitives + tree ops | replace Sender Keys long-term | 4 weeks |

For each:
- Lean CatCrypt module with state machine + transition functions.
- rust_cmd emission to safe Rust.
- Functional correctness theorem (Admitted at PoC scope; security
  proof via SSProve game-based in a follow-on).
- KAT against libsignal-protocol reference impl.

**Key insight:** CatCrypt already has the protocol skeletons (per
your statement).  This track is *wiring* — pointing CatCrypt's
`rust_cmd` primitive calls at our Rocq-emitted symbols instead of
CatCrypt's own primitive emissions or libcrux.

### Track D — wasm component integration (~2 weeks)

signal-wasm is the deployment target.  Work items:

- **D1.** Continue Track L primitive swaps: XEdDSA (depends B8),
  ML-KEM (depends B11), HKDF (depends B6).
- **D2.** Add protocol-level swaps: replace libsignal protocol code
  with CatCrypt-emitted protocol code.
- **D3.** TCB-containment audit: ensure CatCrypt-emitted Rust passes
  wasm-component sandboxing requirements (no allocations, bounded
  stack, etc.).
- **D4.** End-to-end interop test: signal-wasm component talking to
  upstream libsignal-protocol clients (Android, iOS, Desktop).

### Track E — Validation (~ongoing)

- **E1.** libsignal KAT — bit-equivalence with reference Rust
  implementation for every protocol step.
- **E2.** Cross-protocol composition tests: X3DH session → 100
  Double-Ratchet messages → re-session.
- **E3.** Adversarial scenario tests: replay, out-of-order
  delivery, post-compromise key rotation, lost-message scenarios.
- **E4.** Public-test-vector matching: RFC vectors where available
  (X3DH spec, Sender Keys spec).

### Track F — Security proofs (research)

User update 2026-05-12: **CatCrypt already has a Double Ratchet
formalization** (per project context).  This significantly collapses
Track F.

- ~~F1. Computational Double Ratchet proof in SSProve (Lean).~~
  **Subsumed by existing CatCrypt DR.**
- **F1' (revised)**: connect CatCrypt's DR proof to our extracted
  Rust impl via the rust_cmd bridge. Verify the executable code
  matches the formalized spec.  ~2 weeks.
- **F2.** X3DH symbolic-to-computational lifting.  Could re-use
  CatCrypt's DR adversary model as a starting point.  ~1 month.
- **F3.** Composition theorem: Bridge primitive-level (Rocq) +
  protocol-level (Lean CatCrypt) into a single end-to-end claim.
  ~2-3 months once F1' + F2 land.

Net: Track F is more like **~3-4 months** of research connectivity
work, not 6+, thanks to CatCrypt's existing DR.

## Critical path

```
B5 (HMAC) → B6 (HKDF) ─┐
B7 (AES-GCM)            ├─→ C2 (Double Ratchet) ─┐
B1 (X25519, done)       │                          ├─→ E (validation)
B2 (Ed25519, done) ─→ B8 (XEdDSA) ─→ C1 (X3DH)   │
                                       ↓           │
                                     C3 (PQXDH) ←──┴── B11 (ML-KEM)
                                                       
C4 (Sender Keys) — independent track, depends on B5+B7
C5 (zkgroup) — independent, depends on B9+B10
```

**Shortest-path-to-shipped X3DH-only Signal session-setup:**
B5 + B6 + B8 + C1 = 1 + 0.5 + 2 + 7 days = **~2 weeks**.

**Shortest-path-to-full-protocol-stack:**
B-track + C-track + D-track = ~3 weeks + ~6-8 weeks + ~2 weeks =
**~3 months** to a libsignal-equivalent verified-extraction stack.

## Bridge ABI principles

Three rules for the Rocq ↔ Lean meeting point:

1. **Byte-level interop.**  Every primitive surface is `extern "C"
   fn name(out: *mut u8, args: *const u8, ...) -> u64`.  No Rust
   newtypes cross the boundary — just byte arrays of known fixed
   sizes (32 byte scalars, 32 byte pubkeys, 64 byte sigs, etc.).
2. **No allocations.**  All buffers caller-supplied.  Matches
   embedded / wasm requirements.
3. **CT discipline.**  Every primitive is constant-time per its
   side's own proof.  The bridge doesn't introduce data-dependent
   branches.

## Trust model

Each layer's trust set:

| Layer | Trusts |
|---|---|
| Rocq primitive | fiat-crypto axioms (~6 algebraic; mostly Qed), Rocq kernel, jasminc compiler (where applicable) |
| Lean CatCrypt protocol | Lean kernel, primitive correctness (handed off via ABI) |
| Bridge | Rust safe-language guarantees (rustc) |
| wasm component | wasm-component sandbox + everything above |
| Production | hardware crypto instructions (AES-NI, SHA-NI, PCLMULQDQ) |

**Composition theorem we'd want** (Track F2/3): "If Rocq primitive
proofs hold AND Lean protocol proofs hold AND rust_cmd extraction
is faithful (both sides), THEN the wasm-deployed Signal stack
matches the protocol spec under arbitrary adversary."  No-one has
proved this for any production cryptographic stack to date.

## Effort budget

| Phase | Calendar | What ships |
|---|---|---|
| **Phase 0** — bridge crate (Track A) | 1 week | composable extraction artefacts |
| **Phase 1** — primitives complete (Track B) | 3 weeks | full verified primitive layer |
| **Phase 2** — X3DH end-to-end (C1) | 2 weeks | session setup ships |
| **Phase 3** — Double Ratchet (C2) | 3 weeks | per-message stack ships |
| **Phase 4** — PQXDH + Sender Keys (C3, C4) | 2 weeks | full 1:1 + group messaging |
| **Phase 5** — zkgroup (C5) | 2 weeks | private group memberships |
| **Phase 6** — wasm + validation (D, E) | 2 weeks | shipping deployment |
| **Total to ship** | **~13 weeks** (~3 months) | libsignal-equivalent verified-extraction stack |
| Phase 7+ — security proofs (F) | ~3-4 months (CatCrypt DR shrinks this) | research-grade end-to-end theorem |

## Open architectural questions

1. **Where to draw the Rocq/Lean line for building blocks?**
   HMAC, HKDF, XEdDSA could live in either framework.  Default:
   put them where their primitive deps are (HMAC under SHA-256
   side, XEdDSA under Ed25519 side).  Negotiable.

2. **Do we need a "verified compose" theorem for B+C?**  Bridging
   Rocq + Lean proofs about each layer's correctness into an
   end-to-end Lean theorem requires a transport step.  For
   functional correctness, "the Rocq-extracted Rust function
   satisfies the Lean spec of that primitive" — provable via
   abstract specification matching.

3. **Where does zkgroup credential issuance live?**  Issuance is
   server-side; verification is client-side.  Our framework is
   client-side-first; server-side credential issuance would need
   either a separate verified server crate or trusting Signal's
   existing one.

4. **MLS or Sender Keys?**  Signal currently ships Sender Keys.
   MLS is the IETF future-direction.  Don't do both initially;
   pick one.

5. **wasm vs native?**  signal-wasm is the demo target; native
   library deployment (libsignal API match) is the longer-term
   production target.  Same Rust crate, different bindings.

## Recommendations

**For the next 4 weeks** (high-confidence wins):
- Complete Phase 0 (bridge audit).
- Complete Phase 1 (B5-B8 wirings).
- Start Phase 2 (X3DH).  Lands the *first* full verified Signal
  protocol via our framework.

**For the next 3 months** (full stack):
- Phases 1-6 as scoped.  Lands a libsignal-equivalent verified
  stack.

**Beyond 3 months:**
- Phase 7+ security proofs (research thesis territory).
- MLS investigation if Signal pivots away from Sender Keys.
- ML-KEM via Jasmin once libjade's ML-KEM stabilizes.
