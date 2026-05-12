# libjade / formosa-25519 vs AUCurves `rust_cmd_ed` — comparison

This note documents the result of a code-and-proof survey of the
Formosa-Crypto family (libjade and the standalone formosa-25519
repository) against the `rust_cmd_ed` verification framework in
AUCurves.  The motivating question is: for someone writing a *new*
elliptic-curve cryptographic protocol (Schnorr proof of knowledge,
Pedersen commitments, BBS+ signatures, …) and wanting an
end-to-end-verified high-speed implementation, which pipeline is
the better fit?

## Executive summary

libjade is a verified post-quantum library written in Jasmin and proved
in EasyCrypt.  Its scope is intentionally narrow: hash/XOF, stream
ciphers, Poly1305, Curve25519 (X25519, not Ed25519), Kyber, and
Falcon-verify.  **There is no Ed25519 anywhere in libjade or
formosa-25519, neither as Jasmin source nor as EasyCrypt proof.**  The
only ed25519-relevant artifact is libjade's `oldsrc-should-delete`
tree, which contains *no* ed25519 either — only Dilithium and Falcon
sources.  Its present coverage of curves stops at the Montgomery
X25519 scalar-mult primitive.  By contrast, AUCurves' `rust_cmd_ed`
framework was built specifically to take a Gallina protocol body to
safe Rust with a single end-to-end Qed; it already wires Ed25519
sign, plus Schnorr and Pedersen, and is the only one of the two that
exposes a protocol-level composability story.  The two projects have
*complementary* strengths and we recommend a hybrid usage: prefer
libjade's CT-discipline and assembly back-end for leaf field
primitives where it has coverage; prefer `rust_cmd_ed` for everything
*above* the multiplier (curve, hash chaining, protocol).

## §1 — libjade artifact inventory

Surveyed at `$WORKSPACE/libjade` and
`$WORKSPACE/formosa-25519`.

### What is there

Cryptographic operations under `libjade/proof/`:

- `crypto_scalarmult/curve25519` (X25519: ref4, ref5, mulx, each AMD64)
- `crypto_hash/{sha256,sha512,sha3-{224,256,384,512}}` (AMD64 ref / AVX2)
- `crypto_xof/{shake128,shake256}` (AMD64)
- `crypto_onetimeauth/poly1305` (AMD64 AVX2: Rep5Limb spec, Hop1
  equivalence, Sandy-Bridge AVX2 equivalence; ~1500 LoC EC)
- `crypto_stream/{chacha,salsa20,xsalsa20}` (AMD64)
- `crypto_secretbox/xsalsa20poly1305` (AMD64)
- `crypto_kem/{kyber/{kyber512,kyber768},xwing}`  (AMD64)
- `crypto_sign/{dilithium/{dilithium2,3,5},falcon/falcon512}` — the
  proof directories under `crypto_sign/` are present but contain
  **only `.gitkeep` files**.  No EC proofs at all; the README's signing
  bullet is commented-out.
- `common/keccak/keccak1600` (AMD64)

55 `.ec` files total in `libjade/proof`, ~8 400 LoC.  Most are
constant-time proofs of the form `equiv f ~ f : ={leakages, args} ==>
={leakages}` discharged with `proc; inline *; sim => />.` (8-line
files per primitive variant).

### Where Ed25519 lives — nowhere

`find $WORKSPACE/libjade -name "*.jazz" -o -name "*.jinc"`
returns **no file mentioning Ed25519, Edwards or sign**.  Likewise
`formosa-25519` is X25519-only:
`$WORKSPACE/formosa-25519/src/crypto_scalarmult/curve25519/{ref4,ref5,mulx}/scalarmult.jazz`.
The `oldsrc-should-delete/crypto_sign` tree contains only Dilithium
and Falcon; no Ed25519 binary or source has ever lived in the repo.
The README's primitive list (line 36-37) confirms: signatures = only
"Falcon512 (verification only)".

### formosa-25519 X25519 proofs

These are the *functional-correctness* proofs that libjade leaves
out.  Structure (under `proof/crypto_scalarmult/curve25519/amd64/`):

| File | LoC | Purpose |
|---|---:|---|
| `common/Curve25519_Spec.ec` | 64 | high-level spec (montgomery ladder) |
| `common/Curve25519_Procedures.ec` | 622 | mid-level procedure model |
| `common/Curve25519_Operations.ec` | 572 | hoare/phoare lemmas at op level |
| `common/Curve25519_PHoare.ec` | 204 | wrappers |
| `common/Zp_25519.ec`, `Zp_limbs.ec`, `EClib.ec` | 620 | finite field + limb |
| `ref4/CorrectnessProof_Ref4.ec` | 1159 | per-impl 4-limb refinement |
| `ref4/CorrectnessProof_ToBytes.ec` | 1059 | byte (de)serialisation |
| `mulx/CorrectnessProof_Mulx.ec` | 1139 | per-impl mulx (BMI2) refinement |
| **total** | **5 439** | for one curve, ladder only |

Jasmin source for the corresponding two variants (ref4 + mulx, plus
shared common) totals **2 133 LoC**.  **Proof : source ratio ≈ 2.55:1**
for X25519 alone.

A spot check shows the ref4 correctness proof file has **7 `admit`
markers** (and the mulx variant has 4): the addition, subtraction,
mul-by-a24, multiplication and squaring hoares are stated but their
bodies are admitted at the time of writing.  The lossless and phoare
wrappers are then derived from those admitted hoares.  The repository
is presented as proven, but the LoC totals include this large
unfinished surface.

## §2 — Proof tooling and trust base

### libjade — three layers

1. **Jasmin compiler** (Rocq-proved) — preserves semantics and
   secret-independence of control flow / memory-access location
   through compilation.  This is the only piece that connects
   the Jasmin source to actual x86_64 asm.
2. **EasyCrypt constant-time proofs** — `extracted_ct_proof.ec`
   files use the Jasmin `M.leakages` instrumentation and discharge
   `={leakages, args} ==> ={leakages}` with `proc; inline *; sim`.
   The compiler's CT preservation theorem turns that into asm-level
   secret-independence.
3. **EasyCrypt functional-correctness proofs** — lives in
   formosa-25519 (not libjade itself for X25519).  Connects the
   Jasmin program model to a Gallina-style mathematical spec
   (`spec_montgomery_ladder` etc.).

**Trust base** for libjade-extracted asm:

- Jasmin compiler (Coq/Rocq theorems about asm semantics + leakage)
- EasyCrypt kernel + axiomatisation
- the Jasmin source itself
- assumptions about the AT&T assembler and the AMD64 ABI

### AUCurves `rust_cmd_ed` — Rocq end-to-end

A Rocq-defined AST `rust_cmd_ed` is compiled by `rs_func_emit` to a
safe-Rust `Vec<u8>`.  Strong correctness theorems live in
`src/Bedrock/SafeRustEd25519WPBridge.v` (1840 LoC) and friends.

Trust base for AUCurves-extracted safe Rust:

- Rocq kernel
- `RustCmdToRust.v`'s emit function (pure Gallina, Closed)
- `sha512_full_spec` axiom (the only Closed-but-not-Qed input, used
  as the abstract SHA-512 oracle; behaviorally checked against
  RFC 6234 KATs in the bench harness)
- rustc + the LLVM back-end

The chain `rust_cmd_ed → rust_exec_ed → strong correctness → Gallina
spec` has 0 admits across the Ed25519 path; see `bridge_complete` at
`src/Bedrock/RustCmdRupicola.v:1771`.

## §3 — Side-by-side comparison

| Aspect | libjade / formosa-25519 | AUCurves `rust_cmd_ed` |
|---|---|---|
| Source language | Jasmin (low-level structured, with explicit registers, flags, MMX/AVX) | `rust_cmd_ed` AST in Rocq |
| Output | x86_64 AT&T asm (`.s`) | safe Rust (`.rs`) |
| Coverage of Ed25519 sign | **none** — X25519 only | full sign + verify, single Qed end-to-end |
| Verification target | EC pRHL `equiv ... ==> ...` and pHL `phoare [...] = 1%r` per Jasmin function, ad-hoc per implementation variant | Rocq `Theorem`s against Gallina ref spec |
| Proof tool | EasyCrypt (interactive + SMT) + Jasmin's verified compiler | Rocq + Rupicola-style compile tactics |
| Trust base | Jasmin compiler Rocq proofs + EasyCrypt kernel + leakage model | Rocq kernel + `RustCmdToRust` emit + `sha512_full_spec` |
| End-to-end theorem | `eq_spec_impl_scalarmult_jade_ref4` at `CorrectnessProof_Ref4.ec:1045` (ref4); `_mulx` analogue in `CorrectnessProof_Mulx.ec`.  No single statement spans more than one Jasmin function | `ed25519_sign_strong_correct` (and `bridge_complete`) |
| Constant-time discipline | Jasmin compiler's verified leakage preservation + EC `M.leakages` lemma per primitive | `SafeRustEd25519CTLevel.v` types REdSelect-only branching on secrets; AST-level static check |
| Composition across primitives | none — every primitive is a separate Jasmin program with its own EC proof; no shared callee abstraction | shared leaf library, 6 protocols use the same 5 core leaves |
| Performance | dalek-class for X25519 (ref/mulx in formosa-25519), > dalek for SHA-512, Kyber, ChaCha20 | ~1.96× dalek for Ed25519 sign today (5×40-byte field encoding overhead) |
| Source : proof ratio (X25519 example) | 2 133 LoC source → 5 439 LoC proof = 2.55× | leaf field ops imported from fiat-crypto; protocol-level Sign + Verify ≈ 600 LoC source → ~700 LoC Strong_Correctness |
| Effort estimate | reportedly multi-year for one verified curve + supporting prims (Curve25519 alone has > 5 000 LoC EC); maintained by the multi-institution Formosa team | ≈ 6 months for the framework + ~days per new protocol (Schnorr Strong_Correctness is 704 LoC, Pedersen 408 LoC) |
| Reusability across protocols | low — each protocol stands alone | high — Pedersen / Schnorr / Ed25519 share leaf library |

## §4 — Convenience for adding a new protocol

### libjade route

1. Implement the protocol from scratch in Jasmin.  This means
   writing curve-level (e.g., scalar mult / twisted-Edwards add) and
   protocol-level (e.g., challenge hash chaining) code, plus any
   missing field primitives.  For Ed25519 sign this would mean
   bringing in Edwards arithmetic that doesn't exist anywhere in the
   Formosa ecosystem.  (X25519 has *Montgomery* arithmetic, not
   directly reusable.)
2. Write an EasyCrypt high-level spec.  In `Curve25519_Spec.ec` style
   this is a clean Gallina-shaped model.
3. Write a procedural-model file (`*_Procedures.ec`) — the
   intermediate.
4. Write per-operation hoare / lossless / phoare lemmas
   (`*_Operations.ec`, hundreds of lemmas in current proofs, several
   of them admitted).
5. Write a refinement file (`CorrectnessProof_*.ec`) that lifts
   per-op hoares to full-program equivalence.
6. Write a CT proof (`extracted_ct_proof.ec`) — 8 lines per variant.
7. Maintain three implementation variants in parallel (ref / mulx /
   ref5 in X25519's case) so the asm coverage spans CPU feature
   sets.

For Ed25519 sign with Edwards-XYZT this would be a >5 000-LoC EC
proof effort, likely 6-12 months for a verifier already fluent in
EasyCrypt.

### AUCurves route

1. Write the protocol body as `rust_cmd_ed` AST in a `*_RustCmd.v`
   file.  Pedersen `Commit_RustCmd.v` is 93 LoC, Pedersen
   `Open_RustCmd.v` 97 LoC, Schnorr `Sign_RustCmd.v` 144 LoC,
   Schnorr `Verify_RustCmd.v` 159 LoC.  Body size scales with
   number of protocol steps, **not** with field-arithmetic detail
   (that's all in leaves).
2. Write a `Strong_Correctness.v` (Pedersen 408 LoC, Schnorr 704
   LoC) that connects `rust_exec_ed` of the body to the Gallina
   protocol spec.  ≈300-700 LoC per new protocol.
3. Reuse leaves: the 5 core leaves (square, mul, add, sub, sha512)
   need no new bridges; 4 of 5 are shared across all 6 current
   protocols.
4. The CT discipline is discharged by the AST type system
   (`RustCmdRupicolaTyped.v` + `SafeRustEd25519CTLevel.v`).
5. Extraction: one call to `rs_func_emit` writes a `.rs` file
   directly into the cargo crate at `curve25519-jasmin-rs/`.  No
   per-CPU-variant duplication.

A realistic estimate for adding BBS+ signatures or Σ-protocols at
`rust_cmd_ed` level is **3-5 working days** for someone fluent in
Rocq and the existing framework, dominated by the protocol-level
algebraic-correctness proof, not the extraction plumbing.

## §5 — What AUCurves can learn from libjade

1. **Asm-level secret-independence is a stronger guarantee than
   AST-level CT typing.**  Our `REdSelect` discipline forbids
   `match-on-secret-control-flow` in the source, but the
   Jasmin compiler additionally proves that no compiler pass
   *re-introduces* a secret-dependent branch (Spectre v1 protection,
   constant-time-loadstore preservation).  We currently trust rustc
   + LLVM to not insert secret-dependent jumps in safe Rust.  This
   gap is the largest soundness compromise in our pipeline relative
   to libjade.  Recording it as a paper-section caveat is overdue.

2. **Per-implementation variants are useful.**  libjade ships ref4,
   ref5, mulx (BMI2) for X25519 with shared CT discipline.  Our
   pipeline emits exactly one Rust variant, leaning on rustc to
   auto-vectorise where possible.  We could mirror this by emitting
   a `radix-2^51`-encoded leaf alongside the saturated leaf, both
   passing the same strong-correctness theorem.

3. **Spec-as-code is small.**  `Curve25519_Spec.ec` is 64 lines and
   does the whole ladder mathematically.  Our equivalent
   `point_decompress / scalarmult_ed25519` spec is more spread out;
   collecting it into a single short file would help the paper
   reproduce libjade's "this is the *one* statement we want to be
   true" presentation.

4. **`extracted_ct_proof.ec` is a 1-tactic file** (`proc; inline *;
   sim => />.`).  This is essentially what `cmd_ct_ok` does for us,
   modulo automation.  We could expose a 1-line CT discharge tactic
   for new protocols (`rustcmd_ct_proof` macro) so users don't write
   the `cmd_ct_ok` boilerplate by hand.

What libjade does **not** suggest we copy:

- Their unsaturated/limb encoding (radix-2^51 + 5-limb) gives them a
  performance win on Sapphire Rapids — we already evaluated this on
  Zen 4 and saw fiat-radix-2^51 beat all BMI2/IFMA drop-ins (memos
  `reference_bmi2_dropin_loses` and `reference_ifma_zen4_falsified`).
  Our `5×40-byte xyzt` encoding is performance-driven, not a
  best-fit-with-libjade question.

- Their EasyCrypt proof structure (hoare → phoare → equiv) is
  not idiomatic in Rocq; bedrock2 `WeakestPrecondition` and our
  `rhoare` already give us the same expressiveness directly.

## §6 — What libjade can learn from AUCurves

1. **Protocol-level composability via a shared leaf library.**
   libjade has no abstraction layer above "Jasmin function";
   recompiling the same X25519 ladder for use inside a hypothetical
   verified Signal handshake would mean copy-pasting it and
   re-proving equivalence in the new context.  AUCurves' Schnorr,
   Pedersen, and Ed25519 sign all call the *same* `fe_mul_unique`
   and `fe_sub` leaves.  A Jasmin equivalent would need a verified
   inliner that preserves CT analysis across function boundaries.

2. **AST-level CT discipline gives early feedback.**  The Jasmin
   security type system enforces CT after parsing; our `cmd_ct_ok`
   does it on the Rocq AST.  The difference is that we can check CT
   *before* the protocol is even compiled to a target language —
   the protocol author sees `cmd_ct_ok = Some env` or a structural
   "you're branching on a secret here" error in their proof
   development.  A Rocq-modelled Jasmin DSL would inherit the same
   property; libjade's current workflow only checks CT after the
   Jasmin source is complete.

3. **Framework-level Hoare-triple discharge.**  Our `compile_red_*`
   lemmas (in `RustCmdRupicola.v`) form a complete *parallel* WP
   calculus for `rust_cmd_ed`.  Each Hoare rule discharges once and
   is reused across every protocol.  libjade's per-program EC proofs
   re-discharge the analogous obligations every time, contributing
   substantially to its 2.55× source-to-proof ratio for X25519.

4. **Strong-correctness rather than per-function equiv.**
   `eq_spec_impl_scalarmult_jade_ref4` chains several inner equivs
   inside `proc *; inline; wp; call`.  An equivalent `Strong
   Correctness` statement directly relating the spec to the Jasmin
   asm semantics would skip the procedural intermediate and shorten
   proofs.  This may be hard in EasyCrypt's procedural setting, but
   the AUCurves precedent shows it is feasible if the AST is
   semantics-only.

## §7 — Recommendation

For new EC-based protocols (Ed25519 sign was the canonical example;
Schnorr PoK, Pedersen open/commit are next; BBS+ and CL-signatures
are reachable extensions):

- **Use `rust_cmd_ed`** for the protocol-level code, the curve
  arithmetic above the multiplier, the hash chaining, the serialisation,
  and the strong-correctness theorem.  This is the only path that
  gives end-to-end Rocq proof + safe-Rust extraction + zero
  per-protocol axioms (modulo `sha512_full_spec`, which is itself a
  good candidate to swap for an `rust_cmd_ed`-extracted SHA-512).

- **Consume libjade leaves where they fit.**  We already use the
  libjade SHA-512 jasmin source through `formosa-25519` in the
  curve25519-jasmin-rs crate for benchmarks; pushing that asm into
  the production pipeline (with the leakage-preservation guarantee)
  would harden the trust base for the symmetric component.

- For new post-quantum signatures (Dilithium, Falcon), use libjade
  exclusively until `rust_cmd_ed` grows polynomial-arithmetic
  primitives.  These are not on the AUCurves roadmap.

- **Do not** invest in adding Ed25519 to formosa-25519 or libjade
  from scratch; the LoC budget (≈5 000-10 000 EC) would dwarf the
  AUCurves Ed25519 proof we already have, and would produce only an
  asm artefact rather than a Rust crate consumable by the
  libsignal stack.

A reasonable end-state is: AUCurves emits the curve / protocol code
to Rust; the Rust calls into a Jasmin-derived asm for SHA-512 and
(once available) X25519 / Curve448 leaves.  Both pipelines coexist
without duplicating effort, and the trust base of any deployed
artefact is the union of (a) the Rocq kernel, (b) the AUCurves
emit function, (c) the Jasmin compiler proofs, and (d) rustc / LLVM
for the glue.
