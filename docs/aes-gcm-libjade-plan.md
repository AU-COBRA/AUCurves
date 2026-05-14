# AES-GCM via libjade — scoping + foundation plan

This note records the survey that preceded any work on roadmap item #13
("bring AES-GCM into the same EC-verified trust regime as the
SHA-2/X25519/ML-KEM-768 leaves"), describes what is already in the
trees and what is missing, and itemises an incremental plan to
authoring an EasyCrypt-grade AES-256-GCM that the Signal-core
`curve25519-jasmin-rs::symmetric` module could feature-gate against.

The interim libcrux/HACL backend that landed earlier this session
(Cargo feature `aes_gcm_libcrux` in
`$WORKSPACE/curve25519-jasmin-rs/src/symmetric.rs`)
already moves AES-GCM trust off the RustCrypto crate authors and
onto F\*/HACL\* + Cryspen.  Nothing below proposes touching that
backend or `symmetric.rs`; this is a parallel longer-horizon track.

## §1 — Survey results

### §1.1 libjade AES-CTR

**Result: NOT PRESENT.**

The libjade clone at `$WORKSPACE/libjade` (HEAD
`9426b32 Dilithium: remove suspicious annotations`) has no AES at
all — neither Jasmin source nor EasyCrypt proof.  The complete list
of cryptographic primitives under `libjade/proof/` is:

```
proof/crypto_hash/{sha256, sha512, sha3-224, sha3-256, sha3-384, sha3-512}
proof/crypto_xof/{shake128, shake256}
proof/crypto_onetimeauth/poly1305
proof/crypto_stream/{chacha, salsa20, xsalsa20}
proof/crypto_secretbox/xsalsa20poly1305
proof/crypto_scalarmult/curve25519/amd64/{mulx, ref4, ref5}
proof/crypto_kem/{kyber, xwing}
proof/crypto_sign/{dilithium, falcon}
proof/crypto_verify/16
proof/common/keccak
```

No `crypto_aead/`, no `aes`, no `gcm`, no `ghash` anywhere under
`proof/`, `oldsrc-should-delete/`, `test/`, or `bench/`.  The
submodules (`crypto-specs`, `formosa-25519`, `formosa-mlkem`,
`ssbd-tools`) likewise contain no AES artefact.  The sibling clone
`$WORKSPACE/formosa-25519` is also AES-free.

This contradicts the brief's optimistic assumption that
`libjade/proof/crypto_aead/aes256ctr/` exists.  It does not, in this
checkout.  (There is an out-of-tree formosa-aes project at
`https://github.com/formosa-crypto/formosa-aes` that has historically
contained Jasmin AES-CTR, but it is not vendored here and the
release-package README of libjade does not list AES among supported
primitives.)

So: building "AES-GCM on top of libjade's EC-verified AES-CTR" first
requires either *vendoring formosa-aes* (or its successor) into our
tree or *authoring* the AES-CTR Jasmin source plus EasyCrypt proof
from scratch.  Both options are upstream-style efforts, not a
session-scale wiring task.

### §1.2 libjade GHASH / CLMUL building blocks

**Result: NO GHASH spec; CLMUL instruction semantics ARE present in
Jasmin's Rocq proofs.**

There is no GHASH or AES-GCM construction anywhere in libjade.  But
the carryless-multiplication primitive that GHASH is built on top of
is fully present at the Jasmin instruction-set level:

  * `jasmin/proofs/compiler/x86_instr_decl.v:2077` defines
    `wclmulq : u64 → u64 → u128` as a foldr over bits — the
    GF(2)-carryless 64×64→128 multiplication that PCLMULQDQ
    implements.
  * `jasmin/proofs/compiler/x86_instr_decl.v:2081` lifts that to
    `wVPCLMULDQD` (the immediate-controlled 128-bit/256-bit form
    used by both `PCLMULQDQ` and `VPCLMULQDQ`).
  * `jasmin/proofs/compiler/x86_instr_decl.v:188–189` enumerates
    `AESENC`, `VAESENC` etc. as ops; `jasmin/proofs/lang/waes.v:197`
    gives the verified Rocq semantics
    `wAESENC (state rkey : u128) := ...` matching FIPS-197 round
    semantics.
  * `jasmin/compiler/tests/success/x86-64/aes.jazz` and
    `aes_instr.jazz` contain a single-block AES-128 *encryption*
    reference (key schedule + `_aes_enc`).  It is a compiler test
    fixture, not a verified primitive — there is no EasyCrypt proof
    backing it and the file is single-block, single-key-length, not
    a CTR-mode driver.

Practical consequence: the *instructions* needed for both
AES-256-CTR and GHASH already have Rocq semantics inside the
verified Jasmin compiler.  The work to add is

  * Jasmin source for AES-256 key schedule (we have AES-128 key
    schedule as a starting reference)
  * Jasmin source for the CTR driver (counter increment + xor with
    keystream block)
  * Jasmin source for GHASH (Horner schedule of `wclmulq` plus
    GF(2¹²⁸) reduction with the polynomial x¹²⁸ + x⁷ + x² + x + 1)
  * Jasmin source for the GCM tag construction (lengths-block,
    encrypt-counter-zero, xor)
  * EasyCrypt functional-correctness proofs for each
  * EasyCrypt constant-time proofs for each

### §1.3 Existing AES-GCM artefacts inside the BLS workspace

These are *not* libjade but are relevant context:

  * `$WORKSPACE/curve25519-jasmin-rs/src/symmetric.rs:332-378`
    — feature-gated libcrux/HACL AES-256-GCM backend (current
    production verified path).
  * `$WORKSPACE/../SSProve-lean/aesgcm-hax/` — hax-extracted
    Rust AES-GCM crate; pure-Rust reference suitable for
    cross-checking.
  * `$WORKSPACE/../SSProve-lean/CatCrypt/Crypto/AESGCM/`
    (`ConcreteAEAD.lean`, `GCMSecurity.lean`, `GCMReduction.lean`,
    `GCMQuantumUC.lean`, `TightReduction.lean`, …) — SSProve-lean
    security proofs at the spec level (game-based, not
    implementation).
  * `$WORKSPACE/../SSProve-lean/CatCrypt/Crypto/Jasmin/AES/`
    (`AESSpec.lean`, `AESJazz.lean`, `AESEquiv.lean`, `AESPRF.lean`,
    `AESCryptoSSA.lean`, `AESEndToEnd.lean`) — Lean spec of AES-128
    plus a Jasmin-emit + equivalence harness.  This is the closest
    in-tree analogue to what we'd need for AES-256-CTR, but it stops
    at single-block AES-128 and does not cover GCM or any GF(2¹²⁸)
    arithmetic.

So the *trust regime parts of an AES-GCM stack* are partly present in
Lean (security games, AES-128 spec), partly present in Rocq/Jasmin
(instruction semantics, compiler correctness, GF(2) multiplier), and
entirely absent in the production EC pipeline (no
`crypto_aead/aes256gcm/extracted_ct_proof.ec`, no functional
correctness theorem, no CT theorem).

## §2 — Architecture (target)

```
+-----------------------------------------------------------------+
|                  Rust caller (curve25519-jasmin-rs)             |
|       aes256_gcm_encrypt / _decrypt in symmetric.rs             |
+-----------------------------------------------------------------+
                              | feature = "aes_gcm_libjade"
                              v
+-----------------------------------------------------------------+
|         extern "C" jade_aead_aes256_gcm_{encrypt,decrypt}       |
|         linked in via curve25519-jasmin-rs/build.rs             |
+-----------------------------------------------------------------+
                              |
                              v
+-----------------------------------------------------------------+
|              Jasmin source (formosa-aes vendoring)              |
|   crypto_aead/aes256gcm/amd64/{ref, mulx, aesni, vaes}/*.jazz   |
|                                                                 |
|  - aes256_keysched.jazz   (key schedule, 14 rounds)             |
|  - aes256_ctr.jazz        (counter-mode driver)                 |
|  - ghash.jazz             (PCLMULQDQ + reduce)                  |
|  - aes256_gcm.jazz        (top-level AEAD: AAD/CT/lengths/tag)  |
+-----------------------------------------------------------------+
                              |
                              | rocq Jasmin compiler (Qed)
                              v
+-----------------------------------------------------------------+
|         AMD64 assembly (System V ABI)  -- shipped object        |
+-----------------------------------------------------------------+

+-----------------------------------------------------------------+
|        Parallel proof obligations  (EasyCrypt or Rocq)          |
|                                                                 |
|  EC functional:                                                 |
|    aes256_keysched   ≡ FIPS-197 key schedule (256-bit key)      |
|    aes256_ctr        ≡ NIST SP 800-38A CTR mode                 |
|    ghash             ≡ NIST SP 800-38D GHASH (Horner over       |
|                          GF(2^128) mod x^128+x^7+x^2+x+1)       |
|    aes256_gcm        ≡ NIST SP 800-38D GCM                      |
|                                                                 |
|  EC constant-time:                                              |
|    every leaf above CT-proved against secret = {K, P, ...}      |
+-----------------------------------------------------------------+
```

Composition: the four Jasmin leaves compose by Jasmin's program
logic / Hoare triples in EC.  The top-level `aes256_gcm` proof reduces
to `aes256_keysched ∘ aes256_ctr ∘ ghash` plus a small bookkeeping
argument (length-block construction, encrypt-counter-zero, final xor)
— the same shape as Boudot-Rondepierre / Almeida et al. proofs for
ChaCha20Poly1305 already done in `crypto_secretbox/xsalsa20poly1305`.

## §3 — Scope of new EC work

Estimate units: a "session" is ~1 focused multi-hour pass.  Numbers
are best-case; CT proofs in EC routinely double once edge cases
surface.

| Component                                  | Authoring (Jasmin) | EC functional | EC CT | Sessions |
|--------------------------------------------|--------------------|---------------|-------|----------|
| AES-256 key schedule                       | reuse AES-128 ref  | small         | small | 2        |
| AES-256-CTR driver (single + multi-block)  | ~150 LoC Jasmin    | medium        | small | 3-4      |
| GHASH (Horner, PCLMULQDQ + reduction)      | ~80 LoC Jasmin     | **large**     | medium| 4-5      |
| GCM tag composition (AAD ∥ CT ∥ lens)      | ~60 LoC Jasmin     | small         | small | 1-2      |
| End-to-end `aes256_gcm` correctness        | n/a                | medium        | medium| 2        |
| End-to-end CT (post-CT-of-leaves)          | n/a                | n/a           | medium| 1-2      |
| KAT validation (NIST CAVS / Wycheproof)    | n/a                | n/a           | n/a   | 1        |
| Rust extern wiring + feature flag          | ~30 LoC Rust       | n/a           | n/a   | 1        |
| **Total**                                  |                    |               |       | **15-19**|

The single largest piece is GHASH: NIST SP 800-38D's bit-reversed
convention for GF(2¹²⁸) interacts badly with PCLMULQDQ's natural
little-endian limb layout, and EC proofs of the standard
Gueron–Kounavis reduction trick have historically been the work-item
with the worst friction-to-LoC ratio in HACL\*/libjade-style projects.

Faster alternative routes (each shaves a couple of sessions but
narrows the gain):

  * Skip the `aesni` and `vaes` Jasmin variants; ship only `ref` and
    `mulx` (AES-NI but scalar CLMUL).  Cuts ~3 sessions.  We do this
    for X25519 (only `mulx` is the production-linked variant).
  * Reuse the Formosa Crypto formosa-aes EC proof if it exists at
    the time we vendor it (formosa-aes would be a sibling of
    formosa-mlkem, multi-institution authorship — NOT Cryspen, which
    authors libcrux's separate Rust ML-KEM/AES paths).  Then we own
    only the build glue.  TBD.

## §4 — Trust transfer and `LibjadeAxioms.v` impact

The new entries that would land in
`$WORKSPACE/AUCurves/src/Bedrock/LibjadeAxioms.v` once
the EC proofs are written are listed below.  All would follow the
existing pattern (placeholder body `True`, with provenance comment
pointing at the EC file, awaiting a Rocq-side functional spec to
upgrade the body to a real equality):

```coq
(* §5.  AEAD: AES-256-GCM (to be added) *)

(** [jade_aead_aes256_gcm_encrypt] computes RFC 5288 / SP 800-38D
    AES-256-GCM AEAD encryption over key, IV, AAD, plaintext;
    writes ciphertext + 16-byte tag.

    EC provenance: libjade/proof/crypto_aead/aes256gcm/amd64/mulx/
                   extracted_ct_proof.ec   (TBD — not yet authored) *)
Axiom jade_aead_aes256_gcm_encrypt_correct :
  forall (key iv aad pt : list Z) (ct tag : list Z),
    True (* placeholder; see plan in docs/aes-gcm-libjade-plan.md *).

Axiom jade_aead_aes256_gcm_decrypt_correct :
  forall (key iv aad ct tag : list Z) (pt : list Z) (ok : bool),
    True (* placeholder; see plan in docs/aes-gcm-libjade-plan.md *).

(** Trust-localisation note: until the EC proof exists, these axioms
    are vacuous (True); the *name* is still useful as the trust
    handle for `cargo +stable build --features aes_gcm_libjade`
    consumers — the same convention as
    [jade_curve25519_x25519_correct].  Greppable tag: TBD. *)
```

When the EC proof lands, the bodies upgrade to actual equalities
against a Rocq-side AES-GCM functional spec (which we would write by
porting NIST SP 800-38D verbatim — ~200 LoC Gallina).  We can also
upgrade these from `Axiom` to `Theorem` by composing the verified
Jasmin compiler's correctness with the (ported) EC functional spec.

## §5 — Comparison to the libcrux/HACL path (already in production)

Both paths reduce AES-GCM trust off RustCrypto.  They differ in
*which* external project's proof we depend on, and on linkage
strategy.

| Aspect                          | libcrux/HACL (today)           | libjade (proposed)                |
|---------------------------------|--------------------------------|-----------------------------------|
| Cargo feature                   | `aes_gcm_libcrux`              | `aes_gcm_libjade` (planned)       |
| Source language                 | F\*                            | Jasmin                            |
| Proof assistant                 | F\* + Z3 SMT                   | EasyCrypt + (Rocq for compiler)   |
| Compiled by                     | KaRaMeL / Kremlin → C → rustc  | Rocq Jasmin compiler → AMD64 asm  |
| Compiler trust                  | KaRaMeL + clang/rustc          | **Rocq Qed (no SMT, no clang)**   |
| Constant-time guarantee         | F\* secret-int discipline      | EasyCrypt CT proof on .jazz       |
| Functional correctness          | F\* against HACL spec          | EasyCrypt against SP 800-38D spec |
| Supply-chain hops               | Cryspen tarball + libcrux crate| AUCurves-vendored .jazz           |
| Lines of trust outside Cryspen  | ~30k C from KaRaMeL            | ~400 .jazz + 0 C                  |
| Status                          | **shipping** (feature-gate ON) | **plan only**                     |
| Authoring effort to land        | done                           | 15-19 sessions (see §3)           |

When does each path apply?

  * **libcrux/HACL** is the default-on, ready-now backend.  Use for
    any production deployment today and for the duration of the
    libjade-path authoring window.  Trust: F\*/HACL\* + Z3 + KaRaMeL
    + clang.
  * **libjade** would be selected when (a) the EC proof closes and
    (b) the consumer wants a single-prover, no-SMT, no-C-compiler
    trust regime matching SHA-2 and X25519's regime.  Trust: EC +
    Rocq (Jasmin compiler) + AMD64-microarchitecture.

The paths coexist: nothing in the libcrux integration prevents the
libjade integration; both are independent feature flags on the same
`aes256_gcm_encrypt`/`_decrypt` surface.  Default-on remains libcrux
until libjade ships; both can be turned on simultaneously to A/B test
or to compose CI gates.

## §6 — Concrete next steps (one per session)

Items are roughly ordered by dependency.  Each should be a single
focused session and each ends with a committed deliverable in
AUCurves (`src/` or `docs/`) or a tagged branch in the relevant
sibling repo (formosa-aes vendoring decision).

  1. **Decide on formosa-aes vendoring vs. authoring from scratch.**
     Inspect upstream `formosa-crypto/formosa-aes` for AES-256-CTR
     Jasmin source + any extant EC proof.  If it exists and licenses
     are compatible, vendor it as a `BLS/formosa-aes` sibling clone
     and point `libjade-comparison.md` at it.  If not, plan to
     author from the AES-128 single-block reference at
     `jasmin/compiler/tests/success/x86-64/aes.jazz`.
     *Deliverable*: ADR-style note in `docs/aes-gcm-vendoring.md`.

  2. **Land the placeholder axiom triple in LibjadeAxioms.v.**
     Add the §5 block from this document with `True` bodies and
     `TBD` provenance.  Confirm `dune build` is clean.
     *Deliverable*: 1 commit, 1 file touched.

  3. **Land the Rust feature-flag stub.**  Mirror the existing
     `aes_gcm_libcrux` shape in `Cargo.toml` and `symmetric.rs`,
     gated behind `aes_gcm_libjade`.  Body is a `todo!()` with a
     comment pointing back at this plan.  No symbol-link yet.
     *Deliverable*: 1 commit, 2 files touched (Cargo.toml,
     symmetric.rs).  **Note**: explicitly out of scope of *this*
     session per the task instructions; deferred to a future session
     after the EC proof has any actual artefact to link against.

  4. **Author AES-256 key schedule .jazz + EC functional proof.**
     Extend the AES-128 fixture; prove equivalence to FIPS-197 key
     schedule.
     *Deliverable*: new directory `formosa-aes/.../keysched/`,
     extracted_ct_proof.ec passes.

  5. **Author AES-256-CTR driver .jazz + EC functional proof.**
     Reduces to "encrypt N counter blocks and xor".
     *Deliverable*: extracted_ct_proof.ec passes, NIST CAVS vectors
     match in `test/`.

  6. **Author GHASH .jazz + EC functional proof.**  Implement the
     Horner schedule using `wVPCLMULDQD`, then the Gueron–Kounavis
     reduction.  Cross-check with NIST SP 800-38D vectors.
     *Deliverable*: extracted_ct_proof.ec passes.

  7. **Author top-level AES-256-GCM .jazz + EC functional proof.**
     Compose keysched + CTR + GHASH + tag construction.
     *Deliverable*: extracted_ct_proof.ec passes; KAT vectors from
     Wycheproof match.

  8. **Add EC constant-time proofs for each leaf.**  Track via
     `make check_sct` under the libjade build.  Most leaves should
     drop out of the AES-NI + PCLMULQDQ data-independence of those
     instructions; the only typically-nontrivial CT obligation is
     the lengths-block formation in GCM tag emit.
     *Deliverable*: every leaf has a CT certificate.

  9. **Wire the symbol export and link into curve25519-jasmin-rs.**
     Update `build.rs` to assemble the Jasmin output and the Cargo
     feature `aes_gcm_libjade` to link the new symbols.  Reuse the
     pattern from X25519 wiring.
     *Deliverable*: `cargo test --features aes_gcm_libjade` passes
     the existing AES-GCM KAT in `symmetric.rs`.

  10. **Upgrade `LibjadeAxioms.v` placeholders to real equalities.**
      Author a small AES-GCM Gallina spec (~200 LoC) verbatim from
      SP 800-38D; replace `True` bodies with the equality
      statement.  Strip `TBD` tags.
      *Deliverable*: 0 `TBD` axioms remain for AEAD; `Print
      Assumptions` of any downstream consumer (e.g.
      Signal-stack-roadmap files) shows the named axioms with real
      bodies.

  11. **(Optional)** Promote axioms to theorems by composing with
      Rocq Jasmin compiler's correctness statement.

  12. **(Optional)** Bench `aes_gcm_libjade` vs `aes_gcm_libcrux` vs
      default RustCrypto; document in `catcrypt-bench/`.

## §7 — Risks / open questions

  * **formosa-aes upstream status.** If the upstream project is
    stale, vendoring is dangerous; authoring from scratch is the
    fall-back, doubling step §6.4–§6.6.
  * **EC switch compatibility.** Our pinned EC switch must match
    the one libjade is currently authored against.  Re-verifying
    against a newer EC may produce friction; see the existing
    audit checklist for SHA-2 in `LibjadeAxioms.v`.
  * **GF(2¹²⁸) reduction proof.** The Gueron–Kounavis identity is
    well-known but historically painful to mechanise.  Budget at
    least one full session just for that lemma; consider whether a
    direct bit-by-bit proof (slow but easy) is acceptable for
    correctness even if the implementation uses the fast trick.
  * **Vendor lock-in vs. proof reusability.** If we author
    AES-256-GCM in AUCurves rather than upstream, the cost of
    maintaining it (against EC version drift) falls on us.
    Upstreaming to formosa-aes is the long-term right move.

## §8 — What this session did

This session produced:

  * The survey in §1 (no AES in libjade; CLMUL semantics present in
    Jasmin Rocq).
  * The architecture sketch in §2.
  * The 15-19-session estimate in §3.
  * The trust-transfer impact analysis in §4.
  * The side-by-side comparison with the in-production libcrux path
    in §5.
  * The step-by-step itemised plan in §6.

This session did **NOT**:

  * Touch `curve25519-jasmin-rs/src/symmetric.rs` (the libcrux
    backend remains as shipped this session).
  * Touch `LibjadeAxioms.v` (no axioms added yet; deferred to step
    §6.2 per the brief's tagging rule).
  * Modify the `aes_gcm_libcrux` Cargo feature.

Tagging convention for future sessions: any axiom added per §6.2
must carry the literal token `TBD` in its provenance comment and
the literal token `placeholder` in its body comment, so that
`grep -rn "TBD\|placeholder" src/Bedrock/LibjadeAxioms.v` lists all
non-stabilised entries.
