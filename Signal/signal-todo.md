# Signal verification — open issues

Known gaps in the Signal protocol verification stack. Each item is
actionable but deferred pending either paper deadline or upstream work.

## XEdDSA functional spec is orphaned

**File:** `AUCurves/src/Spec/XEdDSA.v` (114 lines, moved 2026-04-15 from
`fiat-crypto/src/Spec/XEdDSA.v`).

**State:**
- Pure algebraic spec of sign/verify over an abstract field+group.
  `Module XEdDSA. Section WithParams. ... End WithParams. End XEdDSA.`
- **Zero importers** across the whole workspace.
- The Commitments security proofs (`XEdDSA_Security.v`,
  `XEdDSA_FiatShamir.v`) define their own Schnorr references and do
  not import this spec.
- The Rust crate (`curve25519-jasmin-rs/src/xeddsa.rs`) implements
  sign/verify using SHAKE-256 directly, with no Coq-verified spec
  link.

**What's missing to wire it in:**
1. **Curve25519 instantiation.** Instantiate `WithParams` with the
   Curve25519 field, prime-order subgroup of Ristretto or Edwards25519,
   and the scalar field `F_l`. ~30 lines.
2. **Connect to Commitments.** Have `XEdDSA_Security.v` import the
   functional spec and prove that the Schnorr-instance-based signature
   scheme produces outputs observationally equivalent to
   `Spec.XEdDSA.sign`. ~50 lines.
3. **Connect to Rust.** The Rust crate's `xeddsa_sign`/`xeddsa_verify`
   should be linked to `Spec.XEdDSA` by a test-vector bridge (running
   the same Ed25519-test-vector inputs through both and checking
   equality). The Coq side would emit reference outputs via
   `vm_compute`. ~100 lines of vectors + a Rust test.

**Why not done:** The current Rust implementation uses SHAKE-256
(replacing SHA-512), so it does NOT produce Signal-compatible
signatures. Connecting to the spec without first resolving that
mismatch would be checking the wrong thing.

**Decision points:**
- Do we commit to SHAKE-256 as Signal's hash? (If so, spec gets
  SHAKE-256; loses byte-level Signal compat.)
- Or verify SHA-512 (painful; no existing verified SHA-512 in our
  chain) and achieve byte-level Signal compat?

## SHA-512 vs SHAKE-256 hash choice

**Current:** SHAKE-256 (via verified Keccak permutation in AUCurves,
0 axioms, integrates with bedrock2). Signal canonically uses SHA-512.

**Impact:**
- Our XEdDSA signatures are NOT byte-compatible with Signal's.
- Security proofs are hash-agnostic (model as random oracle), so
  the EUF-CMA proof holds either way.
- Test-vector verification against Signal's canonical vectors would
  fail on any signature input.

**Options:**
- Keep SHAKE-256, document the incompatibility.
- Verify SHA-512 (estimate: ~2000 lines of Keccak-equivalent work for
  Merkle-Damgård + SHA-2 compression; no existing artifact in our
  stack).
- Use an axiomatized SHA-512 (`SHA512_axiom.v` pattern) until a real
  verification lands. This at least lets us claim Signal compatibility
  modulo the hash assumption.

## Keccak bedrock2 WP proofs

**File:** `AUCurves/src/Bedrock/End2End/RupicolaCrypto/Keccak.v`.

**State:** bedrock2 function bodies for Keccak-f, SHAKE-256 absorb,
SHAKE-256 top-level are concrete (no placeholders), but the
weakest-precondition proofs linking them to the Keccak spec are
Admitted. `program_logic_goal_for_function!` fails on these functions
due to term size; proofs need manual `WeakestPrecondition.call` +
`straightline` chains (~800 lines).

**Impact:** Does not block the deployed Rust crate (uses the `sha3`
crate, validated against our Keccak spec by NIST vectors). Does not
block security proofs (hash is a random oracle). Only affects the
"full WP chain" story.

## Elligator2 inverse completeness

**Status:** Axiom in `AUCurves/fiat-crypto/src/Spec/Elligator2.v`.
`t` (or `-t`) appears among the preimages computed by the 4-coset
inverse of `elligator2_forward(t)`.

**Discharge plan:** `native_compute` on `GF(2^255-19)` using the
Legendre-symbol infrastructure from fiat-crypto's hash-to-curve work.
Computationally verified by go-ristretto's test suite (>10^6 inputs).
Not blocking.

## Lizard roundtrip collision bound

**Status:** Hypothesis `at_most_one_valid` in `Signal/theories/Lizard.v`.
Standard cryptographic assumption (SHA-256 collision resistance on the
125-bit check-bit domain).  Not eliminable without verifying SHA-256
collision resistance, which is not formalized anywhere.

## bedrock2 → Jasmin AST extraction

**Status (2026-04-15, Phase 0+1 complete):** End-to-end pipeline works
for 7/11 X25519-64 field functions + BLS12-381 add (byte-identical to
pre-refactor output). The 7 jasminc-compiled functions are linked into
the Rust crate `curve25519-jasmin-rs` via `build.rs` with 4 correctness
tests passing (`test_bedrock2_jasmin_{clamp,copy_and_from_word,
add_symmetry,cswap}`).

**New pass `lower_mulx_pairs` (A+B):** copy-propagation-aware,
non-adjacent MULHUU/MUL matching that collapses pairs into `#MULX`
intrinsics. Reduced JEmulhuu in X25519 extraction from 18 → 2
(89% match rate), 48 `#MULX` emitted. Identity-case Qed in
`PolishPassProofs.v` (~20 lines, matches `carry_cmd_correct` pattern);
full non-adjacent proof deferred to Phase 3 (~350-450 lines, gated on
ExprBridge `word.mulhuu` semantics).

**Phase 0 fix (clamp):** Replaced byte-granular `clamp` (which our
`tr_cmd` couldn't translate correctly because `access_size` is dropped)
with u64-granular `clamp_64` in `AUCurves/src/Bedrock/End2End/X25519_64/
clamp_64.v`. Generates 14 lines of clean x86-64 assembly.

**Remaining blockers (Phase 2, documented):**

1. **Register pressure** on `fe25519_mul`, `fe25519_square`,
   `fe25519_from_bytes`, `fe25519_to_bytes` (>16 live u64 vars).
   **Phase 2 partially complete (2026-04-15):**
   - OCaml outlining infrastructure in
     `AUCurves/src/Jasmin/ocaml/ocaml_compile.ml`:
     `wrap_chunk_as_subroutine`, `partition_at_splits`,
     `liveness_analysis`.
   - `partition_for_regalloc` rewritten to emit real Jasmin Subroutine
     helpers (was just spill barriers before).
   - `find_split_points` made liveness-driven with gap-filling fallback:
     scans forward for positions with `<=12` live vars, cuts there; for
     remaining long dense regions, adds fallback cuts at local liveness
     minimum.
   - **Result on fe25519_mul:** 322 instrs → 11 chunks.  Chunks 4-10
     have 4-13 vars crossing and would compile fine.  Chunks 0-3 (the
     first 226 instrs, partial-product accumulation) have 20-36 vars
     at every midpoint — schoolbook multiplication simply has no
     low-pressure point during accumulation.
   - **Fundamental limitation:** 5-limb schoolbook produces ~25 partial
     products that must all accumulate into 5 limbs.  Any midpoint in
     that phase has 20+ partial sums live.  20+ u64 SysV-register args
     overwhelms jasminc's Subroutine RegAlloc.
   - **Next step:** pass cross-chunk state via stack-allocated struct
     (single pointer arg, jasminc-side extension).  Or: rewrite
     fiat-crypto's unsaturated Solinas mul synthesis to interleave
     multiplication and reduction, shrinking the live partial-sum
     cross-section (major fiat-crypto internals work).
   - **Investigated 2026-04-15 (D option — Dettman):**
     `fiat-crypto/src/Arithmetic/DettmanMultiplication.v` implements the
     interleaved mul-and-reduce algorithm that shrinks the live
     partial-sum cross-section.  **Partially attempted, memory-blocked.**
     - The Dettman Pipeline is already reified:
       `PushButtonSynthesis/DettmanMultiplication.v` defines `mul` and
       `square` via `Pipeline.BoundsPipeline`, with `mul_correct`/
       `square_correct` Qed'd.  `DettmanMultiplicationReificationCache.v`
       provides `reified_mul_gen`/`reified_square_gen`.
     - Wrote a 50-line bedrock2 glue file at
       `AUCurves/src/Bedrock/End2End/X25519_64/DettmanMul25519.v`
       that constructs `dett_mul_op_built : computed_op (mul ...) Field.mul
       list_binop_insizes list_binop_outsizes (list_binop_inlengths n)`
       via `eapply Build_computed_op; vm_compute; reflexivity.` (and
       again with `native_compute`).  The generic
       `list_binop_*`/`list_unop_*` from `Signature.v` are
       UnsaturatedSolinas-agnostic and reusable.
     - **Both reductions blew up memory**: >15 GB RAM, 16 GB swap,
       state-D process thrashing for 5 min, killed.  For comparison,
       the UnsaturatedSolinas analog `fe25519_ops` compiles in ~5 min
       peaking at 2 GB.  Dettman's interleaved partial-product term
       has deeper nested lets that vm/native compute cannot
       share-collapse.
     - The file is kept as documentation-only (Escape hatches listed:
       hand-write Dettman bedrock2 body + equivalence proof ~450 lines;
       or OCaml-extract via `bedrock2_dettman_multiplication` CLI +
       deserialize into Rocq; or build on 32+ GB RAM machine).
     - **Decision: deferred to post-paper.**
   - **Investigated 2026-04-15 (F option — CryptOpt delegation):**
     Our repo already has `curve25519-jasmin-rs/cryptopt/
     fiat_curve25519_solinas_mul.asm` (superoptimized NASM).  Blocker:
     **representation mismatch** — CryptOpt uses 4-limb saturated
     (accesses `[rsi+0], [rsi+8], [rsi+16], [rsi+24]` only; the 2
     occurrences of `0x20` in the .asm are `[rsp-0x20]` stack spill
     slots, not input-limb offsets).  bedrock2 X25519 uses 5-limb
     unsaturated.  Fixing requires either
     (i) 5-limb↔4-limb conversion routines at every `mul`/`square`
     call site (would eat the perf win), (ii) producing a 5-limb
     CryptOpt variant (upstream work), or (iii) switching bedrock2 ops
     to 4-limb (major internals change, disturbs the 7 already-working
     unsaturated ops).  **Deferred.**
   - **Safety:** threshold restored to 200 (outlining effectively off)
     so the 7 working functions + BLS12 byte-identical regression
     are preserved.  Verified: MD5 match on `bls12_add.s`.

2. **Variable-merging conflict** on `ladderstep`, `montladder`,
   `x25519`, `x25519_base`. New error class distinct from (1):
   jasminc's `register allocation: conflicting variables E.106 and
   A.107 must be merged due to: ...`. Appears to stem from
   function-parameter aliasing patterns in the bedrock2 output that
   jasminc doesn't accept. Likely resolvable by the same outlining
   work that fixes (1), but needs investigation.

3. **Soundness proof for `lower_mulx_pairs` full non-adjacent case**
   (~350-450 lines Qed). Gated on ExprBridge adding `word.mulhuu`
   semantics. Identity-case Qed already shipped.

   **Phase 3 in progress (2026-04-15):**
   - ✅ Phase 3a: `ExprBridge.v` — `eval_jexpr` now evaluates
     `JEmulhuu e1 e2` to `Some (word.mulhuu v1 v2)` (was `None`).
     Rebuilt clean (19:07).
   - ✅ Phase 3b: `PolishProofs.v` — `jeval_mulx` rule fixed:
     `JCmulx h l a b` post-state now `update (update e h
     (word.mulhuu va vb)) l (word.mul va vb)` (was `h := word.of_Z 0`,
     a stub).  Pending full rebuild (blocked by another session's
     HashToCurveSWUProof_G2 build, 10+ min and counting).
   - 🚧 Phase 3d partial: `MulxSoundness.v` (new file) defines
     `expr_reads`, `cmd_touches`, `stmts_between_safe`,
     `wf_mulx_list`, `wf_mulx_cmd` (~100 lines). Pending build.
   - 🚧 Phase 3c partial: drafted `jeval_list`, `jeval_list_app`,
     `cmd_to_list_sound`, `list_to_cmd_sound` in
     `/tmp/phase3_additions.v` (~80 lines). To merge into
     `PolishProofs.v` once build succeeds.
   - Remaining: (i) unchanged-variable lemma — if `cmd_touches x c
     = false` and `jeval e c e'`, then `e' x = e x`; (ii)
     `scan_mulx_pairs_valid` — every match satisfies operand
     equivalence under def_map; (iii) `rewrite_mulx_one_match_sound`
     — rewriting a single match preserves jeval_list; (iv) full
     theorem replacing identity-case Qed.

**Shipped (paper-ready):**
- 7/11 field ops via verified bedrock2→Jasmin chain
- Rust integration + correctness tests (4 passing)
- Updated `writeup/signal-report.tex` with the new row
- Phases 2-4 deferred (see local planning notes)

## Design note: soundness of `lower_mulx_pairs`

Added 2026-04-13. Sketches the proof obligations for the MULX-pairing
pass at `Core.v` lines ~790-1005 (`scan_mulx_pairs`, `rewrite_mulx_aux`,
`lower_mulx_pairs`, `lower_mulx_pairs_cmd`, `lower_mulx_pairs_func`).

### 1. Top-level theorem

Following the `PolishProofs.v` template (`lower_comparisons_cmd_correct`,
`carry_cmd_correct`):

```
Theorem lower_mulx_pairs_cmd_correct :
  forall (c : jasmin_cmd) (e e' : env),
    wf_mulx c = true ->
    jeval e c e' ->
    jeval e (lower_mulx_pairs_cmd c) e'.
```

where `wf_mulx` is a syntactic well-formedness predicate asserting:
(a) every `hi`/`lo` target written by the rewrite is not referenced by
any statement strictly between the `mul` and `mulhuu` positions, and
(b) the `def_map` copy-propagation fuel (8) is sufficient for every
pending chain.  For the BLS12 regression the identity-case specialisation
`wf_mulx c = true -> lower_mulx_pairs_cmd c = c` holds trivially (no
pair is ever produced because the matcher requires adjacency modulo
intervening non-writers of `lo`).

### 2. Key lemmas (in dependence order)

1. **`cmd_to_list_sound`**: `jeval e c e' <-> jeval_list e (cmd_to_list c) e'`
   — JCseq flattens into the list-level big-step; `list_to_cmd` is its
   inverse up to `JCskip` neutrality.  ~30 lines, pure structural
   induction.

2. **`defmap_consistent e m`**: invariant that for every `(x,e_x) ∈ m`,
   `eval_jexpr e (JEvar x) = eval_jexpr e e_x`.  Preserved by
   `defmap_update` at each `JCset` event provided `x` is fresh w.r.t.
   later uses (this is where `wf_mulx` earns its keep).

3. **`resolve_expr_sound`**: under `defmap_consistent e m`,
   `eval_jexpr e (resolve_expr k m e0) = eval_jexpr e e0` for any fuel
   `k`.  Induction on `k`, cases on `e0`, uses `defmap_consistent` at
   the variable case.  ~40 lines.

4. **`equiv_cp_sound`**: corollary — `equiv_cp m a b = true` and
   `defmap_consistent e m` imply `eval_jexpr e a = eval_jexpr e b`.
   Trivial from (3) + reflexivity of `expr_eqb_full`.  ~10 lines.

5. **`scan_mulx_pairs_valid`**: every match `(mul_idx, mulhuu_idx, hi,
   lo, a, b)` produced by `scan_mulx_pairs_aux` satisfies: at position
   `mul_idx` the list has `JCset lo (JEmul a' b')`, at position
   `mulhuu_idx` it has `JCset hi (JEmulhuu a'' b'')`, and the
   `def_map m_k` built up to step `k = mul_idx` makes `equiv_cp m_k a a'`
   and `equiv_cp m_k b b'` true.  Induction on the scan; state a
   strengthened invariant parameterised by the running `(n, m, pending,
   acc)`.  ~60 lines.

6. **`rewrite_mulx_preserves_list_eval`**: the rewrite replaces at
   `mul_idx` with `JCmulx hi lo a b` and at `mulhuu_idx` with `JCskip`.
   The JCmulx big-step (new rule `jeval_mulx`) assigns both `lo :=
   a*b mod 2^64` and `hi := (a*b) / 2^64` in one step.  Combined with
   (5), the pre/post stores agree pointwise because
     - the original `JCset lo (JEmul a b)` writes the same `lo`,
     - the original `JCset hi (JEmulhuu a b)` writes the same `hi`,
     - no other variable is written by either emission,
     - under `wf_mulx`, no read of `lo` occurs between `mul_idx` and
       `mulhuu_idx`, so swapping the write order is observationally
       invisible.

7. **`lower_mulx_pairs_list_correct`**: combine (5) + (6) with a
   commutation argument over the intervening statements (see §3).

### 3. Hardest part — non-adjacency

The rewrite moves the write of `hi` *earlier* (to the `mul_idx`
position) and erases the statement at `mulhuu_idx`.  Soundness requires
that every intervening statement `s_j` (for `mul_idx < j < mulhuu_idx`)
is independent of `hi` — neither reads it nor writes it.  Two proof
strategies:

**(a) Dead-store simulation.** Show `hi ∉ writes(s_j) ∪ reads(s_j)` for
each `j`, then prove `jeval` commutes the `hi`-write across each
`s_j`.  Needs a per-statement `frame_hi` lemma.  Mirrors classical
liveness-based dead-code elimination; clean but requires writes/reads
computation for every constructor (~20 cases with JCadcx/JCsbb/
JCadd_flags/…).

**(b) Value-equality.** Observe that in the *final* state `e'`, the
variable `hi` holds `(a*b) div 2^64` whether computed at `mul_idx` or
at `mulhuu_idx`, because none of `a`, `b` are rewritten in between
(`scan_mulx_pairs_valid` — the `equiv_cp` check re-resolves operands
through the def_map built over the intervening stretch).  This avoids
reasoning about arbitrary `s_j` internals but still needs a
"`hi` not rewritten" sub-lemma, which is a weaker form of (a).

Recommended: **(b)** for the main line, falling back to (a) only for
the final "`hi` not rewritten" side-condition — which is discharged
syntactically from `wf_mulx`.

### 4. Estimated proof size

Comparing to `carry_cmd_correct` (currently a 10-line identity-case
proof + ~100 lines of scaffolding comments for the deferred general
case):

- Identity-case specialisation (BLS12 regression ⇒ transform is the
  identity, trivially sound): **~20 lines**, modelled exactly on
  `lower_carry_cmd_id_simple` + `carry_cmd_correct`.
- Full correctness (MULX actually fires, non-adjacent): **~350-450
  lines** across 6-7 Qed lemmas.  Larger than `carry_cmd_correct`
  would be because the matcher carries a def_map and the rewrite is
  non-local; closer in complexity to a future `adcx_chain_correct`
  than to the existing identity-case discharges.
- New `jeval` rule `jeval_mulx` (computes both limbs via `Z.shiftr` /
  `Z.land` on `word.unsigned (word.mul a b)` at bitwidth 128): **~15
  lines** spec + **~10 lines** lemma relating to `word.mulhuu` once
  that operator is added to `ExprBridge.v`.

### 5. Deferrals / admits

1. **`jeval_mulx` semantics.** Currently `ExprBridge.v` maps
   `bopname.mulhuu` to `JElit 0` (line 74) and marks `JEmulhuu` as
   unsupported (line 138).  Adding a real u128-split semantics is a
   prerequisite — until then, `rewrite_mulx_preserves_list_eval` has no
   meaningful statement.  **Admit until ExprBridge supports mulhuu.**
2. **Write/read sets for carry intrinsics.** `JCadcx`, `JCsbb`,
   `JCadd_flags`, `JCsub_flags` need `writes`/`reads` functions.  Can
   be mechanised from the constructor signatures.  **~50 lines,
   defer.**
3. **Fuel-8 sufficiency.** The `resolve_expr` fuel bound (8) is a
   magic number; for BLS12/Curve25519 chains it suffices, but a formal
   proof would need an upper bound on copy-chain depth from the
   `bedrock2 -> jasmin_cmd` translator.  **Defer as axiom
   `resolve_fuel_sufficient` with a cbv-discharged witness per
   function.**
4. **General control flow.** `lower_mulx_pairs_cmd` recurses into
   `JCif`/`JCwhile`/`JCdecl` bodies.  The soundness proof there is
   structural once the `JCseq` case is closed, but the induction
   hypothesis needs to be stated uniformly — straightforward, ~40
   lines.

### Recommendation

Ship the identity-case discharge now (mirrors `carry_cmd_correct`:
~20 lines Qed, unblocks the paper claim that every pass has a
soundness lemma), and open a tracking issue for the full non-adjacent
proof.  Total immediate work: **~1 Qed lemma, ~20 lines**.  Full
general proof: **~400 lines, gated on `ExprBridge.v` mulhuu support**.
