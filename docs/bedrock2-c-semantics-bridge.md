# Verifying bedrock2's C extraction against a formal C semantics — plan

**Status: deferred.** This file records the scoping done in 2026-05 so the
work can be picked up later without re-deriving it.

## Goal

`bedrock2`'s `ToCString : bedrock2.cmd -> string` is currently **trusted**:
no theorem connects the emitted C source to `bedrock2.exec`'s operational
semantics. Closing this gap turns "verified bedrock2 + trusted printer +
trusted C compiler" into "verified bedrock2 + verified printer + verified
C semantics + verified C compiler."

Concretely: for any `c : bedrock2.cmd` we want a theorem of shape

> if `bedrock2.exec functions c t m1 m2` holds, then under a formal C
> semantics the C source `ToCString c` (or its AST equivalent) steps from
> a refining initial state to a refining final state.

## Candidate semantics — comparison

| | **CompCert / VST** | **RefinedC** | **Cerberus / CN** |
|---|---|---|---|
| C model | CompCert C (UB-free subset, compiler-friendly) | CompCert C | Full ISO C with provenance / UB / pointer aliasing — the real standard |
| Logic | VST in Rocq | Iris, in Rocq | Custom ownership + refinement types, SMT-discharged |
| Style | Heavy interactive proofs | Iris-flavored interactive proofs | Annotation-driven, mostly automatic |
| Industrial use | NASA, automotive | research-only | pKVM (Android hypervisor) — Google/MSR-deployed |
| Maturity (2026) | most mature | growing but heavyweight | actively deployed in industry |
| Repos | `gitlab.mpi-sws.org/iris/vst` | `gitlab.mpi-sws.org/iris/refinedc` | `github.com/rems-project/cerberus` + `github.com/rems-project/cn` |

## Recommendation: Cerberus/CN

CN is the most pragmatic fit:

1. **bedrock2 specs are annotation-ready.** `fnspec!` already has the
   `requires`/`ensures` shape that CN's `/*@ ... @*/` annotations expect.
   The bridge becomes a `bedrock2.fnspec → CN.spec` printer alongside the
   existing `ToCString` printer.
2. **Decidable + SMT-discharged.** Most obligations close automatically.
   RefinedC requires manual Iris proofs.
3. **Provenance / UB-aware.** bedrock2's `(br_word_t)` casts and pointer
   arithmetic are exactly the kind of constructs CN models faithfully via
   PNVI provenance.
4. **Industrial precedent.** The pKVM verification (Android hypervisor,
   shipped to phones) was done with CN. Papers: *"CN: Verifying Systems C
   Code with Separation-Logic Refinement Types"* (Pulte et al., POPL 2023);
   follow-on at OOPSLA 2024.
5. **CHERI path.** `cerberus-cheri` extends CN to capability-typed C if
   that's ever desired.

Trade-offs:
- CN is newer than VST/RefinedC — expect API churn.
- Non-Iris, so does not compose mechanically with an Iris-based Rust track
  (e.g. RustBelt). Bridging is at the trust-base level, not proof-term.

## Two reformulations of the goal under CN

### B-CN.1 (lightweight)

Translate **the spec** to CN annotations, then let CN re-verify the body:

```
to_cn_annot : bedrock2.fnspec → CN.spec
```

Claim: if `bedrock2.exec` shows `cmd` satisfies `fnspec`, then the printed
C source + translated annotations are accepted by CN.

This avoids translating bedrock2's full operational semantics into
Cerberus's framework — only the contract crosses.

### B-CN.2 (full bridge)

Prove `CN-accepted C ⇒ sound w.r.t. bedrock2's intended semantics`. Closes
the loop end-to-end: `bedrock2.cmd → C → CN-checked-C ⇒ ASM via CompCert`.
Heavier; the more ambitious version.

## Phases

| Phase | Content | Estimate |
|---|---|---|
| B.0 Tooling | Build CN under our `rocq-9` switch; `cn-tutorial` examples green | 1 week |
| B.1 `to_cn_annot` | Translator `bedrock2.fnspec → CN.spec`; printer that interleaves with `ToCString` output | 3–4 weeks |
| B.2 Pretty-printer correctness | If we want B-CN.2: define `to_cerberus_ast : bedrock2.cmd → Cerberus AST` and prove AST-equivalence to ToCString modulo formatting | 6–10 weeks |
| B.3 Semantic correspondence | Prove `bedrock2.exec ↔ Cerberus operational step` for matching memory states. Bisimulation between bedrock2's flat byte-map and Cerberus's PNVI memory | 6–10 weeks |
| B.4 Sep-logic bridge | Translate bedrock2's `Map.Separation` predicates to CN ownership annotations | 4–6 weeks |
| B.5 Hoare-spec preservation | `bedrock2 WP.call ⇒ CN-verified` for translated post-conditions | 4–6 weeks |
| B.6 End-to-end Ed25519 | Apply to `ed25519_sign`. Claim: "the C string ToCString emits satisfies the Hoare spec under CN." | 1–2 weeks |

Total: 8–12 months for B-CN.2 end-to-end. B-CN.1 alone is ~3 months.

## Output artifacts

- `Bedrock2CNBridge.v` — Rocq module with `to_cn_annot` + correspondence proofs.
- CN annotation files generated alongside the existing `ToCString` output.
- A short paper section: "Verified C extraction: from bedrock2 to CN."
- Updated trust-audit doc: ToCString moves from "trusted printer" to "verified printer."

## Risks

- **Memory-model mismatch.** bedrock2's `map word byte` flat memory vs
  Cerberus's PNVI block-with-provenance model. Bisimulation may be more
  involved than expected.
- **bedrock2 emits constructs CN may not handle gracefully.** `(br_word_t)`
  casts everywhere, no struct types. May need a wrapper layer in the
  emitted C.
- **CN stability.** Pre-1.0 tooling; expect tactic / API churn.
- **Pretty-printer fidelity.** `ToCString → text → CN parser` round-trip
  has formatting + macro pitfalls. The B.2 AST shortcut sidesteps this.

## Cross-references

- `docs/rust_cmd_ed-emit-evaluation.md` — gap #1 in the C path
  (`sha512_64` length arg) is the kind of bug a CN bridge would catch
  immediately.
- `docs/rustcmd-paper-section.md` — paper-section material that would
  cite the CN bridge as the "verified C extraction" companion to the
  "verified Rust extraction" claim.
- Track A (Rust side): paired with a verified Rust extraction track (see
  `docs/rust-extraction-verification-options.md` once written).
  Iris-uniform with RustBelt; CN sits in a different logical world but
  composes at the trust-base level.

## Concrete next steps when picking this up

1. `opam install coq-cn coq-cerberus` under `rocq-9` (or a sibling switch).
2. Build the `cn-tutorial` examples to confirm tooling works.
3. Write a 50-LoC CN-style spec for `clamp_64` (smallest bedrock2 body
   shipped) — hand-translated; this is the validation that CN can express
   bedrock2's spec shape at all.
4. If that succeeds, mechanize the `bedrock2.fnspec → CN.spec` translator.
5. Stage at `$WORKSPACE/../aucurves-cn-bridge/` (new sibling repo) per the
   repo-separation policy.

## Decision deferred

This plan is recorded for future execution. The Commitments and Signal
papers do not require this bridge in their current scope; the bedrock2
emit chain stays as currently shipped (`ToCString` trusted, post-hoc
spot-checks via dalek / RFC vectors).
