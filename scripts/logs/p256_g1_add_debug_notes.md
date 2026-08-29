# P256_G1_Add_Spec.v — first-execution debug record (2026-08-26/27)

Per-sentence `-time` streams for every run are in `p256_run_*.log` /
`build_real_c*.log` in this directory (the dune Bedrock stanza carries
`(flags -time)`; the launcher archives each run's stream on exit).

## Status of the historical timing entries

`build_timings.txt` lists `~5min P256_G1_Add_Spec.v — ecancel match
error` and `~9min Secp256k1_G1_Add_Spec.v`.  Both are time-to-FAILURE
records: the Secp proof is `Admitted` from the word-stores onward, and
the P-256 main proof had never executed past the prologue before
2026-08-27.  Neither number is a baseline for a successful compile.

## Defect classes found while executing the script for the first time

1. `repeat straightline.` over the 8-stackalloc prologue diverges
   (>90 min, non-interruptible) through in-sentence backtracking and a
   per-step cost that grows with accumulated context; committed single
   sentences are unaffected.  Fix: explicit singles.
2. This bedrock2 release's `straightline` consumes the stackalloc
   intros itself, so the file's `straightline'` destruct branch never
   fires; raw `anybytes`/`msplit` pairs must be converted by an
   explicit post-pass (`anybytes_to_array_1` + `alloc_seps_alt`),
   producing the byte-array route the downstream script expects.
3. `straightline'` calls `anybytes_Bignum` with the memory and size
   arguments swapped — it could never have executed.
4. `Local Open Scope Z_scope` makes bare `4` in `Bignum 4 …` Ltac
   patterns parse as `4%Z` against `4%nat` terms — every such pattern
   silently never matches.  Fix: `4%nat`.
5. The store loop packs `ecancel_assumption` (26-atom chain) and an
   inner `repeat straightline` into one `repeat (...)` sentence — the
   same divergence shape as (1).  Fix: decomposed single store steps
   with `Timeout`-bounded ecancels (first store's ecancel completed
   within its 600 s bound via the `ecancel_assumption_fast` override).

Escalation if a bounded ecancel trips: the reflective
`flatten_seps` + `cancel_seps_at_indices` recipe
(`reference_slow_proofs_fiat`, H3 worked example, ~3000× speedup).

The same five classes apply verbatim to the ported
`P384_G1_Add_Spec.v` / `P224_G1_Add_Spec.v` scripts.

## Classes 6–15 (2026-08-27/28, through the closure)

6. `eassert (H : (... * _)%sep _). { ... }` — the evar-laden goal is
   shelved, so the brace proof runs against the *wrong* goal (600 s
   timeouts measured against the `cmd` goal).  Use the `by` form or a
   `seprewrite_in` with a closed iff1 lemma.
7. Address normal forms: the store phase leaves `word.add a (of_Z 8k)`
   (flat, descending nesting); lemmas stated in `N`-successor form never
   match and `seprewrite_in` may no-op silently.  State fold lemmas in
   the observed flat/descending form (`fold4_scalars_Bignum_flat_desc`).
8. Ecancel searching for an atom that does not exist (an un-folded
   constant buffer) diverges — always confirm the atom is present
   (flatten + `Show`) before blaming ecancel speed.
9. Byte vs character offsets: Rocq's `-time` `Chars` are BYTES; python
   `str.index` counts characters — non-ASCII comment glyphs skew them by
   ~900 bytes at 47 KB.  Patch in binary mode.
10. `repeat (do_binop_call; repeat straightline)` masks the first
    failure; forty explicit `do_binop_call.` sentences with per-call
    `clear_old_seps` are required (sep-hyp accumulation crawls by call
    ~27 otherwise).
11. `cmd.call` unfolds to an args-`dexprs` exists — `unfold1_cmd_goal`
    then a bounded `straightline` pass, then `straightline_call`.
12. Closure: `unfold BLS12_add_mont_spec` before the constant rewrites;
    the rewrite lemmas must target `MontgomeryCurveG1Equiv.three_b_mont`
    / `.a_mont` (not the a=0 `MontgomeryCurveSpecs` homonyms).
13. Wired-spec `m'` is the projection `Field.m' bw <instance>`, not the
    literal 1: `replace ... with 1%Z in *` before any `montsub`-notation
    pattern can match a hypothesis.
14. Call equations carry `((A mod m * B) mod m) mod m`; normalize with
    `Zmod_mod` + `Z{mult,plus,minus}_mod_idemp_{l,r}` (removing
    direction, terminating), NOT `<- Zmult_mod` patterns.
15. `this_mod'` substitution works when invoked as its own SENTENCE and
    stalls inside `repeat`/`do (try ...)`/`first [...]` wrappers —
    same lesson as class 1.  A bare `do 45 (try match ...)` also grew the
    goal tree until OOM; per-sentence commits or the BLS12 direct calls.

Functor-instance frontier (2026-08-29, r7): P-256/P-384/P-224 instances
execute cleanly through the entire closure preamble — landing, defrag,
`assert_valid'`, `BLS12_add_specs_equiv'`, `unfold BLS12_add_mont_spec`,
m'-alignment, idemp normalization, both constant rewrites (0.26 s) — and
stop at the first `this_mod'` substitution sentence (Timeout 300 s; the
pathfinder measured ~15 min/sentence with unbounded tree growth).  The
substitution+ring tail is Admitted with `TODO(ring-final)` in the three
instance files; the Rupicola bridge route is the intended closure.

Trust-story findings (2026-08-29): `BLS12_add_specs_equiv` in
`Theory/WordByWordMontgomery/MontgomeryCurveG1Equiv.v` (line 258) is
`Admitted`; every WP closure that goes through `BLS12_add_specs_equiv'`
(BLS12Curve_G1.v's G1 add and the general-a functor instances) inherits
it.  The Rupicola bridge proof avoids it by direct F.to_Z algebra.  Also:
the unconditional Bignum bridge for the Rupicola add is not derivable —
`spec_of_rcb_add_general` requires valid old OUTPUT buffers (FElem tight
bounds) while the Bignum-level spec assumes nothing; the `_valid_out`
variant is the provable statement.

Closure via the standalone chain lemma (2026-08-29): `eapply
rcb_general_a_chain_Z` unifies with the instance goal in 0.2 s.  Discharging
its forty call-equation premises with `all: try eassumption` took 36 min and
mis-instantiated output evars (a later premise with all-evar arguments was
tried before the premise that fixes its inputs; `eassumption` then matched
an arbitrary hypothesis).  Discharge only premises whose input arguments
are not evars, iterated to a fixpoint (`do 45 (all: try (match goal with
|- montmul _ (toZ ?a) (toZ ?b) => not_evar a; not_evar b; eassumption
| ... end)))`).

Route status (2026-08-29 09:30): the Rupicola route is COMPLETE for the
general-a ADDITION on P-256/P-384/P-224 — `CurveAddGeneralA.v` (derivation,
~3 min), `CurveAddGeneralA_GallinaToZ.v` (F-chain → Gallina spec, Qed),
`CurveAddGeneralA_P{256,384,224}.v` (loaders Qed, wrapper Qed, Bignum bridge
`_valid_out` Qed; each compiles in minutes under dune native).  The
hand-written WP route (`P256_G1_Add_Spec.v` and the functor instances) is
paused; its closure lemma `RcbGeneralAChain.v` is Qed and reusable.

Wrapper-body WP proofs — RESOLVED 2026-08-29 (all four Qed, commit
be20f7b).  Four findings beyond the six listed below:

- `sep` is not definitionally associative: `eapply` cannot bridge a
  left-associated lemma conclusion to a right-associated goal, and
  `straightline` right-associates goals (`flatten_seps_in_goal`,
  ProgramLogic.v:358).  State the rebuild lemma in both associations.
- Neither stackalloc conversion path works for a SYMBOLIC size:
  `BignumStoreFold.stackalloc_anybytes_to_arrays` is hard-wired to
  BasicC64Semantics, and bedrock2's `straightline` branch needs
  `isZcst n` while `straightline_stackalloc` closes its size obligation
  with `Z.max 0 n = n`, true only for a literal.  Width-generic
  `stackalloc_FElem` / `FElem_dealloc` now live in NistWnafWrappers.v.
- `CompilationAbstract.FElem` is a delta-alias of `Compilation2.FElem`
  (CompilationAbstract.v:24) and `ecancel` compares reified atoms
  SYNTACTICALLY, so nothing cancels and `ecancel_assumption`'s
  multimatch exhausts with "No matching clauses for match" — which reads
  like a shape error but is an ordinary cancellation failure.  Precede
  any cancellation against a spec from a CompilationAbstract importer
  with `change CompilationAbstract.FElem with Compilation2.FElem in H`,
  on the whole hypothesis so its postcondition leaves are fixed too.
- Order the single pre-deallocation `assert` in deallocation order
  (innermost-first): each dealloc then hands back a remainder headed by
  the next buffer, so N temporaries cost one cancellation, not N.

Also (WnafTableBuild.v and other RcbProjectiveLaws consumers):
`ring`/`fsatz` emit `abstract`ed subproofs that generalise over the
WHOLE section context, so imported lemmas carry constants their
statements never mention (`b`, `three_b`) and `apply` cannot invent
them — pin with `eapply L with (b := ...) (three_b := ...)`.  And do NOT
add a local `prime` instance: a second opaque proof breaks
convertibility with the field instance baked into the imported theorems.

Original notes from the attempt:

Wrapper-body WP proofs (2026-08-29, from the `store_zero_from_word_ok`
attempt in ScalarMult/NistWnafWrappers.v; the attempt is stashed, the
file's committed state keeps it Admitted):

- `cmd.call` unfolds to `exists args, dexprs m l args /\ Semantics.call …`
  — neither `WeakestPrecondition.call` nor a bare `Semantics.call`, so
  `straightline_call`'s lazymatch does not fire.  Discharge the args
  existential first (cbv of dexprs/expr/expr_body/get/literal, then
  `eexists; split; [map-get lookup|]` per argument).
- The locals map produced by a call's postcondition is LET-BOUND
  (`l' := #{ "x" => p; … }#`).  `map.get` cannot see the put-chain through
  the binder: substitute every `x := _ : map.rep` before evaluating
  arguments.  This one is invisible without printing the context.
- `seprewrite_in <- H` is not accepted here; pass an explicit symmetry
  argument.  This bedrock2 exports no `iff1` symmetry lemma (coqutil
  defines `Lift1Prop.iff1` only) — state a local three-line one.
- Stale pre-call sep hypotheses are matched first by both
  `ecancel_assumption` and any `sep _ _ _`-patterned rewrite; clear them
  before the postcondition rebuild.
- A `try`-wrapped tactic that silently skips a call looks like a
  successful body and only surfaces much later as untouched buffers;
  make such fallbacks fail loudly with the goal printed.

Scalar multiplication (2026-08-29, plan in docs/nist_scalar_mult_plan.md):
the repo's verified wNAF chain leaves the group laws as Section
hypotheses stated with Leibniz equality on raw projective triples —
unsatisfiable for RCB coordinates and never discharged for BLS12/BN254
(see BLS12_wNAF_PointOppInverse.v).  The NIST instantiation therefore
inherits an undischargeable hypothesis until the chain's invariant is
restated up to projective equivalence.

Regressions measured on the functor instances (2026-08-29): the
flatten-based `do_binop_call_flat` at S20 hangs (>50 min) where plain
`do_binop_call` took 84 s — flattening is not a speedup for evar-frame
cancellation; an explicit indexed witness is.  `eapply ...; eauto` on the
Rupicola wrapper's residual goals diverges — discharge them per-goal
under `Timeout`.
