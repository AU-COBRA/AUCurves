# Plan: rust_cmd + Borrow Checker as Replacement for Bedrock2 WP Proofs

The goal is to prove curve implementations correct without separation logic, by:
1. Writing field and curve operations directly in `rust_cmd`
2. Discharging memory safety with a borrow checker proved sound once
3. Translating to `jasmin_cmd` for the assembly path

All new files live alongside existing proofs. Nothing is deleted or modified
until the new approach is validated end-to-end.

---

## Milestone 1 — Borrow checking infrastructure

**New file**: `src/Bedrock/SafeRustBorrowCheck.v`

### 1a. Borrow signatures

Annotate functions with which arguments are `&mut` vs `&`:

```coq
(* true = mutable borrow (&mut), false = shared borrow (&) *)
Definition borrow_sig := string → list bool.
```

For each `RCall dst f args`, the sig says which positions are mutated.
The destination is always `&mut`. `RCloneCall` is handled specially
(the clone breaks aliasing explicitly).

### 1b. Borrow checker

```coq
(* Set of variables currently mutably borrowed *)
Definition borrow_env := list string.

Fixpoint borrow_check (sig : borrow_sig) (env : borrow_env)
    (c : rust_cmd) : bool.
```

Rules:
- `RCall dst f args`: reject if `dst ∈ args`, or if any `&mut` arg appears
  in `env`, or if `dst ∈ env`
- `RCloneCall dst alias f args`: check `dst ∉ args[1..]` after cloning `args[0]`
- `RLimbStore arr _ val`: reject if `arr ∈ env`
- `RLetZero/RLetU64Zero`: extend `env` with new variable as unborrrowed
- `RSeq`, `RIfNz`, `RWhileNz`: recurse; loops require `env` unchanged across body

### 1c. Soundness theorem

```coq
Theorem borrow_check_sound :
  ∀ (sig : borrow_sig) (c : rust_cmd),
    borrow_check sig [] c = true →
    ∀ N u64max lspec s1 s2 s2',
      rust_exec N u64max lspec c s1 s2 →
      rust_exec N u64max lspec c s1 s2' →
      s2 = s2'.
```

Determinism + frame property: borrow-checked programs have no aliasing, so
any two executions from the same state agree. This is the analogue of what
separation logic postconditions establish per-function.

Stronger form (for use in functional correctness):

```coq
(* If borrow_check accepts, each named variable in the output state
   is determined solely by the input values of variables that were
   passed as arguments to calls writing to that variable. *)
```

This is the "no hidden aliasing" property that replaces explicit `sep P Q`
in fnspec postconditions.

**Effort estimate**: ~300 lines, no dependencies on any other new file.

---

## Milestone 2 — rust_cmd → jasmin_cmd translation

**New file**: `src/Bedrock/Jasmin/RustCmdToJasmin.v`

Now that `rust_cmd` is the *source language* (not an intermediate from bedrock2),
the translation to `jasmin_cmd` is the compilation path — not redundant with
the direct `bedrock2 → tr_cmd → jasmin_cmd` route.

### 2a. Translation function

```coq
Fixpoint rj_translate (c : rust_cmd) : jasmin_cmd :=
  match c with
  | RSkip              => JSkip
  | RSeq c1 c2         => JSeq (rj_translate c1) (rj_translate c2)
  | RLetZero x t body  => JDecl x (tt_to_jasmin_ty t) (rj_translate body)
  | RLetU64Zero x body => JDecl x JTu64 (rj_translate body)
  | RScalarSet x e     => JAssign x (rj_expr e)
  | RCall dst f args   => JCall [dst] f args
  | RCloneCall d al f args =>
      JSeq (JAssign al (JVar (hd "" args)))
           (JCall [d] f (al :: tl args))
  | RIfNz e body       => JIf (rj_expr e) (rj_translate body) JSkip
  | RWhileNz e body    => JWhile (rj_expr e) (rj_translate body)
  | RLimbStore a i v   => JStore a (JConst i) v
  end.
```

### 2b. Simulation theorem

```coq
Theorem rj_translate_correct :
  ∀ c s1 s2,
    rust_exec c s1 s2 →
    jasmin_exec (rj_translate c) (rs_to_js s1) (rs_to_js s2)
```

where `rs_to_js : rust_state → jasmin_state` is the state correspondence.

The proof is by structural induction on the `rust_exec` derivation,
one case per constructor.

**Effort estimate**: ~250 lines. Key dependency: jasmin_cmd constructors
from `Jasmin/Core.v` (`JDecl`, `JCall`, `JStore`, etc.).

---

## Milestone 3 — First example: Fp multiplication

**New file**: `src/Bedrock/Field/RustCmdFpMul.v`

Implement Montgomery multiplication for a generic Fp in `rust_cmd`:

```coq
(* Handwritten rust_cmd for fp_mul: takes src1, src2, writes dst *)
Definition fp_mul_cmd : rust_cmd := ...

(* Borrow check certifies memory safety *)
Lemma fp_mul_borrow_ok : borrow_check fp_borrow_sig [] fp_mul_cmd = true.
Proof. reflexivity. Qed.

(* Functional correctness: output is the field product *)
Theorem fp_mul_correct :
  ∀ s a b,
    rs_get_fp s "src1" = a → rs_get_fp s "src2" = b →
    ∃ s', rust_exec fp_mul_cmd s s' ∧
          rs_get_fp s' "dst" = fp_mul a b.
```

The borrow check replaces the entire separation logic precondition
(no `sep (FElem src1_ptr a) (FElem src2_ptr b)` needed).

Composing M1 + M3: the correctness statement is purely mathematical.
No limb-array separation predicates, no `ecancel_assumption`.

**Effort estimate**: ~200 lines.
Key dependency: a concrete `fp_mul` spec (reuse existing fiat-crypto spec).

---

## Milestone 4 — Tower fields

**New file**: `src/Bedrock/Field/FieldExtensions/RustCmdTower.v`

Extend to Fp2, Fp6, Fp12 using the same pattern as M3.
`tower_type` is already in `rust_cmd`; this milestone uses it.

Each tower operation follows the same structure:
1. Write operation in `rust_cmd`
2. `borrow_check` certifies memory safety
3. Prove functional spec (Karatsuba, quadratic extension algebra)

For BLS12, parameterize `tower_type` beyond the current BN254 hardcoding:

```coq
(* New: parameterized tower type *)
Inductive tower_type (p : CurveParams) := TFp | TFp2 | TFp6 | TFp12.
```

This is backward-compatible: `CurveParams := BN254Params` recovers the
existing behavior.

**Effort estimate**: ~400 lines across Fp2/Fp6/Fp12 operations.
Unblocks BLS12, BLS24, Pallas/Vesta (which use non-BN254 towers).

---

## Milestone 5 — Curve point operations

**New file**: `src/Bedrock/Curve/RustCmdCurve.v`

G1 and G2 point addition in `rust_cmd`.

A projective point `(X, Y, Z)` in `rust_cmd` is three named tower variables.
Point addition calls tower ops (from M4) as sub-calls.

```coq
Definition g1_add_cmd : rust_cmd :=
  RSeq (RCall "t0" "fp_mul" ["p1_X"; "p2_X"])  (* t0 = X1 * X2 *)
  (RSeq ...
```

Borrow check verifies: output point variables don't alias input point variables.
This replaces the `sep (Point p1_ptr P1) (Point p2_ptr P2) (Point out_ptr _)`
preconditions in the current G1 add WP proofs.

Functional correctness: prove the output is the sum on the curve.
The algebraic part (curve law) is unchanged from the current approach;
the separation part is gone.

**Effort estimate**: ~300 lines per curve (G1 + G2).

---

## Non-goals / Later milestones

**Miller loop / final exponentiation**: The borrow checker removes the
spatial part, but **loop invariants remain**. These will use a lightweight
relational framework (not full WP), deferred to a later milestone.

**MSM**: Requires `RLimbStoreVar` (variable-index stores) and a borrow
checker that reasons about array slices. Deferred — the `IteratedSepPoints`
approach remains for now.

**Replacing existing proofs**: The existing `Bedrock/Field/` and
`Bedrock/Curve/` WP proofs are untouched throughout all milestones.
Replacement only happens once an end-to-end example (M5) is validated.

---

## Dependency graph

```
M1 (BorrowCheck)
    ├─▶ M2 (rj_translate)   independent of M3-M5
    ├─▶ M3 (Fp mul)
    │       └─▶ M4 (Tower)
    │               └─▶ M5 (Curves)
    └─▶ (later) Miller loop / MSM
```

M1 and M2 are independent and can be developed in parallel.
M3 requires M1 but not M2.
M2 is needed for the jasmin_cmd output path, but M3–M5 correctness
proofs don't depend on it (they target `rust_exec` semantics).

---

## File summary

| File | Milestone | Lines (est.) | Depends on |
|---|---|---|---|
| `SafeRustBorrowCheck.v` | M1 | ~300 | `SafeRustSimulation.v` |
| `Jasmin/RustCmdToJasmin.v` | M2 | ~250 | M1, `Jasmin/Core.v` |
| `Field/RustCmdFpMul.v` | M3 | ~200 | M1 |
| `Field/FieldExtensions/RustCmdTower.v` | M4 | ~400 | M3 |
| `Curve/RustCmdCurve.v` | M5 | ~300 | M4 |
