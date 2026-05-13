(** * Fe25519Mul128Helpers — u128 parallels of the [smul_limbs] /
 *      [smul_scaled] sexpr builders used by [Fe25519MulBody.v].
 *
 *  Phase 0e (2026-05-13).
 *
 *  CONTEXT
 *  =======
 *  [Fe25519MulBody.v] §1 defines two helpers that build sum-of-products
 *  trees for the 5-limb radix-2^51 schoolbook multiplication:
 *
 *      Definition smul_limbs  (av bv : string) (i j : nat) : sexpr_ed :=
 *        SMul (SLimb av i) (SLimb bv j).
 *
 *      Definition smul_scaled (av bv : string) (i j : nat) (k : Z) :
 *          sexpr_ed :=
 *        SMul (SLit k) (SMul (SLimb av i) (SLimb bv j)).
 *
 *  Under the u64-truncating [SMul] semantics ([mask64 (va * vb)]) those
 *  partial products are unsound for radix-2^51 limbs whose products
 *  reach 2^108 — the algebraic content was therefore concentrated in a
 *  single Section hypothesis ([mul_inline_correct]) in
 *  [Fe25519MulCorrect.v] rather than discharged limb-by-limb.
 *
 *  Phase 0e of the unsafe-block reduction plan introduced new IR
 *  constructors [SMul128] / [SAdd128] in
 *  [src/Bedrock/SafeRustEd25519Sim.v §1] (Phase 0e block, commit
 *  a654246) whose semantics is [mask128 (va * vb)] / [mask128 (va + vb)]
 *  — wide enough to hold all five 19-scaled sums of radix-2^51 partial
 *  products without truncation.  See the Phase 0e header in
 *  [SafeRustEd25519Sim.v] for the design rationale.
 *
 *  WHAT THIS FILE PROVIDES
 *  =======================
 *  This file is the Phase-0e E3 deliverable: parallel helpers
 *  [smul128_limbs] / [smul128_scaled] with the SAME signature as the
 *  legacy [smul_limbs] / [smul_scaled] but emitting [SMul128] in place
 *  of [SMul].  Body files written against the u128 fragment can swap
 *  the import and use the new helpers as drop-in replacements:
 *
 *      Require Import Bedrock.End2End.Ed25519.Fe25519Mul128Helpers.
 *      ... smul128_limbs av bv 0 0 ...
 *      ... smul128_scaled av bv 1 4 19 ...
 *
 *  Note: the outer [SAdd] chains in [Fe25519MulBody.v] that combine
 *  these partial products into per-limb sums also need to become
 *  [SAdd128] in the u128 retargeting; this file does NOT introduce a
 *  combinator for that (the combinator IS [SAdd128] itself — there is
 *  no helper to mirror — chains are written directly in the body
 *  file).  Callers should write `SAdd128 (smul128_limbs ...) (...)`.
 *
 *  WHY A NEW FILE RATHER THAN EDITING Fe25519MulBody.v
 *  ===================================================
 *  [Fe25519MulBody.v] / [Fe25519SquareBody.v] are read-only in the
 *  Phase 0e split — the legacy [SMul]/[SAdd] body remains the source
 *  of truth for the already-mechanized [Fe25519MulCorrect.v].  Phase
 *  0e introduces a parallel u128 body in a successor file (Phase 0f
 *  scope), and these helpers live alongside that successor.
 *
 *  IR DEPENDENCIES
 *  ===============
 *  Uses [SMul128], [SLimb], [SLit] from [SafeRustEd25519Sim.v] §1
 *  (Phase 0e block, 2026-05-13).  No new constructors required.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1.  Phase-0e u128 helpers                                        *)
(* ================================================================ *)

(** [smul128_limbs a b i j] : [SMul128 (SLimb a i) (SLimb b j)] —
    partial product [a[i] * b[j]] in the u128 fragment.  Mirrors
    [Fe25519MulBody.smul_limbs] with [SMul] → [SMul128]. *)
Definition smul128_limbs (av bv : String.string) (i j : nat) : sexpr_ed :=
  SMul128 (SLimb av i) (SLimb bv j).

(** [smul128_scaled a b i j k] :
    [SMul128 (SLit k) (SMul128 (SLimb a i) (SLimb b j))] — for the 19×
    reduction on high-side products.  Mirrors
    [Fe25519MulBody.smul_scaled] with [SMul] → [SMul128].  The outer
    multiply must also be [SMul128] because [k * (a[i] * b[j])] for
    radix-2^51 limbs reaches 19 · 2^108 ≈ 2^112 and would be truncated
    to 64 bits by [SMul]. *)
Definition smul128_scaled (av bv : String.string) (i j : nat) (k : Z) :
    sexpr_ed :=
  SMul128 (SLit k) (SMul128 (SLimb av i) (SLimb bv j)).
