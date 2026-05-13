(** * Fe25519MulBody — rust_cmd_ed AST for [fe25519_mul].
 *
 *  Phase 0d of the unsafe-block reduction plan
 *  (see [docs/signal-stack-status-2026-05-13.md] §6.3): mirror the
 *  Phase 0c [fe25519_add] / [fe25519_sub] inlining for the larger
 *  field-multiplication leaf.  Eliminating the [extern "C"] boundary
 *  for [fe25519_mul] drops gcc/clang from the runtime trust set for
 *  every mul-shaped callsite in curve25519-jasmin-rs.
 *
 *  Status (Phase 0d scaffold, 2026-05-13)
 *  ======================================
 *  [fe25519_mul_body] is an INLINE 5-limb radix-2^51 schoolbook
 *  multiplication expressed entirely in [rust_cmd_ed] via five
 *  [REdLimbStore] writes (one per output limb), each carrying a
 *  sum-of-products [sexpr_ed] tree.  No [extern "C"] FFI boundary
 *  remains for this leaf in the surface AST.
 *
 *  Correctness lives in [Fe25519MulCorrect.v] (Phase 0d).  The single
 *  top-level theorem [fe25519_mul_body_correct] reduces to one Section
 *  hypothesis [mul_inline_correct] which captures the algebraic
 *  content of fiat-crypto's [Positional.mulmod] composed with the
 *  radix-2^51 carry chain (mirrored from fiat-crypto's
 *  [carry_mul_op]).  Discharging that hypothesis mechanically is the
 *  substantive Phase 0e / 0f task — it is the radix-2^51 schoolbook +
 *  reduce proof and intentionally factored out of the scaffold so
 *  this file remains a clean structural mirror of
 *  [Fe25519AddSubBody.v].
 *
 *  Counting note: the task spec mentions ~25 [REdLimbStore]s.  In the
 *  C output (curve25519_64.c §fiat_25519_carry_mul) the 25 figure
 *  counts u128 partial products (x1..x25) plus a 10-step reduce
 *  chain.  Our IR does not model u128 — [SMul] returns [mask64
 *  (va * vb)], i.e. truncated u64 — so the partial-product chain
 *  cannot be soundly expressed limb-by-limb at the IR level without
 *  introducing a 128-bit scratch type.  Two options were considered:
 *
 *    (A) emit 25 [REdLimbStore]s into u64 scratch slots, with the
 *        algebra discharged externally — this gives the literal store
 *        count but the u64 semantics is unsound for the partial
 *        products (each fits 2^108 not 2^64).
 *    (B) emit 5 [REdLimbStore]s — one per output limb — each carrying
 *        a single sum-of-products [sexpr_ed] tree (25 [SMul] +
 *        [SAdd] of the 5×5 schoolbook).  The tree IS unsound under
 *        u64 [mask64] (same reason), but the structural form is
 *        cleaner and the unsoundness is concentrated in a single
 *        Section hypothesis ([mul_inline_correct]) rather than smeared
 *        across 25 lemmas.
 *
 *  Option (B) is chosen here.  The 25 [SMul] operations are embedded
 *  in the 5 output-limb sexprs — count by traversing the tree.
 *  Phase 0e may revisit and emit a sequenced [REdLimbStore] chain if
 *  the IR is extended with a [TFp25519_lifted] / u128-scratch type.
 *
 *  IR DEPENDENCIES
 *  ===============
 *  Uses [REdLimbStore], [SLimb], [SAdd], [SMul], [SLit] from
 *  [SafeRustEd25519Sim.v] §1 (all introduced in Phase 0b, commit
 *  f9578ce).  No new IR constructors required.
 *
 *  FOLLOW-UP (Phase 0e / 0f, deferred)
 *  ===================================
 *  1. Discharge [mul_inline_correct] mechanically against fiat-crypto's
 *     [Positional.mulmod] / [eval_carry_mulmod] for radix-2^51.  This
 *     is the substantive arithmetic step and will require either:
 *       (a) extending [eval_sexpr_ed] semantics with a u128
 *           interpretation for [SMul] when both arguments are bounded
 *           by 2^54 (the [TFp25519] limb bound), or
 *       (b) introducing a [TFp25519_partial] tower type holding 5 u128
 *           accumulators, with a separate [SMul128] / [SAdd128]
 *           sexpr family.
 *     Option (b) mirrors the C output more directly and is the
 *     suggested path; estimated ~400 LoC.
 *  2. Apply the same recipe to [fe25519_square] (symmetric case,
 *     saves ~half the SMuls) and [fe25519_carry] (carry-only chain,
 *     no SMuls).
 *  3. Mirror [BridgeInstances] wiring: drop [fe25519_mul_prim] from
 *     the function-table, replace callsites in [CurveBodies] /
 *     [CombScalarmultBody] / [Fe25519InvertBody] with [fe25519_mul]
 *     using this inline body.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1.  Helpers                                                      *)
(* ================================================================ *)

(** Construct a [located_ed] for a [TFp25519] slot by name. *)
Definition LFpMul (v : String.string) : located_ed :=
  {| loc_var := v; loc_type := TFp25519 |}.

(** [smul a b] : [SMul (SLimb a i) (SLimb b j)] — partial product
    a[i] * b[j]. *)
Definition smul_limbs (av bv : String.string) (i j : nat) : sexpr_ed :=
  SMul (SLimb av i) (SLimb bv j).

(** [smul_scaled a b i j k] : [SMul (SLit k) (SMul (SLimb a i) (SLimb b j))]
    — for the 19× reduction on high-side products. *)
Definition smul_scaled (av bv : String.string) (i j : nat) (k : Z) :
    sexpr_ed :=
  SMul (SLit k) (SMul (SLimb av i) (SLimb bv j)).

(* ================================================================ *)
(* §2.  fe25519_mul body                                             *)
(* ================================================================ *)

(** [fe25519_mul_body] computes [dest := a * b] in [F p], [p = 2^255 -
    19], inlined as five [REdLimbStore] writes — one per output limb.
    Each store's RHS is the radix-2^51 schoolbook sum for that limb,
    with the 19-fold reduction folded into the high-side partial
    products:

      h0 = a0*b0 + 19*(a1*b4 + a2*b3 + a3*b2 + a4*b1)
      h1 = a0*b1 + a1*b0 + 19*(a2*b4 + a3*b3 + a4*b2)
      h2 = a0*b2 + a1*b1 + a2*b0 + 19*(a3*b4 + a4*b3)
      h3 = a0*b3 + a1*b2 + a2*b1 + a3*b0 + 19*(a4*b4)
      h4 = a0*b4 + a1*b3 + a2*b2 + a3*b1 + a4*b0

    Carry propagation (the x26..x52 chain in [fiat_25519_carry_mul])
    is folded into the algebraic [mul_inline_correct] hypothesis in
    [Fe25519MulCorrect.v]; see header for why a sequenced
    [REdLimbStore] chain is deferred. *)
Definition fe25519_mul_body : function_body_ed :=
  fun dest args =>
    match args with
    | [a_loc; b_loc] =>
        let av := a_loc.(loc_var) in
        let bv := b_loc.(loc_var) in
        (* h0 = a0*b0 + 19*(a1*b4 + a2*b3 + a3*b2 + a4*b1) *)
        let e0 :=
          SAdd (smul_limbs av bv 0 0)
            (SAdd (smul_scaled av bv 1 4 19)
              (SAdd (smul_scaled av bv 2 3 19)
                (SAdd (smul_scaled av bv 3 2 19)
                      (smul_scaled av bv 4 1 19)))) in
        (* h1 = a0*b1 + a1*b0 + 19*(a2*b4 + a3*b3 + a4*b2) *)
        let e1 :=
          SAdd (smul_limbs av bv 0 1)
            (SAdd (smul_limbs av bv 1 0)
              (SAdd (smul_scaled av bv 2 4 19)
                (SAdd (smul_scaled av bv 3 3 19)
                      (smul_scaled av bv 4 2 19)))) in
        (* h2 = a0*b2 + a1*b1 + a2*b0 + 19*(a3*b4 + a4*b3) *)
        let e2 :=
          SAdd (smul_limbs av bv 0 2)
            (SAdd (smul_limbs av bv 1 1)
              (SAdd (smul_limbs av bv 2 0)
                (SAdd (smul_scaled av bv 3 4 19)
                      (smul_scaled av bv 4 3 19)))) in
        (* h3 = a0*b3 + a1*b2 + a2*b1 + a3*b0 + 19*(a4*b4) *)
        let e3 :=
          SAdd (smul_limbs av bv 0 3)
            (SAdd (smul_limbs av bv 1 2)
              (SAdd (smul_limbs av bv 2 1)
                (SAdd (smul_limbs av bv 3 0)
                      (smul_scaled av bv 4 4 19)))) in
        (* h4 = a0*b4 + a1*b3 + a2*b2 + a3*b1 + a4*b0 *)
        let e4 :=
          SAdd (smul_limbs av bv 0 4)
            (SAdd (smul_limbs av bv 1 3)
              (SAdd (smul_limbs av bv 2 2)
                (SAdd (smul_limbs av bv 3 1)
                      (smul_limbs av bv 4 0)))) in
        REdSeq
          (REdLimbStore dest 0%nat e0)
          (REdSeq
            (REdLimbStore dest 1%nat e1)
            (REdSeq
              (REdLimbStore dest 2%nat e2)
              (REdSeq
                (REdLimbStore dest 3%nat e3)
                (REdLimbStore dest 4%nat e4))))
    | _ => REdSkip
    end.

(** Public function-table entry.  Downstream callers extend their
    [function_table_ed] with this to delegate mul through [REdCallFn]
    instead of the (Phase 0a) [REdCall "fe25519_mul_prim" ...]
    extern-FFI form. *)
Definition fe25519_mul_table : function_table_ed :=
  [ ("fe25519_mul", fe25519_mul_body) ].
