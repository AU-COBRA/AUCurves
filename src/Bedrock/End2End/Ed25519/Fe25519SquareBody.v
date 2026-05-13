(** * Fe25519SquareBody — rust_cmd_ed AST for [fe25519_square].
 *
 *  Phase 0c-square sibling of [Fe25519MulBody.v]: mirror the inline
 *  schoolbook used there for the symmetric squaring case
 *  [dest := a * a].  Squaring is the smaller of the two large fe25519
 *  leaves: schoolbook squaring touches the 5×5 product grid only on or
 *  above the diagonal — 5 diagonal products + 10 cross-products = 15
 *  unique partial products (vs 25 for mul).  Eliminating the
 *  [extern "C"] boundary for [fe25519_square] drops gcc/clang from the
 *  runtime trust set for every square-shaped callsite in
 *  curve25519-jasmin-rs (notably [fe25519_invert] and the
 *  Montgomery-ladder doubling step).
 *
 *  Status (Phase 0c, 2026-05-13)
 *  =============================
 *  [fe25519_square_body] is an INLINE 5-limb radix-2^51 schoolbook
 *  squaring expressed entirely in [rust_cmd_ed] via five
 *  [REdLimbStore] writes (one per output limb), each carrying a
 *  sum-of-products [sexpr_ed] tree.  No [extern "C"] FFI boundary
 *  remains for this leaf in the surface AST.
 *
 *  Correctness lives in [Fe25519SquareCorrect.v] (Phase 0c).  The single
 *  top-level theorem [fe25519_square_body_correct] reduces to one
 *  Section hypothesis [square_inline_correct] which captures the
 *  algebraic content of fiat-crypto's [Positional.squaremod] composed
 *  with the radix-2^51 carry chain (mirrored from fiat-crypto's
 *  [carry_square_op] /  [fiat_25519_carry_square]).
 *
 *  Algorithm (from fiat-crypto's [carry_square_op] / the C extraction
 *  [fiat_25519_carry_square] in [fiat-c/src/curve25519_64.c], with the
 *  19-fold reduction and the 2× doublings folded into the per-output
 *  limb sums):
 *
 *      h0 = a0*a0 + 38*a1*a4 + 38*a2*a3
 *      h1 = 2*a0*a1 + 38*a2*a4 + 19*a3*a3
 *      h2 = 2*a0*a2 + a1*a1 + 38*a3*a4
 *      h3 = 2*a0*a3 + 2*a1*a2 + 19*a4*a4
 *      h4 = 2*a0*a4 + 2*a1*a3 + a2*a2
 *
 *  Each [a_i*a_j] (i < j) cross-product carries either a 2× factor
 *  (when both indices are < the "wrap boundary" at limb 5) or a 38×
 *  factor (= 2 × 19, when one of i,j gets the 19-fold reduction).
 *  Diagonals [a_i*a_i] carry either ×1 (low limbs) or ×19 (when i is on
 *  the reduced side, here only [a3*a3] in [h1] and [a4*a4] in [h3]).
 *
 *  Counting note: the C output [fiat_25519_carry_square] uses 15 u128
 *  partial-product variables (x9..x23) plus an 8-step reduce chain.
 *  As with [Fe25519MulBody.v], our IR does not model u128, so option
 *  (B) — 5 [REdLimbStore]s carrying sum-of-products [sexpr_ed] trees,
 *  with the algebraic content discharged as a single Section
 *  hypothesis — is chosen.  Phase 0e may revisit and emit a sequenced
 *  [REdLimbStore] chain over a [TFp25519_lifted] / u128-scratch type.
 *
 *  IR DEPENDENCIES
 *  ===============
 *  Uses [REdLimbStore], [SLimb], [SAdd], [SMul], [SLit] from
 *  [SafeRustEd25519Sim.v] §1 (all introduced in Phase 0b, commit
 *  f9578ce).  No new IR constructors required.
 *
 *  FOLLOW-UP (Phase 0d / 0e, deferred)
 *  ===================================
 *  1. Discharge [square_inline_correct] mechanically against
 *     fiat-crypto's [Positional.squaremod] / [eval_carry_squaremod]
 *     for radix-2^51.  Estimated ~300 LoC (about ¾ of the [mul] effort
 *     since squaring uses 15 partial products instead of 25 and the
 *     reduce chain is the same shape).
 *  2. Mirror [BridgeInstances] wiring: drop [fe25519_square_prim] from
 *     the function-table, replace callsites in [Fe25519InvertBody]
 *     ([fe25519_invert] is ~250 squarings) and the doubling step of
 *     [ScalarmultBody] with [fe25519_square] using this inline body.
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
Definition LFpSquare (v : String.string) : located_ed :=
  {| loc_var := v; loc_type := TFp25519 |}.

(** [ssq_diag a i] : [SMul (SLimb a i) (SLimb a i)] — the diagonal
    partial product a[i] * a[i]. *)
Definition ssq_diag (av : String.string) (i : nat) : sexpr_ed :=
  SMul (SLimb av i) (SLimb av i).

(** [ssq_cross a i j] : [SMul (SLimb a i) (SLimb a j)] — the
    (i, j) cross-product a[i] * a[j], unscaled.  Callers wrap with
    [SMul (SLit k) _] to apply the 2×, 19×, or 38× scaling factor
    appropriate to that grid position. *)
Definition ssq_cross (av : String.string) (i j : nat) : sexpr_ed :=
  SMul (SLimb av i) (SLimb av j).

(** [ssq_cross_scaled a i j k] : [SMul (SLit k) (SMul (SLimb a i)
    (SLimb a j))] — the cross-product with a leading scalar factor
    [k].  Used for 2×, 19×, and 38× scalings in the schoolbook. *)
Definition ssq_cross_scaled (av : String.string) (i j : nat) (k : Z) :
    sexpr_ed :=
  SMul (SLit k) (SMul (SLimb av i) (SLimb av j)).

(** [ssq_diag_scaled a i k] : [SMul (SLit k) (SMul (SLimb a i)
    (SLimb a i))] — the diagonal product with a leading scalar factor.
    Used for the ×19 diagonals at the high-limb wrap (a3*a3, a4*a4). *)
Definition ssq_diag_scaled (av : String.string) (i : nat) (k : Z) :
    sexpr_ed :=
  SMul (SLit k) (SMul (SLimb av i) (SLimb av i)).

(* ================================================================ *)
(* §2.  fe25519_square body                                          *)
(* ================================================================ *)

(** [fe25519_square_body] computes [dest := a * a] in [F p],
    [p = 2^255 - 19], inlined as five [REdLimbStore] writes — one per
    output limb.  Each store's RHS is the radix-2^51 schoolbook sum for
    that limb specialised to the symmetric a=b case, with the 19-fold
    reduction and the 2× doubling factors folded into the partial
    products (see header §Algorithm for the closed-form sums).

    The five sum-of-products trees collectively reference 15 unique
    partial products: 5 diagonals (a0², a1², a2², a3², a4²) and 10
    cross-products (a0·a1, a0·a2, …, a3·a4).  Each cross-product
    appears in exactly one output-limb sum because of the symmetric
    schoolbook structure (the duplicate a[j]*a[i] is collapsed into
    a 2× factor on a[i]*a[j], i < j).

    Carry propagation (the x25..x50 chain in
    [fiat_25519_carry_square]) is folded into the algebraic
    [square_inline_correct] hypothesis in [Fe25519SquareCorrect.v];
    see header for why a sequenced [REdLimbStore] chain is deferred. *)
Definition fe25519_square_body : function_body_ed :=
  fun dest args =>
    match args with
    | [a_loc] =>
        let av := a_loc.(loc_var) in
        (* h0 = a0*a0 + 38*a1*a4 + 38*a2*a3 *)
        let e0 :=
          SAdd (ssq_diag av 0)
            (SAdd (ssq_cross_scaled av 1 4 38)
                  (ssq_cross_scaled av 2 3 38)) in
        (* h1 = 2*a0*a1 + 38*a2*a4 + 19*a3*a3 *)
        let e1 :=
          SAdd (ssq_cross_scaled av 0 1 2)
            (SAdd (ssq_cross_scaled av 2 4 38)
                  (ssq_diag_scaled av 3 19)) in
        (* h2 = 2*a0*a2 + a1*a1 + 38*a3*a4 *)
        let e2 :=
          SAdd (ssq_cross_scaled av 0 2 2)
            (SAdd (ssq_diag av 1)
                  (ssq_cross_scaled av 3 4 38)) in
        (* h3 = 2*a0*a3 + 2*a1*a2 + 19*a4*a4 *)
        let e3 :=
          SAdd (ssq_cross_scaled av 0 3 2)
            (SAdd (ssq_cross_scaled av 1 2 2)
                  (ssq_diag_scaled av 4 19)) in
        (* h4 = 2*a0*a4 + 2*a1*a3 + a2*a2 *)
        let e4 :=
          SAdd (ssq_cross_scaled av 0 4 2)
            (SAdd (ssq_cross_scaled av 1 3 2)
                  (ssq_diag av 2)) in
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
    [function_table_ed] with this to delegate square through
    [REdCallFn] instead of the (Phase 0a) [REdCall
    "fe25519_square_prim" ...] extern-FFI form. *)
Definition fe25519_square_table : function_table_ed :=
  [ ("fe25519_square", fe25519_square_body) ].

(* ================================================================ *)
(* §3.  Sanity: count of REdLimbStores                               *)
(* ================================================================ *)

(** [num_red_limb_stores] gives the surface count.  This is checked
    to be 5 below (one per output limb of the radix-2^51
    representation, mirroring [Fe25519MulBody]). *)
Fixpoint num_red_limb_stores (c : rust_cmd_ed) : nat :=
  match c with
  | REdLimbStore _ _ _ => 1%nat
  | REdSeq c1 c2 => Nat.add (num_red_limb_stores c1) (num_red_limb_stores c2)
  | _ => 0%nat
  end.

Example fe25519_square_body_stores_5 :
  num_red_limb_stores
    (fe25519_square_body
       (LFpSquare "dest"%string) [LFpSquare "a"%string]) = 5%nat.
Proof. reflexivity. Qed.
