(** * BuildCombTableBody — rust_cmd_ed AST for the comb-table
 *     initialiser used by the windowed scalar multiplication.
 *
 *  Builds a precomputed table
 *
 *      cells[i*16 + d] = d · 16^i · B    for i ∈ 0..63, d ∈ 0..15,
 *
 *  where B is the Ed25519 base point.  The table is laid out flat
 *  in a single [TArr 1024 TFp25519] slot indexed [i*16 + d].
 *
 *  Inner loop ([d]): cumulatively add [16^i · B] starting from 0.
 *  Outer loop ([i]): square-doublings of the base point 16-times to
 *  step from [16^i] to [16^(i+1)], realised here as repeated
 *  application of an external [point_mul16] leaf.
 *
 *  For the math/structural proof in
 *  [BuildCombTableCorrect.v] we keep the body deliberately simple:
 *  the [d=0] cell is set to the identity (REdLetZero leaves zero in
 *  place), and the d-th cell is filled by [point_add_to_cell(cells,
 *  i, d, base_i)].  The semantics of [point_add_to_cell] is supplied
 *  by an oracle [Hypothesis] in the Correct file.
 *
 *  Phase 2.C of "extend the IR": Part C of the three-chain prompt.
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
(* §1. Helpers                                                       *)
(* ================================================================ *)

Definition LFp (v : String.string) : located_ed :=
  {| loc_var := v; loc_type := TFp25519 |}.

Definition LCells (v : String.string) : located_ed :=
  {| loc_var := v; loc_type := TArr 1024 TFp25519 |}.

Fixpoint seqN (l : list rust_cmd_ed) : rust_cmd_ed :=
  match l with
  | [] => REdSkip
  | [c] => c
  | c :: cs => REdSeq c (seqN cs)
  end.

(* ================================================================ *)
(* §2. Body                                                          *)
(* ================================================================ *)

(** Inner-loop body: given the row-base [base_i = 16^i · B] held at
    [base_i_slot], populate cells[i*16 + d] for [d = 15, 14, ..., 0]
    using
        cells[i*16 + d] := d · base_i
    realised by the oracle
        REdCall "comb_cell_set" cells [i, d, base_i].

    REdFor counts down: d = 15, 14, ..., 0 in the loop variable [d].
    The math invariant is symmetric in d, so the iteration order
    doesn't matter for the spec. *)
Definition inner_loop_cmd (i_slot d_slot : String.string)
                          (cells base_i : located_ed) : rust_cmd_ed :=
  REdFor d_slot 16
    (REdCallN "comb_cell_set" [cells]
              [{| loc_var := i_slot; loc_type := TU64 |}
              ;{| loc_var := d_slot; loc_type := TU64 |}
              ; base_i]).

(** Outer-loop body: at iteration [i], the row base [base_i]
    contains [16^i · B].  Populate the row [cells[i*16..]],
    then update [base_i := 16 · base_i] for the next iteration. *)
Definition outer_loop_cmd (i_slot d_slot : String.string)
                          (cells base_i : located_ed) : rust_cmd_ed :=
  REdSeq
    (inner_loop_cmd i_slot d_slot cells base_i)
    (REdCall "point_mul16" base_i [base_i]).
(* Note: in real Rust, point_mul16 would write to a scratch and
   copy back; here we let the oracle handle it directly. *)

(** Top-level body.

    Slots:
      [cells : TArr 1024 TFp25519]     — output table (in-place)
      [base_i : TFp25519]              — running row-base (16^i · B)

    Args:
      [B_loc : TFp25519]               — input: the base point B
      [cells_loc : TArr 1024 TFp25519] — output table slot
      [dest = cells_loc]                — out unused.

    NOTE: we conventionally take the table slot as the *first*
    argument and the base point as the *second*, so that the
    function "writes into" its first argument.  The dest is unused
    (REdSkip-like; we return via mutating cells). *)
Definition build_comb_table_body : function_body_ed :=
  fun _dest args =>
    match args with
    | [cells_loc; B_loc] =>
        REdLetZero "base_i" TFp25519 (
        REdLetZero "i_v"    TU64 (
        REdLetZero "d_v"    TU64 (
        REdSeq
          (* base_i := B *)
          (REdCall "fe25519_copy" (LFp "base_i") [B_loc])
          (REdFor "i_v" 64
            (outer_loop_cmd "i_v" "d_v" cells_loc (LFp "base_i")))
        )))
    | _ => REdSkip
    end.
