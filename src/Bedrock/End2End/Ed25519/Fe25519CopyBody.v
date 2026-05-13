(** * Fe25519CopyBody — rust_cmd_ed AST for [fe25519_copy].
 *
 *  Phase 0c (2026-05-13) inline trivial leaf: copy a 5-limb radix-2^51
 *  [TFp25519] payload into a destination slot.  Mirrors fiat-crypto's
 *  [copy_op] / bedrock2 emission [out[i] := a[i]] for i = 0..4.
 *
 *  Body is five [REdLimbStore]s, each writing [SLimb a i] (the [i]-th
 *  limb of the source) into limb [i] of [dest].  No [extern "C"] FFI
 *  boundary; Rust emission is [dest[i] = a[i]] per limb.
 *
 *  Companion correctness proof in [Fe25519CopyCorrect.v] is parametric
 *  over the same [Fp25519_holds] / [feval] decoder used by
 *  [Fe25519AddSubCorrect.v]; no new section hypotheses are required
 *  because limb-list identity preserves [feval].  No new global axioms.
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

(** Construct a [located_ed] for a [TFp25519] slot by name. *)
Definition LFp_copy (v : String.string) : located_ed :=
  {| loc_var := v; loc_type := TFp25519 |}.

(* ================================================================ *)
(* §2. fe25519_copy body                                             *)
(* ================================================================ *)

(** [fe25519_copy_body] computes [dest := a] in [F p] inline, as a
    5-limb radix-2^51 copy chain.

    Surface AST: five [REdLimbStore] writes, each setting limb [i] of
    [dest] to [SLimb a i].  Mirrors fiat-crypto's [copy_op] / bedrock2
    emission [out[i] := a[i]] for i = 0..4.  Note that [eval_sexpr_ed]
    applies [mask64] to the [SLimb] read so the IR-level limb is
    [mask64 (nth i la 0)]; the limb-bound regime (each input limb in
    [0, 2^54) for radix-2^51) makes [mask64] the identity on input
    limbs, so the copy is semantically the input limb list. *)
Definition fe25519_copy_body : function_body_ed :=
  fun dest args =>
    match args with
    | [a_loc] =>
        let a_v := a_loc.(loc_var) in
        REdSeq
          (REdLimbStore dest 0%nat (SLimb a_v 0%nat))
          (REdSeq
            (REdLimbStore dest 1%nat (SLimb a_v 1%nat))
            (REdSeq
              (REdLimbStore dest 2%nat (SLimb a_v 2%nat))
              (REdSeq
                (REdLimbStore dest 3%nat (SLimb a_v 3%nat))
                (REdLimbStore dest 4%nat (SLimb a_v 4%nat)))))
    | _ => REdSkip
    end.

(** Public function-table entry. *)
Definition fe25519_copy_table : function_table_ed :=
  [ ("fe25519_copy", fe25519_copy_body) ].
