(** * Fe25519FromWordBody — rust_cmd_ed AST for [fe25519_from_word].
 *
 *  Phase 0c (2026-05-13) inline trivial leaf: convert a single 64-bit
 *  scalar [w] into a 5-limb radix-2^51 [TFp25519] payload.  Mirrors
 *  fiat-crypto's [from_word_op] / bedrock2 emission [out[0] := w;
 *  out[1] := 0; ...; out[4] := 0].
 *
 *  Body is five [REdLimbStore]s: limb 0 reads the scalar slot via
 *  [SVar], limbs 1..4 write [SLit 0].  No [extern "C"] FFI boundary;
 *  Rust emission is [dest[0] = w; dest[1..4] = 0].
 *
 *  Companion correctness proof in [Fe25519FromWordCorrect.v] is
 *  parametric over the same [Fp25519_holds] / [feval] decoder used by
 *  the other Phase 0c leaves; no new GLOBAL axioms.
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

Definition LFp_fw (v : String.string) : located_ed :=
  {| loc_var := v; loc_type := TFp25519 |}.

(* ================================================================ *)
(* §2. fe25519_from_word body                                        *)
(* ================================================================ *)

(** [fe25519_from_word_body] computes [dest := F.of_Z w] in [F p]
    inline, as a 5-limb radix-2^51 store of [w] into limb 0 plus
    zeros into limbs 1..4.

    Surface AST:
      [REdLimbStore dest 0 (SVar w);
       REdLimbStore dest 1 (SLit 0);
       REdLimbStore dest 2 (SLit 0);
       REdLimbStore dest 3 (SLit 0);
       REdLimbStore dest 4 (SLit 0)]

    Mirrors fiat-crypto's [from_word_op] / bedrock2 emission
    [out[0] := w; out[1..4] := 0].  No carry is needed (a single
    limb in [0, 2^64) fits radix-2^51 + slack; callers wanting a
    fully reduced output can compose [fe25519_carry] afterwards).

    [args] is a single [located_ed] whose [loc_var] names the
    scalar source slot.  Its [loc_type] is irrelevant to the IR —
    [SVar] consults the scalar table, not the tower. *)
Definition fe25519_from_word_body : function_body_ed :=
  fun dest args =>
    match args with
    | [w_loc] =>
        let w_v := w_loc.(loc_var) in
        REdSeq
          (REdLimbStore dest 0%nat (SVar w_v))
          (REdSeq
            (REdLimbStore dest 1%nat (SLit 0))
            (REdSeq
              (REdLimbStore dest 2%nat (SLit 0))
              (REdSeq
                (REdLimbStore dest 3%nat (SLit 0))
                (REdLimbStore dest 4%nat (SLit 0)))))
    | _ => REdSkip
    end.

(** Public function-table entry. *)
Definition fe25519_from_word_table : function_table_ed :=
  [ ("fe25519_from_word", fe25519_from_word_body) ].
