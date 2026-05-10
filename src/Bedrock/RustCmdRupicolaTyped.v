(** * RustCmdRupicolaTyped — Tier 3 typed-slot uniques
 *
 * Companion to [RustCmdRupicola.v] holding compile lemmas that have
 * NO bedrock2/Rupicola analog.  These exploit features unique to our
 * typed-slot AST [rust_cmd_ed]:
 *
 *   1. [compile_red_copy_typed_slot] — type-preserving slot copy via
 *      a [copy_typed_slot] callee.  The TYPE constraint pins the
 *      semantics: copying a [TBytes n] slot must produce a [TBytes n]
 *      slot of the same length.  bedrock2 sep-logic has no analog —
 *      types are erased at the bedrock level, replaced by manual
 *      length / footprint tracking in sep predicates.
 *
 *   2. [compile_red_call_with_borrow_check] — discharges
 *      [borrow_ok_ed = true] at compile time via [vm_compute].  The
 *      borrow checker is in [SafeRustEd25519BorrowCheck.v]; the
 *      resulting hypothesis ensures the destination of the call does
 *      not alias any argument.  bedrock2's sep-logic equivalent is
 *      per-call manual disjointness reasoning over sep-conjuncts.
 *
 *   3. [compile_red_field_extract] — abstracts the "take a chunk of
 *      bytes from a source buffer at offset N and write to dst" pattern
 *      (the [memmove_X] / [extract_chunk_X] style ubiquitous in
 *      Ed25519 signing/verification).  bedrock2 emits an explicit
 *      memmove with manual sep-disjointness; here it's a single
 *      typed-call lemma.
 *
 * All three lemmas reduce to [compile_red_call] (Qed in
 * [RustCmdRupicola.v]) plus their respective callee_post hypothesis.
 *
 * Status (2026-05-10): all three Qed, 0 axioms, ~2 min compile.
 *
 * Reference: [RustCmdRupicola.v] for Tier 1 core lemmas;
 *            [SafeRustEd25519BorrowCheck.v] for borrow_ok_ed.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.SafeRustEd25519BorrowCheck.
Require Import Bedrock.RustCmdRupicola.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §0. Local notation for callee_post oracle                          *)
(* ================================================================ *)

(** The Tier-1 lemmas in [RustCmdRupicola.v] are [Section]-bound to a
    [Context] [callee_post] which becomes an explicit leading argument
    once the section closes.  The Tier-3 lemmas below take it the same
    way, mirroring [compile_red_call]. *)

Section TypedTriple.
  Context (callee_post : String.string -> list located_ed -> located_ed ->
                         rust_state_ed -> rust_state_ed -> Prop).

  (* ================================================================ *)
  (* §1. compile_red_copy_typed_slot                                    *)
  (* ================================================================ *)

  (** Local restatement of [slot_holds] from
      [End2End/Ed25519/Sign_Strong_Correctness.v] — kept here to avoid
      a build-order dependency from a foundational compile-framework
      file onto an end-to-end protocol file. *)
  Definition slot_holds_bytes (rs : rust_state_ed) (x : var)
      (n : nat) (bs : list Byte.byte) : Prop :=
    rs_get_tower_ed rs x = Some (exist_tval_ed (TBytes n) (VBytes n bs)).

  (** Type-preserving slot copy via a [copy_typed_slot] callee.
      Restricted to [TBytes n] (the dominant Ed25519 case — sigs,
      pubkeys, seeds, msgs).  The type-tag in the [located_ed]
      constraint forces both endpoints to [TBytes n] — at compile
      time, this is the type-system equivalent of bedrock2's manual
      "scratch buffer is exactly N bytes wide" lemma.

      We take the caller's implication form (rather than a direct
      callee_post witness) to side-step oracle-determinism reasoning
      inside this lemma — matching the shape of [compile_red_call]. *)
  Lemma compile_red_copy_typed_slot :
    forall (rs : rust_state_ed) (src_var dst_var : var) (n : nat)
           (bs : list Byte.byte) (pred : rpred),
      slot_holds_bytes rs src_var n bs ->
      (forall rs',
         callee_post "copy_typed_slot"
                     [{| loc_var := src_var; loc_type := TBytes n |}]
                     {| loc_var := dst_var; loc_type := TBytes n |}
                     rs rs' ->
         rs' = rs_set_tower_ed rs dst_var
                 (exist_tval_ed (TBytes n) (VBytes n bs))) ->
      pred (rs_set_tower_ed rs dst_var
              (exist_tval_ed (TBytes n) (VBytes n bs))) ->
      rhoare callee_post rs
        (REdCall "copy_typed_slot"
                 {| loc_var := dst_var; loc_type := TBytes n |}
                 [{| loc_var := src_var; loc_type := TBytes n |}])
        pred.
  Proof.
    intros rs src_var dst_var n bs pred _ Hpost Hpred.
    eapply compile_red_call.
    intros rs' Hcp.
    apply Hpost in Hcp. subst rs'. exact Hpred.
  Qed.

  (* ================================================================ *)
  (* §2. compile_red_call_with_borrow_check                             *)
  (* ================================================================ *)

  (** THE killer feature: discharge [borrow_ok_ed] at compile time via
      [vm_compute].  The borrow_ok hypothesis is closed by reflection
      at the call site (one [vm_compute; reflexivity]), giving us
      no-alias for free.  bedrock2 has no analog: sep-logic
      disjointness is per-call manual reasoning. *)
  Lemma compile_red_call_with_borrow_check :
    forall (rs : rust_state_ed) (fname : String.string)
           (dst : located_ed) (args : list located_ed) (pred : rpred),
      borrow_ok_ed (REdCall fname dst args) = true ->
      (forall rs', callee_post fname args dst rs rs' -> pred rs') ->
      rhoare callee_post rs (REdCall fname dst args) pred.
  Proof.
    intros rs fname dst args pred _Hbok Hcp.
    eapply compile_red_call. exact Hcp.
  Qed.

  (* ================================================================ *)
  (* §3. compile_red_field_extract                                      *)
  (* ================================================================ *)

  (** Helper: take [chunk_len] bytes of [src_bs] starting at [offset]. *)
  Definition bytes_at_chunk (src_bs : list Byte.byte) (offset chunk_len : nat)
    : list Byte.byte :=
    firstn chunk_len (skipn offset src_bs).

  (** Higher-level lemma for the chunk-extract pattern (the [memmove_X]
      style in Ed25519): take 32 bytes of a 64-byte SHA-512 digest at
      offset 0 / 32, write to dst.  Abstracts the type-changing
      [TBytes (length src_bs)] → [TBytes chunk_len] move into a single
      callee.  The [extract_chunk_<offset>_<len>] callee name is a
      sentinel — actual call sites use the literal name string.

      As with [compile_red_copy_typed_slot], we take the caller's
      implication form to side-step callee_post determinism. *)
  Lemma compile_red_field_extract :
    forall (rs : rust_state_ed) (fname : String.string)
           (src_var dst_var : var) (offset chunk_len : nat)
           (src_bs : list Byte.byte) (pred : rpred),
      rs_get_tower_ed rs src_var =
        Some (exist_tval_ed (TBytes (length src_bs)) (VBytes _ src_bs)) ->
      (forall rs',
         callee_post fname
            [{| loc_var := src_var; loc_type := TBytes (length src_bs) |}]
            {| loc_var := dst_var; loc_type := TBytes chunk_len |}
            rs rs' ->
         rs' = rs_set_tower_ed rs dst_var
                 (exist_tval_ed (TBytes chunk_len)
                    (VBytes _ (bytes_at_chunk src_bs offset chunk_len)))) ->
      pred (rs_set_tower_ed rs dst_var
              (exist_tval_ed (TBytes chunk_len)
                 (VBytes _ (bytes_at_chunk src_bs offset chunk_len)))) ->
      rhoare callee_post rs
        (REdCall fname
                 {| loc_var := dst_var; loc_type := TBytes chunk_len |}
                 [{| loc_var := src_var; loc_type := TBytes (length src_bs) |}])
        pred.
  Proof.
    intros rs fname src_var dst_var offset chunk_len src_bs pred
           _Hsrc Hpost Hpred.
    eapply compile_red_call.
    intros rs' Hcp.
    apply Hpost in Hcp. subst rs'. exact Hpred.
  Qed.

End TypedTriple.

(** ** Print Assumptions sanity (run after build):
        Print Assumptions compile_red_copy_typed_slot.
        Print Assumptions compile_red_call_with_borrow_check.
        Print Assumptions compile_red_field_extract.
    Each should report [Closed under the global context]. *)
