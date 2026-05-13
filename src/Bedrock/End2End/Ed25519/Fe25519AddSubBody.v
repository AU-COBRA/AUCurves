(** * Fe25519AddSubBody — rust_cmd_ed AST for [fe25519_add]
 *  and [fe25519_sub].
 *
 *  Phase 0 of the unsafe-block reduction plan (see
 *  [AUCurves/docs/signal-stack-status-2026-05-13.md] §6.3): the
 *  curve25519-jasmin-rs crate currently calls fiat-crypto's
 *  C-extracted [fe25519_add] / [fe25519_sub] through `extern "C"`
 *  wrappers, contributing ~150 `unsafe` blocks crate-wide.  Moving
 *  those leaves to the [rust_cmd_ed → emitted Rust] pipeline
 *  (already used for [Fe25519InvertBody.v], [MontToEdwardsBody.v],
 *  [XEdDSAVerifyBody.v]) eliminates the `extern "C"` boundaries for
 *  these symbols and drops gcc/clang from the runtime trust set.
 *
 *  Status (Phase 0b, 2026-05-13)
 *  =============================
 *  [fe25519_add_body] is now an INLINE 5-limb radix-2^51 add chain
 *  expressed entirely in [rust_cmd_ed] via the new [REdLimbStore] +
 *  [SLimb] constructors (see [SafeRustEd25519Sim.v] §1).  No
 *  [extern "C"] FFI boundary remains for this leaf.  Emitted Rust
 *  code is [dest[i] = a[i].wrapping_add(b[i])] for i = 0..4 (the
 *  five-limb-store sequence).  The matching C/bedrock2 emission is
 *  also pure — store_word(addr_of(dest) + 8*i, ...).
 *
 *  [fe25519_sub_body] is unchanged from Phase 0a (still one
 *  [REdCall "fe25519_sub_prim" ...]) — converting it to inline form
 *  is mechanical given the new IR but requires the +2p offset
 *  constants which we did not thread through Phase 0b scaffolding.
 *  See FOLLOW-UP at end of file.
 *
 *  History
 *  =======
 *  Phase 0a (2026-05-12, commit 6999797):
 *    Body was [REdCall "fe25519_add_prim" dest [a; b]] — one
 *    extern "C" call.  Three-line proof via [add_prim_correct]
 *    section hypothesis.
 *  Phase 0b (2026-05-13, this file):
 *    Body is [REdSeq (REdLimbStore ...) ...] × 5 — full inline.
 *    Proof structure unchanged ([add_inline_correct] section
 *    hypothesis), three-line delegation.  Mechanical discharge of
 *    that hypothesis against fiat-crypto's [Positional.add_correct]
 *    is the Phase 0c follow-up.
 *
 *  IR EXTENSION
 *  ============
 *  Phase 0b extends [rust_cmd_ed] / [bedrock_cmd_ed] /
 *  [sexpr_ed] with:
 *    - [REdLimbStore (loc : located_ed) (i : nat) (e : sexpr_ed)]
 *      — writes limb [i] of a [TFp25519] slot.
 *    - [SLimb (v : var) (i : nat)] — reads limb [i] of a tower slot
 *      named [v] (supports TFp25519, TFp25519_64, TFpL25519).
 *    - [BEdLimbStore] mirror in [bedrock_cmd_ed].
 *  Semantic cases [rexec_limb_store_fp25519] /
 *  [bexec_limb_store_fp25519] handle the inductive transition.
 *  Bridge layers (BorrowCheck, NormalizeSelect, InlineCallFn,
 *  RustCmdToC, RustCmdToRust, CTLevel, WPBridge) all carry stub
 *  cases — see those files for per-pass treatment.  No new global
 *  axioms.
 *
 *  FOLLOW-UP (Phase 0c, deferred)
 *  ==============================
 *  1. Discharge [add_inline_correct] mechanically by importing
 *     fiat-crypto's [Positional.add_correct] (radix-2^51) and
 *     chaining through [rexec_limb_store_fp25519] inversions.
 *     Estimated ~150 LoC.
 *  2. Inline [fe25519_sub_body] using the same scheme with
 *     hard-coded +2p offset constants in [SLit] form (fiat-crypto's
 *     [sub_op] subtracts then adds [2 * Positional.encode_2p]).
 *  3. Apply the same recipe to [fe25519_mul], [fe25519_square],
 *     [fe25519_carry] — each is ~25 [REdLimbStore]s.  This drops
 *     5 more `extern "C"` symbols, ~30 unsafe blocks at protocol
 *     callsites.
 *  4. Discharge [SLimb] in the WP bridge ([SafeRustEd25519WPBridge.v]
 *     [sexpr_well_formed] case) by extending [state_refine_ed] with
 *     a per-slot address oracle.
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
Definition LFp (v : String.string) : located_ed :=
  {| loc_var := v; loc_type := TFp25519 |}.

(* ================================================================ *)
(* §2.  fe25519_add / fe25519_sub bodies                             *)
(* ================================================================ *)

(** [fe25519_add_body] computes [dest := a + b] in [F p],
    [p = 2^255 - 19], inlined as a 5-limb radix-2^51 add chain.

    Surface AST: five [REdLimbStore] writes, each setting limb [i] of
    [dest] to [SLimb a i + SLimb b i].  Mirrors fiat-crypto's
    [add_op] / bedrock2 emission [out[i] := a[i] + b[i]] for
    i = 0..4.  No carry is performed — bound growth is one bit per
    add, so up to 2^14 chained adds stay within the radix-2^51 +
    slack envelope; callers wanting a fully reduced output compose
    [fe25519_carry] afterwards (matching fiat-crypto's
    [carry_add_op] decomposition).

    Phase 0b status (2026-05-13): IR-level body is inline — no
    [REdCall] / [extern "C"] in the surface emission.  The
    correctness obligation (limb-wise [F.add]) is supplied as a
    section hypothesis [add_inline_correct] in
    [Fe25519AddSubCorrect.v]; full mechanical discharge requires
    importing fiat-crypto's [Positional.add_correct] for radix-2^51
    and is left as the immediate Phase 0c follow-up.

    History:
      Phase 0a (2026-05-12, commit 6999797): body was a single
        [REdCall "fe25519_add_prim" dest [a; b]] (one extern "C").
      Phase 0b (2026-05-13, this file): body is inline limb chain
        using [REdLimbStore] + [SLimb] from
        [SafeRustEd25519Sim.v]. *)
Definition fe25519_add_body : function_body_ed :=
  fun dest args =>
    match args with
    | [a_loc; b_loc] =>
        let a_v := a_loc.(loc_var) in
        let b_v := b_loc.(loc_var) in
        REdSeq
          (REdLimbStore dest 0%nat (SAdd (SLimb a_v 0%nat) (SLimb b_v 0%nat)))
          (REdSeq
            (REdLimbStore dest 1%nat (SAdd (SLimb a_v 1%nat) (SLimb b_v 1%nat)))
            (REdSeq
              (REdLimbStore dest 2%nat (SAdd (SLimb a_v 2%nat) (SLimb b_v 2%nat)))
              (REdSeq
                (REdLimbStore dest 3%nat (SAdd (SLimb a_v 3%nat) (SLimb b_v 3%nat)))
                (REdLimbStore dest 4%nat (SAdd (SLimb a_v 4%nat) (SLimb b_v 4%nat))))))
    | _ => REdSkip
    end.

(** [fe25519_sub_body] computes [dest := a - b] in [F p]. *)
Definition fe25519_sub_body : function_body_ed :=
  fun dest args =>
    match args with
    | [a_loc; b_loc] =>
        REdCall "fe25519_sub_prim" dest [a_loc; b_loc]
    | _ => REdSkip
    end.

(** Public function-table entries.  Downstream callers (e.g. the
    bedrock2-to-RustCmd bridge in [Scalarmult_Impl_RustCmd], or any
    body that wants to delegate add/sub through [REdCallFn] instead
    of [REdCall]) extend their [function_table_ed] with these. *)
Definition fe25519_add_sub_table : function_table_ed :=
  [ ("fe25519_add", fe25519_add_body)
  ; ("fe25519_sub", fe25519_sub_body) ].
