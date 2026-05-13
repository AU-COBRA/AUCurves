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
 *  Status (Phase 0c, 2026-05-13)
 *  =============================
 *  [fe25519_add_body] is an INLINE 5-limb radix-2^51 add chain
 *  expressed entirely in [rust_cmd_ed] via the [REdLimbStore] +
 *  [SLimb] constructors (see [SafeRustEd25519Sim.v] §1).  No
 *  [extern "C"] FFI boundary remains for this leaf.  Emitted Rust
 *  code is [dest[i] = a[i].wrapping_add(b[i])] for i = 0..4 (the
 *  five-limb-store sequence).  The matching C/bedrock2 emission is
 *  also pure — store_word(addr_of(dest) + 8*i, ...).
 *
 *  [fe25519_sub_body] (Phase 0c, 2026-05-13) is now also an INLINE
 *  5-limb chain: [dest[i] := (a[i] - b[i]) + 2 * encode_2p[i]] via
 *  [REdLimbStore + SAdd + SSub + SLit].  Parameterised by [p_off :
 *  nat -> Z] which the caller instantiates with fiat-crypto's
 *  per-limb [2 * Positional.encode_2p] constants for radix-2^51 (the
 *  borrow-correction constants emitted by [sub_op]).
 *
 *  Correctness for both leaves is in [Fe25519AddSubCorrect.v] (Phase
 *  0c).  The two top-level theorems
 *  [fe25519_add_body_correct] / [fe25519_sub_body_correct] are Qed,
 *  reduced to four mechanical Section [Hypothesis] statements at the
 *  limb level ([Fp25519_holds_intro] / [Fp25519_holds_elim] /
 *  [Fp25519_holds_set_other] / [feval_limbwise_(add|sub)_mask64]).
 *  These section hypotheses become Π-quantified parameters of the
 *  closed theorems and discharge to fiat-crypto's [add_correct] /
 *  [sub_correct] at instantiation time.  Print Assumptions reports
 *  "Closed under the global context" — no new global axioms.
 *
 *  History
 *  =======
 *  Phase 0a (2026-05-12, commit 6999797):
 *    Body was [REdCall "fe25519_add_prim" dest [a; b]] — one
 *    extern "C" call.  Three-line proof via [add_prim_correct]
 *    section hypothesis.
 *  Phase 0b (2026-05-13, commit f9578ce):
 *    [fe25519_add_body] became [REdSeq (REdLimbStore ...) ...] × 5
 *    — full inline.  Proof via [add_inline_correct] section
 *    hypothesis.  [fe25519_sub_body] still [REdCall].
 *  Phase 0c (2026-05-13, this file):
 *    Both leaves inline.  [add_inline_correct] / [sub_inline_correct]
 *    promoted from section [Hypothesis] to internal [Lemma] in
 *    [Fe25519AddSubCorrect.v], discharged mechanically against four
 *    limb-level Section hypotheses.
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
 *  FOLLOW-UP (Phase 0d, deferred)
 *  ==============================
 *  1. Apply the same recipe to [fe25519_mul], [fe25519_square],
 *     [fe25519_carry] — each is ~25 [REdLimbStore]s.  The proof
 *     pattern in [Fe25519AddSubCorrect.v] (5 [rexec_limb_store_inv]
 *     + [is_addN_eq_build] + [feval_limbwise_*_mask64]) extends
 *     directly; mul/square need [SMul] (already in IR) and a
 *     multi-limb folding helper.  This drops 5 more `extern "C"`
 *     symbols, ~30 unsafe blocks at protocol callsites.
 *  2. Discharge [SLimb] in the WP bridge ([SafeRustEd25519WPBridge.v]
 *     [sexpr_well_formed] case) by extending [state_refine_ed] with
 *     a per-slot address oracle.
 *  3. Instantiate the limb-level Section hypotheses at the
 *     [Scalarmult_Impl_RustCmd] level using fiat-crypto's
 *     [Positional.eval] composed with [F.of_Z], to convert the
 *     Section-quantified [fe25519_add_body_correct] into a
 *     theorem about a concrete [Fp25519_holds].
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

(** [fe25519_sub_body] computes [dest := a - b] in [F p] inline, using
    the +2p offset correction per limb (Phase 0c, 2026-05-13).

    Surface AST: five [REdLimbStore] writes, each setting limb [i] of
    [dest] to [SAdd (SSub (SLimb a i) (SLimb b i)) (SLit (p_off i))].
    Mirrors fiat-crypto's [sub_op] / bedrock2 emission
    [out[i] := (a[i] - b[i]) + 2 * encode_2p[i]] for i = 0..4 (radix-2^51
    sub-with-borrow correction).  No carry is performed — bound growth
    matches fiat-crypto's no-carry [sub], callers wanting a fully
    reduced output compose [fe25519_carry] afterwards.

    The function body is parameterized by [p_off : nat -> Z] — the
    radix-2^51 borrow-correction constants.  At instantiation time
    [p_off] is supplied as the fiat-crypto-generated literal list
    [[0xfffffffffffda; 0xffffffffffffe; ...]] (concrete values
    depend on the chosen radix-2^51 modulus encoding).  See
    [Fe25519AddSubCorrect.v] for the algebraic correctness proof, which
    is mechanical given [feval_limbwise_sub_mask64].

    History:
      Phase 0a (2026-05-12, commit 6999797): body was a single
        [REdCall "fe25519_sub_prim" dest [a; b]] (one extern "C").
      Phase 0b (2026-05-13, commit f9578ce): body unchanged from 0a;
        plan to inline once the IR carried the new [SLit]/[REdLimbStore]
        constructors.
      Phase 0c (2026-05-13, this file): inline 5-limb chain.  Drops the
        last [extern "C"] FFI for fe25519 add/sub. *)
Definition fe25519_sub_body (p_off : nat -> Z) : function_body_ed :=
  fun dest args =>
    match args with
    | [a_loc; b_loc] =>
        let a_v := a_loc.(loc_var) in
        let b_v := b_loc.(loc_var) in
        REdSeq
          (REdLimbStore dest 0%nat
             (SAdd (SSub (SLimb a_v 0%nat) (SLimb b_v 0%nat))
                   (SLit (p_off 0%nat))))
          (REdSeq
            (REdLimbStore dest 1%nat
               (SAdd (SSub (SLimb a_v 1%nat) (SLimb b_v 1%nat))
                     (SLit (p_off 1%nat))))
            (REdSeq
              (REdLimbStore dest 2%nat
                 (SAdd (SSub (SLimb a_v 2%nat) (SLimb b_v 2%nat))
                       (SLit (p_off 2%nat))))
              (REdSeq
                (REdLimbStore dest 3%nat
                   (SAdd (SSub (SLimb a_v 3%nat) (SLimb b_v 3%nat))
                         (SLit (p_off 3%nat))))
                (REdLimbStore dest 4%nat
                   (SAdd (SSub (SLimb a_v 4%nat) (SLimb b_v 4%nat))
                         (SLit (p_off 4%nat)))))))
    | _ => REdSkip
    end.

(** Public function-table entries.  Downstream callers (e.g. the
    bedrock2-to-RustCmd bridge in [Scalarmult_Impl_RustCmd], or any
    body that wants to delegate add/sub through [REdCallFn] instead
    of [REdCall]) extend their [function_table_ed] with these.
    Parameterised by [p_off] (the radix-2^51 borrow-correction constants
    used by sub). *)
Definition fe25519_add_sub_table (p_off : nat -> Z) : function_table_ed :=
  [ ("fe25519_add", fe25519_add_body)
  ; ("fe25519_sub", fe25519_sub_body p_off) ].
