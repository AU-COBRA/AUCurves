(** * Fe25519AddSubBody — rust_cmd_ed AST scaffolds for [fe25519_add]
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
 *  This file is the AST-level scaffold step.  It:
 *    1. Names two function bodies [fe25519_add_body] /
 *       [fe25519_sub_body] of type [function_body_ed].
 *    2. Defines their AST as a single delegated [REdCall] to a
 *       lower-level leaf [fe25519_add_prim] / [fe25519_sub_prim].
 *       The rename signals that the *high-level* name
 *       [fe25519_add] is now a verified-helper entry (callable via
 *       [REdCallFn]), while the lower-level [fe25519_add_prim] is
 *       the residual primitive op.
 *    3. Companion [Fe25519AddSubCorrect.v] then proves
 *       [fe25519_add_body_correct] / [fe25519_sub_body_correct]
 *       under hypotheses about [fe25519_add_prim] / [fe25519_sub_prim].
 *
 *  Breadcrumbs for the follow-up Phase-0b step (eliminating the
 *  inner [_prim] leaf entirely):
 *
 *    The IR's [rust_cmd_ed] currently has no per-limb access to a
 *    [TFp25519] slot — that type stores its 5×u64 radix-2^51 limbs
 *    as a sealed [VFp25519 limbs] payload.  To express the
 *    fiat-crypto bedrock2 extraction of [fe25519_add]
 *    (5 limb-additions + carry chain) directly in [rust_cmd_ed], we
 *    must either:
 *
 *      (a) Add an [REdLimbLoad : var -> located_ed -> nat ->
 *           rust_cmd_ed] / [REdLimbStore : located_ed -> nat ->
 *           sexpr_ed -> rust_cmd_ed] pair giving limb-indexed
 *           read/write into [TFp25519].
 *
 *      (b) Refactor [TFp25519] to [TArr 5 (TScalar TU64)] and reuse
 *           the existing [REdArrLoad] / [REdArrStore].  This requires
 *           introducing a [TScalar] u64 leaf type into [tower_type_ed]
 *           and routing it through [rust_val_ed] / [tt_zero_ed] /
 *           [well_formed_ed] / [tt_bytes_ed] / [tt_encode].
 *
 *    Option (a) is additive and local; option (b) is more uniform
 *    with the rest of the IR (no special-case u64 ops).  Either way,
 *    once limb access is available, [fe25519_add_body] becomes
 *
 *        for i in 0..5 { out[i] := a[i] + b[i] }
 *        (* + final-carry chain, 1 extra round of mask/shift/add *)
 *
 *    and [fe25519_sub_body] mirrors with constant [+ 2*p_offset] to
 *    keep limbs non-negative.  The proof of [..._body_correct]
 *    against [F.add] / [F.sub] then mirrors fiat-crypto's
 *    [add_correct] / [sub_correct] bedrock2 theorems.
 *
 *  This file is closed [Qed].  [Fe25519AddSubCorrect.v] is closed
 *  [Admitted] (chain-walk pending), in the same shape as
 *  [Fe25519InvertCorrect.v]'s headline theorem.
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
    [p = 2^255 - 19].

    Surface AST: a single [REdCall] to the lower-level primitive
    [fe25519_add_prim] [dest [a; b]].  The primitive's semantics
    [add_prim_correct] (see [Fe25519AddSubCorrect.v]) is supplied as
    a section hypothesis exactly as
    [Fe25519InvertCorrect.fe25519_invert_correct] supplies
    [sqr_correct]/[mul_correct]/[copy_correct].

    Note (Phase-0a vs. Phase-0b): at this AST level the body is one
    [REdCall], which the existing printer emits as a single
    `extern "C"` call to [fe25519_add_prim].  Phase 0b will replace
    this body with an inline per-limb addition chain once the IR
    gains limb-level access (see file header breadcrumb). *)
Definition fe25519_add_body : function_body_ed :=
  fun dest args =>
    match args with
    | [a_loc; b_loc] =>
        REdCall "fe25519_add_prim" dest [a_loc; b_loc]
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
