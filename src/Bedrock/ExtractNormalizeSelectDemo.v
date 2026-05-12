(** * ExtractNormalizeSelectDemo: validate the [normalize_select] pre-pass
 *
 *  Companion to [NormalizeSelect.v].  This file exercises the
 *  Option C pipeline on a body that DOES contain [REdSelect] and
 *  emits Jasmin text via [pp_cmd] to verify that:
 *
 *    1. The bedrock2-stub for [REdSelect] (cmd.cond skip skip) is no
 *       longer in the output — every byte is materialized.
 *    2. [pp_cmd] produces legible Jasmin: a long sequence of byte
 *       load/store ops, no `if (cond) { } else { }` control flow.
 *    3. The mask-merge expression
 *           (bt & __sel_mask__) + (bf & __sel_not_mask__)
 *       appears once per byte index.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.NormalizeSelect.
Require Import Bedrock.RustCmdEdToJasmin.
Require Import Bedrock.Jasmin.Core.
Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* §1. Normalized 32-byte CT-cmov demo                               *)
(* ================================================================ *)

(** Direct Jasmin extraction of a [REdSelect] body.  Before the pass,
    this would emit a `if (cond) { } else { }` empty-arm stub
    (destroys CT).  After the pass, this emits 32 byte-load + 32
    byte-store ops, each with the explicit mask-merge expression —
    purely branch-free. *)
Definition select_jasmin_32 : jasmin_cmd :=
  rust_cmd_ed_to_jasmin select_only_demo_32.

(** Pretty-printed Jasmin source — usable as a paste-in for the
    jasminc invocation. *)
Definition select_jasmin_32_text : string :=
  pp_cmd "  " select_jasmin_32.

(** Also keep the unwrapped (bedrock-stub) text around so we can
    diff the two pipelines and show the qualitative difference. *)
Definition select_jasmin_32_unwrapped : jasmin_cmd :=
  rust_cmd_ed_to_jasmin_unwrapped select_only_demo_32.

Definition select_jasmin_32_unwrapped_text : string :=
  pp_cmd "  " select_jasmin_32_unwrapped.

(* ================================================================ *)
(* §2. Sanity: count byte stores in the Jasmin output                *)
(* ================================================================ *)

(** Use the source-level counters in [NormalizeSelect.v] to assert
    that we get 32 byte stores in the *normalized rust_cmd_ed*; the
    Jasmin emitter produces one [JCstore] per [REdByteStore] so the
    Jasmin output has the same count. *)
Lemma byte_stores_round_trip_32 :
  count_byte_stores (normalize_select select_only_demo_32) = 32%nat.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* §3. Extraction of Jasmin text                                     *)
(* ================================================================ *)

(** Dump the new (mask-merge) Jasmin output.  Inspectable via
    [Eval vm_compute in select_jasmin_32_text]. *)
Redirect "select_jasmin_32_text"
  Eval vm_compute in select_jasmin_32_text.

(** Dump the OLD (bedrock2-stub) Jasmin output for diff. *)
Redirect "select_jasmin_32_unwrapped_text"
  Eval vm_compute in select_jasmin_32_unwrapped_text.

(** Larger demo at N=200 (matches the scalarmult-ladder slot
    size). *)
Definition select_jasmin_200 : jasmin_cmd :=
  rust_cmd_ed_to_jasmin select_only_demo_200.

Definition select_jasmin_200_text : string :=
  pp_cmd "  " select_jasmin_200.

Redirect "select_jasmin_200_text"
  Eval vm_compute in select_jasmin_200_text.

Lemma byte_stores_round_trip_200 :
  count_byte_stores (normalize_select select_only_demo_200) = 200%nat.
Proof. vm_compute. reflexivity. Qed.
