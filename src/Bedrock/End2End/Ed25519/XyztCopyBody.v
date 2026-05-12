(** * XyztCopyBody — verified [function_body_ed] forwarder for a
 *                    200-byte xyzt slot copy leaf.
 *
 *  Companion to [XyztAddBody.v] / [XyztDoubleBody.v] / [ScalarmultBody.v].
 *  Added in Phase B of [docs/scalarmult-verification-plan.md] (commit b4af602)
 *  to provide a verified-helper dispatch target for the final
 *  accum → dest copy step in [scalarmult_body_decomposed].
 *
 *  Granular field-op decomposition is unnecessary here: the underlying
 *  Rust leaf is a 200-byte memcpy and the framework-level dispatch is
 *  trivially correct (one [REdCall] forward; one inversion).
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* §1.  Verified rust_cmd_ed body                                    *)
(* ================================================================ *)

(** Body for the "xyzt_copy" entry of the curve-level
    [function_table_ed].

    Surface: one [located_ed] argument [src] (a 200-byte xyzt slot),
    one destination [dest] (also a 200-byte xyzt slot). *)
Definition xyzt_copy_body : function_body_ed :=
  fun dest args =>
    match args with
    | [src] => REdCall "fe25519_xyzt_copy" dest [src]
    | _     => REdSkip
    end.

(* ================================================================ *)
(* §2.  Correctness                                                  *)
(* ================================================================ *)

(** Local callee-honoured predicate: [fe25519_xyzt_copy] copies a
    200-byte [src] slot to its 200-byte [dest] slot verbatim. *)
Definition xyzt_copy_callee_post_honoured
    (callee_post :
       String.string -> list located_ed -> located_ed ->
       rust_state_ed -> rust_state_ed -> Prop)
    (src dest : located_ed) : Prop :=
  forall (rs1 rs2 : rust_state_ed) (src_bs : list Byte.byte),
    dest.(loc_type) = TBytes 200 ->
    rs_get_tower_ed rs1 src.(loc_var)
      = Some (exist_tval_ed (TBytes 200) (VBytes 200 src_bs)) ->
    callee_post "fe25519_xyzt_copy" [src] dest rs1 rs2 ->
    rs_get_tower_ed rs2 dest.(loc_var)
      = Some (exist_tval_ed (TBytes 200) (VBytes 200 src_bs)).

Theorem xyzt_copy_body_correct :
  forall callee_post callee_post_n function_table
         (src dest : located_ed)
         (rs1 rs2 : rust_state_ed)
         (src_bs : list Byte.byte),
    dest.(loc_type) = TBytes 200 ->
    rs_get_tower_ed rs1 src.(loc_var)
      = Some (exist_tval_ed (TBytes 200) (VBytes 200 src_bs)) ->
    xyzt_copy_callee_post_honoured callee_post src dest ->
    rust_exec_ed callee_post callee_post_n function_table
                 (xyzt_copy_body dest [src]) rs1 rs2 ->
    rs_get_tower_ed rs2 dest.(loc_var)
      = Some (exist_tval_ed (TBytes 200) (VBytes 200 src_bs)).
Proof.
  intros callee_post callee_post_n function_table src dest rs1 rs2
         src_bs Htype Hsrc Hcontract Hexec.
  cbv [xyzt_copy_body] in Hexec.
  inversion Hexec; clear Hexec; subst.
  eapply Hcontract; eauto.
Qed.

(* Print Assumptions xyzt_copy_body. *)
(* Print Assumptions xyzt_copy_body_correct. *)
