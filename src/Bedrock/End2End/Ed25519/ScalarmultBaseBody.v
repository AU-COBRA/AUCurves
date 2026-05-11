(** * ScalarmultBaseBody — verified [function_body_ed] forwarder for
 *                         fixed-generator scalar multiplication.
 *
 *  Phase 4 of the curve-leaf verification plan; companion to
 *  [ScalarmultBaseVerified.v].  Forwards [REdCallFn] dispatch to the
 *  external "fe25519_scalarmult_base" leaf (which internally uses the
 *  precomputed base-point table).
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.ScalarmultBaseVerified.
Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* §1.  Verified rust_cmd_ed body                                    *)
(* ================================================================ *)

(** Body for the "scalarmult_base" entry of the curve-level
    [function_table_ed].

    Surface: one [located_ed] argument [scalar] (32-byte slot), one
    destination [dest] (200-byte projective xyzt slot). *)
Definition scalarmult_base_body : function_body_ed :=
  fun dest args =>
    match args with
    | [scalar] => REdCall "fe25519_scalarmult_base" dest [scalar]
    | _        => REdSkip
    end.

(* ================================================================ *)
(* §2.  Correctness                                                  *)
(* ================================================================ *)

Definition scalarmult_base_callee_post_honoured
    (callee_post :
       String.string -> list located_ed -> located_ed ->
       rust_state_ed -> rust_state_ed -> Prop)
    (scalar dest : located_ed) : Prop :=
  forall (rs1 rs2 : rust_state_ed) (scalar_bs : list Byte.byte),
    dest.(loc_type) = TBytes 200 ->
    rs_get_tower_ed rs1 scalar.(loc_var)
      = Some (exist_tval_ed (TBytes 32) (VBytes 32 scalar_bs)) ->
    callee_post "fe25519_scalarmult_base" [scalar] dest rs1 rs2 ->
    rs_get_tower_ed rs2 dest.(loc_var)
      = Some (exist_tval_ed (TBytes 200)
                (VBytes 200 (ed25519_scalarmult_base_gallina scalar_bs))).

Theorem scalarmult_base_body_correct :
  forall callee_post callee_post_n function_table
         (scalar dest : located_ed)
         (rs1 rs2 : rust_state_ed)
         (scalar_bs : list Byte.byte),
    dest.(loc_type) = TBytes 200 ->
    rs_get_tower_ed rs1 scalar.(loc_var)
      = Some (exist_tval_ed (TBytes 32) (VBytes 32 scalar_bs)) ->
    scalarmult_base_callee_post_honoured callee_post scalar dest ->
    rust_exec_ed callee_post callee_post_n function_table
                 (scalarmult_base_body dest [scalar]) rs1 rs2 ->
    rs_get_tower_ed rs2 dest.(loc_var)
      = Some (exist_tval_ed (TBytes 200)
                (VBytes 200 (ed25519_scalarmult_base_gallina scalar_bs))).
Proof.
  intros callee_post callee_post_n function_table scalar dest rs1 rs2
         scalar_bs Htype Hs Hcontract Hexec.
  cbv [scalarmult_base_body] in Hexec.
  inversion Hexec; clear Hexec; subst.
  eapply Hcontract; eauto.
Qed.

(* Print Assumptions scalarmult_base_body. *)
(* Print Assumptions scalarmult_base_body_correct. *)
