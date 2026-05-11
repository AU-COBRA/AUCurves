(** * XyztDoubleBody — verified [function_body_ed] forwarder for the
 *                     extended-twisted-Edwards point doubling leaf.
 *
 *  Phase 3 of the curve-leaf verification plan; companion to
 *  [XyztDoubleVerified.v].  Same pattern as [XyztAddBody.v] but with
 *  a single point operand instead of two.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.XyztDoubleVerified.
Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* §1.  Verified rust_cmd_ed body                                    *)
(* ================================================================ *)

(** Body for the "xyzt_double" entry of the curve-level
    [function_table_ed].

    Surface: one [located_ed] argument [P], one destination [dest]
    (both 200-byte projective xyzt slots).  Forwarded to a single
    [REdCall] to the external "fe25519_xyzt_double" leaf. *)
Definition xyzt_double_body : function_body_ed :=
  fun dest args =>
    match args with
    | [P] => REdCall "fe25519_xyzt_double" dest [P]
    | _   => REdSkip
    end.

(* ================================================================ *)
(* §2.  Correctness                                                  *)
(* ================================================================ *)

Definition xyzt_double_callee_post_honoured
    (callee_post :
       String.string -> list located_ed -> located_ed ->
       rust_state_ed -> rust_state_ed -> Prop)
    (P dest : located_ed) : Prop :=
  forall (rs1 rs2 : rust_state_ed) (p_bs : list Byte.byte),
    dest.(loc_type) = TBytes 200 ->
    rs_get_tower_ed rs1 P.(loc_var)
      = Some (exist_tval_ed (TBytes 200) (VBytes 200 p_bs)) ->
    callee_post "fe25519_xyzt_double" [P] dest rs1 rs2 ->
    rs_get_tower_ed rs2 dest.(loc_var)
      = Some (exist_tval_ed (TBytes 200)
                (VBytes 200 (ed25519_xyzt_double_gallina p_bs))).

Theorem xyzt_double_body_correct :
  forall callee_post callee_post_n function_table
         (P dest : located_ed)
         (rs1 rs2 : rust_state_ed)
         (p_bs : list Byte.byte),
    dest.(loc_type) = TBytes 200 ->
    rs_get_tower_ed rs1 P.(loc_var)
      = Some (exist_tval_ed (TBytes 200) (VBytes 200 p_bs)) ->
    xyzt_double_callee_post_honoured callee_post P dest ->
    rust_exec_ed callee_post callee_post_n function_table
                 (xyzt_double_body dest [P]) rs1 rs2 ->
    rs_get_tower_ed rs2 dest.(loc_var)
      = Some (exist_tval_ed (TBytes 200)
                (VBytes 200 (ed25519_xyzt_double_gallina p_bs))).
Proof.
  intros callee_post callee_post_n function_table P dest rs1 rs2 p_bs
         Htype Hp Hcontract Hexec.
  cbv [xyzt_double_body] in Hexec.
  inversion Hexec; clear Hexec; subst.
  eapply Hcontract; eauto.
Qed.

(* Print Assumptions xyzt_double_body. *)
(* Print Assumptions xyzt_double_body_correct. *)
