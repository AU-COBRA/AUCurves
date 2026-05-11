(** * ScalarmultBody — verified [function_body_ed] forwarder for the
 *                     variable-base scalar-multiplication leaf.
 *
 *  Phase 4 of the curve-leaf verification plan; companion to
 *  [ScalarmultVerified.v].  Forwards [REdCallFn] dispatch to the
 *  external "fe25519_scalarmult" leaf.  The granular decomposition
 *  into the per-bit double/add loop (a la [Scalarmult_Impl_RustCmd.v])
 *  is multi-week future work; the body here closes the
 *  framework-level dispatch obligation and unblocks consumers.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.ScalarmultVerified.
Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* §1.  Verified rust_cmd_ed body                                    *)
(* ================================================================ *)

(** Body for the "scalarmult" entry of the curve-level
    [function_table_ed].

    Surface: two [located_ed] arguments [scalar; P], one destination
    [dest] (scalar is a 32-byte slot, P and dest are 200-byte projective
    xyzt slots). *)
Definition scalarmult_body : function_body_ed :=
  fun dest args =>
    match args with
    | [scalar; P] => REdCall "fe25519_scalarmult" dest [scalar; P]
    | _           => REdSkip
    end.

(* ================================================================ *)
(* §2.  Correctness                                                  *)
(* ================================================================ *)

Definition scalarmult_callee_post_honoured
    (callee_post :
       String.string -> list located_ed -> located_ed ->
       rust_state_ed -> rust_state_ed -> Prop)
    (scalar P dest : located_ed) : Prop :=
  forall (rs1 rs2 : rust_state_ed) (scalar_bs p_bs : list Byte.byte),
    dest.(loc_type) = TBytes 200 ->
    rs_get_tower_ed rs1 scalar.(loc_var)
      = Some (exist_tval_ed (TBytes 32) (VBytes 32 scalar_bs)) ->
    rs_get_tower_ed rs1 P.(loc_var)
      = Some (exist_tval_ed (TBytes 200) (VBytes 200 p_bs)) ->
    callee_post "fe25519_scalarmult" [scalar; P] dest rs1 rs2 ->
    rs_get_tower_ed rs2 dest.(loc_var)
      = Some (exist_tval_ed (TBytes 200)
                (VBytes 200 (ed25519_scalarmult_gallina scalar_bs p_bs))).

Theorem scalarmult_body_correct :
  forall callee_post callee_post_n function_table
         (scalar P dest : located_ed)
         (rs1 rs2 : rust_state_ed)
         (scalar_bs p_bs : list Byte.byte),
    dest.(loc_type) = TBytes 200 ->
    rs_get_tower_ed rs1 scalar.(loc_var)
      = Some (exist_tval_ed (TBytes 32) (VBytes 32 scalar_bs)) ->
    rs_get_tower_ed rs1 P.(loc_var)
      = Some (exist_tval_ed (TBytes 200) (VBytes 200 p_bs)) ->
    scalarmult_callee_post_honoured callee_post scalar P dest ->
    rust_exec_ed callee_post callee_post_n function_table
                 (scalarmult_body dest [scalar; P]) rs1 rs2 ->
    rs_get_tower_ed rs2 dest.(loc_var)
      = Some (exist_tval_ed (TBytes 200)
                (VBytes 200 (ed25519_scalarmult_gallina scalar_bs p_bs))).
Proof.
  intros callee_post callee_post_n function_table scalar P dest rs1 rs2
         scalar_bs p_bs Htype Hs Hp Hcontract Hexec.
  cbv [scalarmult_body] in Hexec.
  inversion Hexec; clear Hexec; subst.
  eapply Hcontract; eauto.
Qed.

(* Print Assumptions scalarmult_body. *)
(* Print Assumptions scalarmult_body_correct. *)
