(** * CalculateKeyPairBody — verified [function_body_ed] forwarders
 *                           for the Edwards signing-key derivation
 *                           leaves (a and A variants).
 *
 *  Phase 5 of the curve-leaf verification plan; companion to
 *  [CalculateKeyPairVerified.v].  Two variants:
 *
 *    - [calculate_key_pair_a_body] : 32-byte secret seed → 32-byte
 *      signing scalar [a].
 *    - [calculate_key_pair_A_body] : 32-byte secret seed → 32-byte
 *      compressed public key [A] with sign forced to 0.
 *
 *  Both forward to a single [REdCall] to the corresponding external
 *  leaf.  The granular bedrock2-level decomposition lives in
 *  [Sign_Strong_Correctness_VerifiedClamp.v] for a, and at the
 *  bedrock2 layer for A — neither is duplicated here.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.CalculateKeyPairVerified.
Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* §1.  Verified rust_cmd_ed bodies                                  *)
(* ================================================================ *)

(** Body for the "calculate_key_pair_a" entry. *)
Definition calculate_key_pair_a_body : function_body_ed :=
  fun dest args =>
    match args with
    | [k] => REdCall "fe25519_calculate_key_pair_a" dest [k]
    | _   => REdSkip
    end.

(** Body for the "calculate_key_pair_A" entry. *)
Definition calculate_key_pair_A_body : function_body_ed :=
  fun dest args =>
    match args with
    | [k] => REdCall "fe25519_calculate_key_pair_A" dest [k]
    | _   => REdSkip
    end.

(* ================================================================ *)
(* §2.  Correctness                                                  *)
(* ================================================================ *)

Definition calculate_key_pair_a_callee_post_honoured
    (callee_post :
       String.string -> list located_ed -> located_ed ->
       rust_state_ed -> rust_state_ed -> Prop)
    (k dest : located_ed) : Prop :=
  forall (rs1 rs2 : rust_state_ed) (k_bs : list Byte.byte),
    dest.(loc_type) = TBytes 32 ->
    rs_get_tower_ed rs1 k.(loc_var)
      = Some (exist_tval_ed (TBytes 32) (VBytes 32 k_bs)) ->
    callee_post "fe25519_calculate_key_pair_a" [k] dest rs1 rs2 ->
    rs_get_tower_ed rs2 dest.(loc_var)
      = Some (exist_tval_ed (TBytes 32)
                (VBytes 32 (calculate_key_pair_a_spec k_bs))).

Definition calculate_key_pair_A_callee_post_honoured
    (callee_post :
       String.string -> list located_ed -> located_ed ->
       rust_state_ed -> rust_state_ed -> Prop)
    (k dest : located_ed) : Prop :=
  forall (rs1 rs2 : rust_state_ed) (k_bs : list Byte.byte),
    dest.(loc_type) = TBytes 32 ->
    rs_get_tower_ed rs1 k.(loc_var)
      = Some (exist_tval_ed (TBytes 32) (VBytes 32 k_bs)) ->
    callee_post "fe25519_calculate_key_pair_A" [k] dest rs1 rs2 ->
    rs_get_tower_ed rs2 dest.(loc_var)
      = Some (exist_tval_ed (TBytes 32)
                (VBytes 32 (calculate_key_pair_A_spec k_bs))).

Theorem calculate_key_pair_a_body_correct :
  forall callee_post callee_post_n function_table
         (k dest : located_ed)
         (rs1 rs2 : rust_state_ed)
         (k_bs : list Byte.byte),
    dest.(loc_type) = TBytes 32 ->
    rs_get_tower_ed rs1 k.(loc_var)
      = Some (exist_tval_ed (TBytes 32) (VBytes 32 k_bs)) ->
    calculate_key_pair_a_callee_post_honoured callee_post k dest ->
    rust_exec_ed callee_post callee_post_n function_table
                 (calculate_key_pair_a_body dest [k]) rs1 rs2 ->
    rs_get_tower_ed rs2 dest.(loc_var)
      = Some (exist_tval_ed (TBytes 32)
                (VBytes 32 (calculate_key_pair_a_spec k_bs))).
Proof.
  intros callee_post callee_post_n function_table k dest rs1 rs2 k_bs
         Htype Hk Hcontract Hexec.
  cbv [calculate_key_pair_a_body] in Hexec.
  inversion Hexec; clear Hexec; subst.
  eapply Hcontract; eauto.
Qed.

Theorem calculate_key_pair_A_body_correct :
  forall callee_post callee_post_n function_table
         (k dest : located_ed)
         (rs1 rs2 : rust_state_ed)
         (k_bs : list Byte.byte),
    dest.(loc_type) = TBytes 32 ->
    rs_get_tower_ed rs1 k.(loc_var)
      = Some (exist_tval_ed (TBytes 32) (VBytes 32 k_bs)) ->
    calculate_key_pair_A_callee_post_honoured callee_post k dest ->
    rust_exec_ed callee_post callee_post_n function_table
                 (calculate_key_pair_A_body dest [k]) rs1 rs2 ->
    rs_get_tower_ed rs2 dest.(loc_var)
      = Some (exist_tval_ed (TBytes 32)
                (VBytes 32 (calculate_key_pair_A_spec k_bs))).
Proof.
  intros callee_post callee_post_n function_table k dest rs1 rs2 k_bs
         Htype Hk Hcontract Hexec.
  cbv [calculate_key_pair_A_body] in Hexec.
  inversion Hexec; clear Hexec; subst.
  eapply Hcontract; eauto.
Qed.

(* Print Assumptions calculate_key_pair_a_body_correct. *)
(* Print Assumptions calculate_key_pair_A_body_correct. *)
