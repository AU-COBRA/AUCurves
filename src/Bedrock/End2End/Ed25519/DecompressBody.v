(** * DecompressBody — verified [function_body_ed] forwarders for the
 *                     Edwards point decompression leaves.
 *
 *  Phase 5 of the curve-leaf verification plan; companion to
 *  [DecompressVerified.v].  Both _R and _A variants share the same
 *  body (the underlying gallina spec is identical — only the input
 *  framing differs at the call site); we expose them as two named
 *  bodies for the function_table_ed entry-point lookup.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.DecompressVerified.
Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* §1.  Verified rust_cmd_ed bodies                                  *)
(* ================================================================ *)

(** Body for "decompress_R": 64-byte signature operand → 200-byte xyzt.
    The leaf internally extracts the first 32 bytes (per the gallina
    spec's [firstn 32]). *)
Definition decompress_R_body : function_body_ed :=
  fun dest args =>
    match args with
    | [sig_in] => REdCall "fe25519_decompress_R" dest [sig_in]
    | _        => REdSkip
    end.

(** Body for "decompress_A": 32-byte compressed pubkey → 200-byte xyzt. *)
Definition decompress_A_body : function_body_ed :=
  fun dest args =>
    match args with
    | [pub] => REdCall "fe25519_decompress_A" dest [pub]
    | _     => REdSkip
    end.

(* ================================================================ *)
(* §2.  Correctness                                                  *)
(* ================================================================ *)

Definition decompress_R_callee_post_honoured
    (callee_post :
       String.string -> list located_ed -> located_ed ->
       rust_state_ed -> rust_state_ed -> Prop)
    (sig_in dest : located_ed)
    (n_in : nat) : Prop :=
  forall (rs1 rs2 : rust_state_ed) (in_bs : list Byte.byte),
    dest.(loc_type) = TBytes 200 ->
    rs_get_tower_ed rs1 sig_in.(loc_var)
      = Some (exist_tval_ed (TBytes n_in) (VBytes n_in in_bs)) ->
    callee_post "fe25519_decompress_R" [sig_in] dest rs1 rs2 ->
    rs_get_tower_ed rs2 dest.(loc_var)
      = Some (exist_tval_ed (TBytes 200)
                (VBytes 200 (ed25519_decompress_R_spec in_bs))).

Definition decompress_A_callee_post_honoured
    (callee_post :
       String.string -> list located_ed -> located_ed ->
       rust_state_ed -> rust_state_ed -> Prop)
    (pub dest : located_ed) : Prop :=
  forall (rs1 rs2 : rust_state_ed) (pub_bs : list Byte.byte),
    dest.(loc_type) = TBytes 200 ->
    rs_get_tower_ed rs1 pub.(loc_var)
      = Some (exist_tval_ed (TBytes 32) (VBytes 32 pub_bs)) ->
    callee_post "fe25519_decompress_A" [pub] dest rs1 rs2 ->
    rs_get_tower_ed rs2 dest.(loc_var)
      = Some (exist_tval_ed (TBytes 200)
                (VBytes 200 (ed25519_decompress_A_spec pub_bs))).

Theorem decompress_R_body_correct :
  forall callee_post callee_post_n function_table
         (sig_in dest : located_ed)
         (rs1 rs2 : rust_state_ed)
         (in_bs : list Byte.byte)
         (n_in : nat),
    dest.(loc_type) = TBytes 200 ->
    rs_get_tower_ed rs1 sig_in.(loc_var)
      = Some (exist_tval_ed (TBytes n_in) (VBytes n_in in_bs)) ->
    decompress_R_callee_post_honoured callee_post sig_in dest n_in ->
    rust_exec_ed callee_post callee_post_n function_table
                 (decompress_R_body dest [sig_in]) rs1 rs2 ->
    rs_get_tower_ed rs2 dest.(loc_var)
      = Some (exist_tval_ed (TBytes 200)
                (VBytes 200 (ed25519_decompress_R_spec in_bs))).
Proof.
  intros callee_post callee_post_n function_table sig_in dest rs1 rs2
         in_bs n_in Htype Hin Hcontract Hexec.
  cbv [decompress_R_body] in Hexec.
  inversion Hexec; clear Hexec; subst.
  eapply Hcontract; eauto.
Qed.

Theorem decompress_A_body_correct :
  forall callee_post callee_post_n function_table
         (pub dest : located_ed)
         (rs1 rs2 : rust_state_ed)
         (pub_bs : list Byte.byte),
    dest.(loc_type) = TBytes 200 ->
    rs_get_tower_ed rs1 pub.(loc_var)
      = Some (exist_tval_ed (TBytes 32) (VBytes 32 pub_bs)) ->
    decompress_A_callee_post_honoured callee_post pub dest ->
    rust_exec_ed callee_post callee_post_n function_table
                 (decompress_A_body dest [pub]) rs1 rs2 ->
    rs_get_tower_ed rs2 dest.(loc_var)
      = Some (exist_tval_ed (TBytes 200)
                (VBytes 200 (ed25519_decompress_A_spec pub_bs))).
Proof.
  intros callee_post callee_post_n function_table pub dest rs1 rs2
         pub_bs Htype Hin Hcontract Hexec.
  cbv [decompress_A_body] in Hexec.
  inversion Hexec; clear Hexec; subst.
  eapply Hcontract; eauto.
Qed.

(* Print Assumptions decompress_R_body_correct. *)
(* Print Assumptions decompress_A_body_correct. *)
