(** * XyztAddBody — verified [function_body_ed] forwarder for the
 *                  extended-twisted-Edwards point addition leaf.
 *
 *  Phase 3 of the curve-leaf verification plan (companion to
 *  Phase 1's [XyztAddVerified.v]):
 *
 *    §1  [xyzt_add_body : function_body_ed]
 *        — single-instruction [REdCall] that forwards the dispatch to
 *          the external "fe25519_xyzt_add" oracle.  The body matches
 *          the [REdCallFn] surface so [function_table_ed] dispatch can
 *          name it.  Decomposing into field-op-level
 *          [REdCall]s is multi-week future work; this body
 *          discharges the framework obligation today.
 *
 *    §2  [xyzt_add_body_correct]
 *        — given that [callee_post] honours the "fe25519_xyzt_add"
 *          contract (output slot becomes
 *          [VBytes 200 (ed25519_xyzt_add_gallina P Q)]), the
 *          [rust_exec_ed] derivation produces the expected slot.
 *          Qed-clean, no axiom dependency.
 *
 *  Mirrors [Clamp64Verified.v]'s body / body_correct shape, but with a
 *  single [REdCall] step instead of four byte-load/byte-store ops.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.XyztAddVerified.
Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* §1.  Verified rust_cmd_ed body                                    *)
(* ================================================================ *)

(** Body for the "xyzt_add" entry of the curve-level
    [function_table_ed].

    Surface: two [located_ed] arguments [P; Q], one destination [dest]
    (all 200-byte projective xyzt slots).  Forwarded to a single
    [REdCall] to the external "fe25519_xyzt_add" leaf.

    The body is exactly the function table dispatch from
    [Sign_Verify_RustCmd.v]: the framework's [REdCallFn] semantics
    inlines this body, producing the same observable behaviour as the
    direct [REdCall].

    On unexpected arity (args.length ≠ 2), the body collapses to
    [REdSkip] — defensive; never hit on well-typed sites. *)
Definition xyzt_add_body : function_body_ed :=
  fun dest args =>
    match args with
    | [P; Q] => REdCall "fe25519_xyzt_add" dest [P; Q]
    | _      => REdSkip
    end.

(* ================================================================ *)
(* §2.  Correctness                                                  *)
(* ================================================================ *)

(** Predicate: [callee_post] honours the "fe25519_xyzt_add" contract.
    Quantified over rs1/rs2 because the framework's callee_post is a
    relation; we only constrain the case where the named leaf is
    invoked. *)
Definition xyzt_add_callee_post_honoured
    (callee_post :
       String.string -> list located_ed -> located_ed ->
       rust_state_ed -> rust_state_ed -> Prop)
    (P Q dest : located_ed) : Prop :=
  forall (rs1 rs2 : rust_state_ed) (p_bs q_bs : list Byte.byte),
    dest.(loc_type) = TBytes 200 ->
    rs_get_tower_ed rs1 P.(loc_var)
      = Some (exist_tval_ed (TBytes 200) (VBytes 200 p_bs)) ->
    rs_get_tower_ed rs1 Q.(loc_var)
      = Some (exist_tval_ed (TBytes 200) (VBytes 200 q_bs)) ->
    callee_post "fe25519_xyzt_add" [P; Q] dest rs1 rs2 ->
    rs_get_tower_ed rs2 dest.(loc_var)
      = Some (exist_tval_ed (TBytes 200)
                (VBytes 200 (ed25519_xyzt_add_gallina p_bs q_bs))).

(** Main correctness theorem. *)
Theorem xyzt_add_body_correct :
  forall callee_post callee_post_n function_table
         (P Q dest : located_ed)
         (rs1 rs2 : rust_state_ed)
         (p_bs q_bs : list Byte.byte),
    dest.(loc_type) = TBytes 200 ->
    rs_get_tower_ed rs1 P.(loc_var)
      = Some (exist_tval_ed (TBytes 200) (VBytes 200 p_bs)) ->
    rs_get_tower_ed rs1 Q.(loc_var)
      = Some (exist_tval_ed (TBytes 200) (VBytes 200 q_bs)) ->
    xyzt_add_callee_post_honoured callee_post P Q dest ->
    rust_exec_ed callee_post callee_post_n function_table
                 (xyzt_add_body dest [P; Q]) rs1 rs2 ->
    rs_get_tower_ed rs2 dest.(loc_var)
      = Some (exist_tval_ed (TBytes 200)
                (VBytes 200 (ed25519_xyzt_add_gallina p_bs q_bs))).
Proof.
  intros callee_post callee_post_n function_table P Q dest rs1 rs2 p_bs q_bs
         Htype Hp Hq Hcontract Hexec.
  cbv [xyzt_add_body] in Hexec.
  inversion Hexec; clear Hexec; subst.
  eapply Hcontract; eauto.
Qed.

(* ================================================================ *)
(* §3.  Print-assumptions guard                                      *)
(* ================================================================ *)

(** Both should report [Closed under the global context]. *)
(* Print Assumptions xyzt_add_body. *)
(* Print Assumptions xyzt_add_body_correct. *)
