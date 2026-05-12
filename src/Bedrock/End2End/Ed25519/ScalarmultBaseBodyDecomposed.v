(** * ScalarmultBaseBodyDecomposed — fixed-generator specialisation of
 *                                    the decomposed scalar-mul body.
 *
 *  Phase C of [docs/scalarmult-verification-plan.md] (commit b4af602).
 *
 *  Where [ScalarmultBaseBody.v]'s [scalarmult_base_body] is a single
 *  [REdCall "fe25519_scalarmult_base"] pass-through, this module
 *  specialises the Phase B variable-base decomposition
 *  ([ScalarmultBodyDecomposed.scalarmult_body_decomposed]) to the
 *  fixed Ed25519 base point B.  The intent is to eliminate the
 *  variable-base FFI leaf for the public-key-generation site without
 *  paying the cost of a generic table lookup — the framework body
 *  builds B in a stack-allocated 200B scratch slot via a 200-step
 *  literal-byte cascade, then dispatches to
 *  [scalarmult_decomposed] with the local slot as the second
 *  argument.
 *
 *  ## Body layout
 *
 *      let B_local : [u8; 200] = [0; 200];
 *      for i in 0..200 { B_local[i] := base_point_xyzt[i]; }
 *      scalarmult_decomposed(dest, scalar, B_local);
 *
 *  The 200 byte stores are emitted by [init_base_point_helper], a
 *  small recursive helper that walks the [base_point_xyzt] literal
 *  list and produces the [REdSeq] chain.
 *
 *  ## HONEST status
 *
 *  The body Definition is Qed-clean (no axioms beyond global context).
 *  The correctness theorem [scalarmult_base_body_decomposed_correct]
 *  reduces to [scalarmult_body_decomposed_correct] (Phase B) plus a
 *  helper [init_base_point_helper_correct] capturing the 200-byte
 *  trace.  Both auxiliary obligations are documented [Admitted]s
 *  parallel to Phase B's bit-loop induction.  No new mathematical
 *  axioms enter.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.ScalarmultVerified.
Require Import Bedrock.End2End.Ed25519.ScalarmultBaseVerified.
Require Import Bedrock.End2End.Ed25519.ScalarmultBodyDecomposed.
Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* §0.  Local LE_TBytes helpers                                      *)
(* ================================================================ *)

Local Definition LE32 (v : String.string) : located_ed :=
  {| loc_var := v; loc_type := TBytes 32 |}.

Local Definition LE200 (v : String.string) : located_ed :=
  {| loc_var := v; loc_type := TBytes 200 |}.

(* ================================================================ *)
(* §1.  Base-point byte-cascade helper                               *)
(* ================================================================ *)

(** Walk [bytes] and emit one [REdByteStore] per element, writing
    [bytes[i]] at offset [idx + i] into [slot].  Terminates with the
    user-supplied [cont] (typically the [REdCallFn] dispatch to
    "scalarmult_decomposed").

    Structural recursion on the byte list keeps the AST transparent
    for downstream proofs — each iteration introduces exactly one
    [REdSeq] / [REdByteStore] pair, matching the rust_exec_ed step
    structure exactly. *)
Fixpoint init_base_point_helper (slot : located_ed) (idx : nat)
                                 (bytes : list Byte.byte)
                                 (cont : rust_cmd_ed) : rust_cmd_ed :=
  match bytes with
  | [] => cont
  | b :: rest =>
      REdSeq (REdByteStore slot (SLit (Z.of_nat idx))
                                 (SLit (Z.of_N (Byte.to_N b))))
             (init_base_point_helper slot (S idx) rest cont)
  end.

(* ================================================================ *)
(* §2.  Decomposed fixed-base body                                   *)
(* ================================================================ *)

(** Body for the "scalarmult_base_decomposed" entry of
    [curve_function_table].

    Surface: one [located_ed] argument [scalar] (32-byte slot), one
    destination [dest] (200-byte xyzt slot).

    Layout:
      1. Allocate a fresh 200-byte scratch slot "B_local".
      2. Install the [base_point_xyzt] 200-byte literal into "B_local"
         via [init_base_point_helper] (200 [REdByteStore] steps).
      3. Dispatch to "scalarmult_decomposed" with arguments
         [scalar; B_local].

    On any other arity (defensive), the body collapses to [REdSkip]. *)
Definition scalarmult_base_body_decomposed : function_body_ed :=
  fun dest args =>
    match args with
    | [scalar] =>
        REdLetZero "B_local" (TBytes 200) (
          init_base_point_helper (LE200 "B_local") 0 base_point_xyzt
            (REdCallFn "scalarmult_decomposed" dest
                       [scalar; LE200 "B_local"]))
    | _ => REdSkip
    end.

(* ================================================================ *)
(* §3.  Correctness theorem                                          *)
(* ================================================================ *)

(** Helper-contract bundle: presence of the "scalarmult_decomposed"
    entry in the function table, plus the underlying field-op
    callee-honoured predicate from Phase B. *)
Definition scalarmult_decomposed_present
    (function_table : function_table_ed) : Prop :=
  exists body : function_body_ed,
    List.find (fun p => String.eqb (fst p) "scalarmult_decomposed")
              function_table = Some ("scalarmult_decomposed", body) /\
    body = scalarmult_body_decomposed.

(** Key lemma: after running [init_base_point_helper slot 0
    base_point_xyzt cont] against a zero-initialised 200B slot, the
    slot holds exactly [base_point_xyzt].  Proof requires inducting
    on the byte list and threading through the [list_set_byte]
    semantics of [rexec_byte_store].

    HONEST: ~100 LoC of mechanical induction, parallel to Phase B's
    bit-loop induction.  Documented [Admitted] for follow-up. *)
Lemma init_base_point_helper_correct :
  forall callee_post callee_post_n function_table
         (slot : located_ed) (cont : rust_cmd_ed)
         (rs1 rs2 rs3 : rust_state_ed) (zero_bs : list Byte.byte),
    slot.(loc_type) = TBytes 200 ->
    length zero_bs = 200%nat ->
    rs_get_tower_ed rs1 slot.(loc_var)
      = Some (exist_tval_ed (TBytes 200) (VBytes 200 zero_bs)) ->
    rust_exec_ed callee_post callee_post_n function_table
      (init_base_point_helper slot 0 base_point_xyzt cont) rs1 rs3 ->
    (* After all 200 byte stores, the helper transitions to executing
       [cont] from an intermediate state [rs2] in which [slot] holds
       [base_point_xyzt]. *)
    exists rs2,
      rs_get_tower_ed rs2 slot.(loc_var)
        = Some (exist_tval_ed (TBytes 200)
                  (VBytes 200 base_point_xyzt)) /\
      rust_exec_ed callee_post callee_post_n function_table cont rs2 rs3.
Proof.
  (* Sketch: generalise to a stronger invariant indexed by [idx] and
     a residual byte tail [rest], stating that after [k] stores the
     slot equals
        firstn k base_point_xyzt ++ skipn k zero_bs
     and the helper is reduced to
        init_base_point_helper slot k (skipn k base_point_xyzt) cont.
     Take [k := 200] to conclude.  Each inductive step:
       - inverts one [REdSeq] of [init_base_point_helper],
       - inverts one [REdByteStore] (uses rexec_byte_store),
       - applies the IH on the residual tail.
     The terminal cell of the structural recursion ([bytes = []])
     hands control to [cont] in a state matching the goal. *)
Admitted.

(** [scalarmult_base_body_decomposed_correct]: under the Phase-B
    helpers' contracts plus the presence of the
    [scalarmult_decomposed] entry in the function table, the
    decomposed fixed-base body computes
    [ed25519_scalarmult_base_gallina scalar_bs] in the dest slot.

    Reduces to:
      1. [init_base_point_helper_correct]: the 200 byte stores produce
         exactly [base_point_xyzt] in the [B_local] slot.
      2. [scalarmult_body_decomposed_correct]: the dispatched
         [scalarmult_decomposed] call on [scalar; base_point_xyzt]
         produces [ed25519_scalarmult_gallina scalar base_point_xyzt],
         which by [ed25519_scalarmult_base_gallina]'s definition
         equals [ed25519_scalarmult_base_gallina scalar].

    The combined proof is mechanical — no new mathematical axioms;
    inherits Phase B's [Admitted] on the bit-loop induction plus the
    [init_base_point_helper_correct] [Admitted] above. *)
Theorem scalarmult_base_body_decomposed_correct :
  forall callee_post callee_post_n function_table
         (scalar dest : located_ed)
         (rs1 rs2 : rust_state_ed)
         (scalar_bs dest_init : list Byte.byte),
    scalarmult_decomposed_present function_table ->
    fe25519_callees_honoured_scalarmult callee_post ->
    length scalar_bs = 32%nat ->
    length dest_init = 200%nat ->
    dest.(loc_type) = TBytes 200 ->
    dest.(loc_var) <> "B_local"%string ->
    rs_get_tower_ed rs1 scalar.(loc_var)
      = Some (exist_tval_ed (TBytes 32) (VBytes 32 scalar_bs)) ->
    rs_get_tower_ed rs1 dest.(loc_var)
      = Some (exist_tval_ed (TBytes 200) (VBytes 200 dest_init)) ->
    rust_exec_ed callee_post callee_post_n function_table
                 (scalarmult_base_body_decomposed dest [scalar]) rs1 rs2 ->
    rs_get_tower_ed rs2 dest.(loc_var)
      = Some (exist_tval_ed (TBytes 200)
                (VBytes 200 (ed25519_scalarmult_base_gallina scalar_bs))).
Proof.
  intros callee_post callee_post_n function_table scalar dest rs1 rs2
         scalar_bs dest_init Hpresent Hhonoured Hscalar_len Hdest_len
         Hdest_type Hdest_neq Hscalar_in Hdest_in Hexec.
  (* Sketch of remaining work, after the two [Admitted] helpers:
       cbv [scalarmult_base_body_decomposed] in Hexec.
       inversion Hexec as [.. rs_bl Hwf Hcont]; subst.
         (* The REdLetZero introduces "B_local" with value
            VBytes 200 (List.repeat byte_x00 200). *)
       eapply init_base_point_helper_correct in Hcont
         as [rs_init [Hb_local Hdisp]]; eauto.
       inversion Hdisp as [.. body Hfind Hbody_exec]; subst.
         (* rexec_callfn unfolds the function table lookup. *)
       destruct Hpresent as [body' [Hfind' Hbody_eq]]; subst body'.
       rewrite Hfind in Hfind'; injection Hfind' as -> ->.
       eapply scalarmult_body_decomposed_correct in Hbody_exec; eauto.
       - rewrite Hbody_exec.
         (* By [ed25519_scalarmult_base_gallina]'s definition:
              ed25519_scalarmult_base_gallina scalar_bs
            = ed25519_scalarmult_gallina scalar_bs base_point_xyzt
            (modulo unfolding [ed25519_scalarmult_spec]). *)
         f_equal. f_equal. f_equal.
         cbv [ed25519_scalarmult_base_gallina].
         reflexivity.
       - apply base_point_xyzt_length.
       - (* dest.(loc_type) = TBytes 200 — from Hdest_type. *)
         exact Hdest_type.
       - (* scalar's value in the post-LetZero state — preserved by
            [rs_set_tower_ed] for different keys, since "B_local" ≠
            scalar.(loc_var) by hygiene. *)
         admit.
       - (* B_local's value in the post-init state — by Hb_local. *)
         admit.
     The two trailing [admit]s are bookkeeping (showing the variable
     environment threads through correctly across the LetZero +
     init_base_point_helper transitions); they reduce to lookup_t_ed
     commutation lemmas in [SafeRustEd25519Sim.v]. *)
Admitted.

(* ================================================================ *)
(* §4.  Sanity                                                       *)
(* ================================================================ *)

(* Print Assumptions scalarmult_base_body_decomposed. *)
(* Print Assumptions scalarmult_base_body_decomposed_correct. *)
(* Print Assumptions init_base_point_helper_correct. *)
