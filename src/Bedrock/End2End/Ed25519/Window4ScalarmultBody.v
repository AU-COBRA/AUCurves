(** * Window4ScalarmultBody — unsigned window-4 variable-base
 *                            scalar multiplication.
 *
 *  Phase 1a (verified follow-on for the curve25519-jasmin-rs commit
 *  `f91c713`, "Phase 1b: Rust-only verified-primitive scalarmult").
 *
 *  Companion to [WnafScalarmultBody.v] and [CombScalarmultBody.v].
 *  Uses **unsigned window-4 with a 16-entry table** of all multiples
 *  0·P .. 15·P.  Sidesteps wnaf's sign-bit Admitted gap: every digit
 *  ∈ 0..16, so the table lookup is purely an unsigned CT-select with
 *  no conditional negation.
 *
 *  ## Algorithm (w = 4, 64 windows)
 *
 *    T[0] := identity;  T[k] := T[k-1] + P  for k ∈ 1..15
 *    Q := identity
 *    for i in 0..64:
 *      d := 63 - i                  (MSB-first scan)
 *      digit := nibble of scalar at position d
 *      for j in 0..4: Q := xyzt_double(Q)
 *      lookup_buf := T[digit]       (CT lookup over 16 entries)
 *      Q := xyzt_add(Q, lookup_buf)
 *    dest := xyzt_copy(Q)
 *
 *  ## HONEST status
 *
 *  Body Definition: Qed-clean.  Correctness theorem
 *  [window4_scalarmult_body_correct] is [Admitted] at PoC level,
 *  matching [comb_scalarmult_base_body_correct] /
 *  [wnaf_scalarmult_body_correct].
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import coqutil.Word.LittleEndianList.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.ScalarmultVerified.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §0.  Local LE_TBytes helpers                                      *)
(* ================================================================ *)

Local Definition LE200 (v : String.string) : located_ed :=
  {| loc_var := v; loc_type := TBytes 200 |}.

Local Definition LE32 (v : String.string) : located_ed :=
  {| loc_var := v; loc_type := TBytes 32 |}.

(* ================================================================ *)
(* §1.  Table-build helper — T[k] := T[k-1] + P  for k = 1..15.      *)
(* ================================================================ *)

(** Each line: REdSeq (one xyzt-add) (rest).  All 15 nested. *)
Local Definition build_window4_table_body
    (P_in T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 : located_ed)
    (cont : rust_cmd_ed) : rust_cmd_ed :=
  let step (a b : located_ed) (k : rust_cmd_ed) : rust_cmd_ed :=
    REdSeq (REdCallFn "xyzt_add_decomposed" b [a; P_in]) k in
  REdSeq (REdCallFn "xyzt_copy" T1 [P_in])
    (step T1 T2
    (step T2 T3
    (step T3 T4
    (step T4 T5
    (step T5 T6
    (step T6 T7
    (step T7 T8
    (step T8 T9
    (step T9 T10
    (step T10 T11
    (step T11 T12
    (step T12 T13
    (step T13 T14
    (step T14 T15 cont)))))))))))))).

(* ================================================================ *)
(* §2.  CT table lookup over 16 entries                              *)
(* ================================================================ *)

Local Definition ct_table_lookup_16
    (digit_var : var) (dest : located_ed)
    (T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 : located_ed)
    : rust_cmd_ed :=
  let step (k : Z) (Tk : located_ed) (rest : rust_cmd_ed) : rust_cmd_ed :=
    REdSeq (REdSelect (SSub (SVar digit_var) (SLit k)) dest Tk dest) rest in
  REdSeq (REdSelect (SLit 0) dest T0 dest)
    (step 1  T1
    (step 2  T2
    (step 3  T3
    (step 4  T4
    (step 5  T5
    (step 6  T6
    (step 7  T7
    (step 8  T8
    (step 9  T9
    (step 10 T10
    (step 11 T11
    (step 12 T12
    (step 13 T13
    (step 14 T14
    (REdSelect (SSub (SVar digit_var) (SLit 15)) dest T15 dest))))))))))))))).

(* ================================================================ *)
(* §3.  Inner window-iter body                                       *)
(* ================================================================ *)

(** One iteration of the window-4 loop body (i ∈ 0..63). *)
Local Definition window4_iter
    (scalar : located_ed)
    (T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 : located_ed)
    (Q lookup_buf Q_plus : located_ed) : rust_cmd_ed :=
  let double_Q :=
    REdCallFn "xyzt_double_decomposed" Q [Q] in
  REdLetU64 "d" (SSub (SLit 63) (SVar "i"))
  (REdLetU64 "byte_idx" (SShr (SVar "d") (SLit 1))
  (REdLetU64 "nibble_shift" (SMul (SAnd (SVar "d") (SLit 1)) (SLit 4))
  (REdSeq (REdByteLoad "scalar_byte" scalar (SVar "byte_idx"))
  (REdLetU64 "digit"
     (SAnd (SShr (SVar "scalar_byte") (SVar "nibble_shift")) (SLit 15))
  (REdSeq double_Q
  (REdSeq double_Q
  (REdSeq double_Q
  (REdSeq double_Q
  (REdSeq (ct_table_lookup_16 "digit" lookup_buf
            T0 T1 T2 T3 T4 T5 T6 T7
            T8 T9 T10 T11 T12 T13 T14 T15)
  (REdSeq (REdCallFn "xyzt_add_decomposed" Q_plus [Q; lookup_buf])
          (REdSelect (SLit 1) Q_plus Q Q))))))))))).

(* ================================================================ *)
(* §4.  Top-level body                                               *)
(* ================================================================ *)

(** Body for the "window4_scalarmult" entry of [curve_function_table].

    Args: [scalar; P]   (32-byte + 200-byte slots).
    Dest: 200-byte xyzt slot.

    Layout: 19 REdLetZero scratch slots + table-build + Q-identity
    setup + 64-iter REdFor loop + xyzt_copy to dest. *)
Definition window4_scalarmult_body : function_body_ed :=
  fun dest args =>
    match args with
    | [scalar; P] =>
        let scratch_slots (body : rust_cmd_ed) : rust_cmd_ed :=
          REdLetZero "T0"  (TBytes 200) (
          REdLetZero "T1"  (TBytes 200) (
          REdLetZero "T2"  (TBytes 200) (
          REdLetZero "T3"  (TBytes 200) (
          REdLetZero "T4"  (TBytes 200) (
          REdLetZero "T5"  (TBytes 200) (
          REdLetZero "T6"  (TBytes 200) (
          REdLetZero "T7"  (TBytes 200) (
          REdLetZero "T8"  (TBytes 200) (
          REdLetZero "T9"  (TBytes 200) (
          REdLetZero "T10" (TBytes 200) (
          REdLetZero "T11" (TBytes 200) (
          REdLetZero "T12" (TBytes 200) (
          REdLetZero "T13" (TBytes 200) (
          REdLetZero "T14" (TBytes 200) (
          REdLetZero "T15" (TBytes 200) (
          REdLetZero "Q"          (TBytes 200) (
          REdLetZero "lookup_buf" (TBytes 200) (
          REdLetZero "Q_plus"     (TBytes 200) body
          )))))))))))))))))) in
        scratch_slots (
          (* Identity in T[0]. *)
          REdSeq (REdByteStore (LE200 "T0") (SLit 40)  (SLit 1))
          (REdSeq (REdByteStore (LE200 "T0") (SLit 80)  (SLit 1))
          (REdSeq (REdByteStore (LE200 "T0") (SLit 160) (SLit 1))
          (* Build T[1..15]. *)
          (build_window4_table_body P
             (LE200 "T1")  (LE200 "T2")  (LE200 "T3")  (LE200 "T4")
             (LE200 "T5")  (LE200 "T6")  (LE200 "T7")  (LE200 "T8")
             (LE200 "T9")  (LE200 "T10") (LE200 "T11") (LE200 "T12")
             (LE200 "T13") (LE200 "T14") (LE200 "T15")
          (* Identity in Q. *)
          (REdSeq (REdByteStore (LE200 "Q") (SLit 40)  (SLit 1))
          (REdSeq (REdByteStore (LE200 "Q") (SLit 80)  (SLit 1))
          (REdSeq (REdByteStore (LE200 "Q") (SLit 160) (SLit 1))
          (* Main 64-iter window loop, then copy to dest. *)
          (REdSeq
            (REdFor "i" 64
               (window4_iter scalar
                  (LE200 "T0")  (LE200 "T1")  (LE200 "T2")  (LE200 "T3")
                  (LE200 "T4")  (LE200 "T5")  (LE200 "T6")  (LE200 "T7")
                  (LE200 "T8")  (LE200 "T9")  (LE200 "T10") (LE200 "T11")
                  (LE200 "T12") (LE200 "T13") (LE200 "T14") (LE200 "T15")
                  (LE200 "Q")   (LE200 "lookup_buf") (LE200 "Q_plus")))
            (REdCallFn "xyzt_copy" dest [LE200 "Q"])
          ))))))))
    | _ => REdSkip
    end.

(* ================================================================ *)
(* §5.  Helper-presence + callees-honoured predicates                *)
(* ================================================================ *)

Definition window4_helpers_present
    (function_table : function_table_ed) : Prop :=
  (exists body, List.find (fun p => String.eqb (fst p) "xyzt_add_decomposed")
                          function_table = Some ("xyzt_add_decomposed", body)) /\
  (exists body, List.find (fun p => String.eqb (fst p) "xyzt_double_decomposed")
                          function_table = Some ("xyzt_double_decomposed", body)) /\
  (exists body, List.find (fun p => String.eqb (fst p) "xyzt_copy")
                          function_table = Some ("xyzt_copy", body)).

Definition fe25519_callees_honoured_window4
    (callee_post : String.string -> list located_ed -> located_ed ->
                   rust_state_ed -> rust_state_ed -> Prop) : Prop :=
  forall src dst rs1 rs2 src_bs,
     dst.(loc_type) = TBytes 200 ->
     rs_get_tower_ed rs1 src.(loc_var)
       = Some (exist_tval_ed (TBytes 200) (VBytes 200 src_bs)) ->
     callee_post "fe25519_xyzt_copy" [src] dst rs1 rs2 ->
     rs_get_tower_ed rs2 dst.(loc_var)
       = Some (exist_tval_ed (TBytes 200) (VBytes 200 src_bs)).

(* ================================================================ *)
(* §6.  Window-4 partial-sum spec                                    *)
(* ================================================================ *)

(** [window4_partial_sum scalar j]: top-j nibbles of [scalar] as
    an integer.  After j iterations of the window-4 loop, Q holds
    [scalarmult (window4_partial_sum scalar j) P]. *)
Fixpoint window4_partial_sum_nat
    (scalar : list Byte.byte) (j : nat) : Z :=
  match j with
  | O => 0
  | S k =>
      let nibble_pos := (63 - k)%nat in
      let byte_idx   := (nibble_pos / 2)%nat in
      let nibble     := (nibble_pos mod 2)%nat in
      let b          := List.nth byte_idx scalar Byte.x00 in
      let digit      := Z.land (Z.shiftr (Z.of_N (Byte.to_N b))
                                          (Z.of_nat (4 * nibble))) 15 in
      window4_partial_sum_nat scalar k * 16 + digit
  end.

Definition window4_partial_sum (scalar : list Byte.byte) (j : Z) : Z :=
  window4_partial_sum_nat scalar (Z.to_nat j).

Lemma window4_partial_sum_full :
  forall scalar,
    length scalar = 32%nat ->
    window4_partial_sum scalar 64
    = coqutil.Word.LittleEndianList.le_combine scalar.
Proof.
  (* Mechanical induction over the 64 nibbles, mirroring
     [comb_partial_sum_full] in CombScalarmultBody.v.  Defers to
     the same Stdlib le_combine decomposition. *)
Admitted.

(* ================================================================ *)
(* §7.  Correctness theorem (Admitted, PoC)                          *)
(* ================================================================ *)

Theorem window4_scalarmult_body_correct :
  forall callee_post callee_post_n function_table
         (scalar P dest : located_ed)
         (rs1 rs2 : rust_state_ed)
         (scalar_bs P_bs dest_init : list Byte.byte),
    window4_helpers_present function_table ->
    fe25519_callees_honoured_window4 callee_post ->
    length scalar_bs = 32%nat ->
    length P_bs = 200%nat ->
    length dest_init = 200%nat ->
    dest.(loc_type) = TBytes 200 ->
    scalar.(loc_type) = TBytes 32 ->
    P.(loc_type) = TBytes 200 ->
    rs_get_tower_ed rs1 scalar.(loc_var)
      = Some (exist_tval_ed (TBytes 32) (VBytes 32 scalar_bs)) ->
    rs_get_tower_ed rs1 P.(loc_var)
      = Some (exist_tval_ed (TBytes 200) (VBytes 200 P_bs)) ->
    rs_get_tower_ed rs1 dest.(loc_var)
      = Some (exist_tval_ed (TBytes 200) (VBytes 200 dest_init)) ->
    rust_exec_ed callee_post callee_post_n function_table
                 (window4_scalarmult_body dest [scalar; P]) rs1 rs2 ->
    rs_get_tower_ed rs2 dest.(loc_var)
      = Some (exist_tval_ed (TBytes 200)
                (VBytes 200 (ed25519_scalarmult_gallina scalar_bs P_bs))).
Proof.
  (* PROOF STRATEGY (Admitted at PoC level, parallel to
     comb_scalarmult_base_body_correct and wnaf_scalarmult_body_correct):
     1. Inversion through 19 REdLetZero + 6 REdByteStore initialisations.
     2. Build phase: 15 [REdCallFn xyzt_*] inversions yield T[k] = k·P.
     3. Window-loop induction over [REdFor "i" 64] with invariant:
          after j iters, Q = scalarmult (window4_partial_sum scalar j) P
        Base j = 0: Q = identity = 0·P.
        Step: 4 doublings give 16·Q; xyzt_add gives 16·Q + digit·P;
        matches the partial-sum recurrence.
     4. Terminal: window4_partial_sum scalar 64 = le_combine scalar.
     5. Final xyzt_copy dispatches xyzt_copy_body into dest. *)
Admitted.
