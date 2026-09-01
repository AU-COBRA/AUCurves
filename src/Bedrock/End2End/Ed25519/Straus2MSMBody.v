(** * Straus2MSMBody — 2-MSM via Straus's algorithm.
 *
 *  Phase 6 (rust_cmd_ed shape) of
 *  curve25519-jasmin-rs/docs/projective-boundary-plan.md.
 *
 *  Computes Q = s·B + k·A from two scalars (s, k) and two base
 *  points (B, A), using shared doublings across both scalarmults.
 *
 *  ## Algorithm (unsigned window-4, 64 windows)
 *
 *    T_B[0..15] := { 0·B, B, 2·B, …, 15·B }
 *    T_A[0..15] := { 0·A, A, 2·A, …, 15·A }
 *    Q := identity
 *    for i in 0..64:
 *      d := 63 - i                            (MSB-first scan)
 *      digit_s := nibble of s at position d   (0..15)
 *      digit_k := nibble of k at position d   (0..15)
 *      for j in 0..4: Q := xyzt_double(Q)     (shared doublings)
 *      Q := Q + T_B[digit_s]
 *      Q := Q + T_A[digit_k]
 *    dest := xyzt_copy(Q)
 *
 *  Cost: 256 shared doublings + 128 adds + 30 table-setup adds.
 *  Saves ~256 doublings vs running two independent window-4
 *  scalarmults.
 *
 *  ## HONEST status
 *
 *  Body Definition: Qed-clean.  Correctness theorem
 *  [straus_2msm_body_correct] is [Admitted] at PoC level.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import coqutil.Word.LittleEndianList.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.ScalarmultVerified.
Require Import Bedrock.End2End.Ed25519.Window4ScalarmultBody.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §0.  Local helpers                                                *)
(* ================================================================ *)

Local Definition LE200 (v : String.string) : located_ed :=
  {| loc_var := v; loc_type := TBytes 200 |}.

(** Build a 16-slot table-name list for one side (B or A). *)
Local Definition tb_names : list located_ed :=
  [LE200 "TB0";  LE200 "TB1";  LE200 "TB2";  LE200 "TB3";
   LE200 "TB4";  LE200 "TB5";  LE200 "TB6";  LE200 "TB7";
   LE200 "TB8";  LE200 "TB9";  LE200 "TB10"; LE200 "TB11";
   LE200 "TB12"; LE200 "TB13"; LE200 "TB14"; LE200 "TB15"].

Local Definition ta_names : list located_ed :=
  [LE200 "TA0";  LE200 "TA1";  LE200 "TA2";  LE200 "TA3";
   LE200 "TA4";  LE200 "TA5";  LE200 "TA6";  LE200 "TA7";
   LE200 "TA8";  LE200 "TA9";  LE200 "TA10"; LE200 "TA11";
   LE200 "TA12"; LE200 "TA13"; LE200 "TA14"; LE200 "TA15"].

(* ================================================================ *)
(* §1.  Per-iter Straus body                                         *)
(* ================================================================ *)

(** One Straus iteration body: 4 shared doubles + 2 CT-select-adds.
    Reuses [ct_table_lookup_16] from [Window4ScalarmultBody.v]. *)
Local Definition straus_iter
    (s k : located_ed)
    (TB0 TB1 TB2 TB3 TB4 TB5 TB6 TB7
     TB8 TB9 TB10 TB11 TB12 TB13 TB14 TB15 : located_ed)
    (TA0 TA1 TA2 TA3 TA4 TA5 TA6 TA7
     TA8 TA9 TA10 TA11 TA12 TA13 TA14 TA15 : located_ed)
    (Q lookup_buf Q_plus : located_ed) : rust_cmd_ed :=
  let dbl := REdCallFn "xyzt_double_decomposed" Q [Q] in
  let lookup_B := ct_table_lookup_16 "digit_s" lookup_buf
                    TB0 TB1 TB2 TB3 TB4 TB5 TB6 TB7
                    TB8 TB9 TB10 TB11 TB12 TB13 TB14 TB15 in
  let lookup_A := ct_table_lookup_16 "digit_k" lookup_buf
                    TA0 TA1 TA2 TA3 TA4 TA5 TA6 TA7
                    TA8 TA9 TA10 TA11 TA12 TA13 TA14 TA15 in
  let add_xyzt := REdCallFn "xyzt_add_decomposed" Q_plus [Q; lookup_buf] in
  let cmov_Q := REdSelect (SLit 1) Q_plus Q Q in
  REdLetU64 "d" (SSub (SLit 63) (SVar "i"))
  (REdLetU64 "byte_idx" (SShr (SVar "d") (SLit 1))
  (REdLetU64 "nibble_shift" (SMul (SAnd (SVar "d") (SLit 1)) (SLit 4))
  (REdSeq (REdByteLoad "scalar_byte_s" s (SVar "byte_idx"))
  (REdSeq (REdByteLoad "scalar_byte_k" k (SVar "byte_idx"))
  (REdLetU64 "digit_s"
     (SAnd (SShr (SVar "scalar_byte_s") (SVar "nibble_shift")) (SLit 15))
  (REdLetU64 "digit_k"
     (SAnd (SShr (SVar "scalar_byte_k") (SVar "nibble_shift")) (SLit 15))
  (REdSeq dbl
  (REdSeq dbl
  (REdSeq dbl
  (REdSeq dbl
  (REdSeq lookup_B
  (REdSeq add_xyzt
  (REdSeq cmov_Q
  (REdSeq lookup_A
  (REdSeq add_xyzt
          cmov_Q))))))))))))))).

(* ================================================================ *)
(* §2.  Identity-marker setup                                        *)
(* ================================================================ *)

(** Install Y[0] = Z[0] = Tb[0] = 1 marker bytes into a slot. *)
Local Definition install_identity (slot : located_ed) (cont : rust_cmd_ed)
    : rust_cmd_ed :=
  REdSeq (REdByteStore slot (SLit 40)  (SLit 1))
  (REdSeq (REdByteStore slot (SLit 80)  (SLit 1))
  (REdSeq (REdByteStore slot (SLit 160) (SLit 1))
          cont)).

(* ================================================================ *)
(* §3.  Top-level body                                               *)
(* ================================================================ *)

Definition straus_2msm_body : function_body_ed :=
  fun dest args =>
    match args with
    | [s; k; B; A] =>
        (* All 35 scratch slots allocated via 35 REdLetZero. *)
        REdLetZero "TB0"  (TBytes 200) (
        REdLetZero "TB1"  (TBytes 200) (
        REdLetZero "TB2"  (TBytes 200) (
        REdLetZero "TB3"  (TBytes 200) (
        REdLetZero "TB4"  (TBytes 200) (
        REdLetZero "TB5"  (TBytes 200) (
        REdLetZero "TB6"  (TBytes 200) (
        REdLetZero "TB7"  (TBytes 200) (
        REdLetZero "TB8"  (TBytes 200) (
        REdLetZero "TB9"  (TBytes 200) (
        REdLetZero "TB10" (TBytes 200) (
        REdLetZero "TB11" (TBytes 200) (
        REdLetZero "TB12" (TBytes 200) (
        REdLetZero "TB13" (TBytes 200) (
        REdLetZero "TB14" (TBytes 200) (
        REdLetZero "TB15" (TBytes 200) (
        REdLetZero "TA0"  (TBytes 200) (
        REdLetZero "TA1"  (TBytes 200) (
        REdLetZero "TA2"  (TBytes 200) (
        REdLetZero "TA3"  (TBytes 200) (
        REdLetZero "TA4"  (TBytes 200) (
        REdLetZero "TA5"  (TBytes 200) (
        REdLetZero "TA6"  (TBytes 200) (
        REdLetZero "TA7"  (TBytes 200) (
        REdLetZero "TA8"  (TBytes 200) (
        REdLetZero "TA9"  (TBytes 200) (
        REdLetZero "TA10" (TBytes 200) (
        REdLetZero "TA11" (TBytes 200) (
        REdLetZero "TA12" (TBytes 200) (
        REdLetZero "TA13" (TBytes 200) (
        REdLetZero "TA14" (TBytes 200) (
        REdLetZero "TA15" (TBytes 200) (
        REdLetZero "Q"          (TBytes 200) (
        REdLetZero "lookup_buf" (TBytes 200) (
        REdLetZero "Q_plus"     (TBytes 200)
          (install_identity (LE200 "TB0")
          (install_identity (LE200 "TA0")
          (install_identity (LE200 "Q")
          (build_window4_table_body B
             (LE200 "TB1")  (LE200 "TB2")  (LE200 "TB3")  (LE200 "TB4")
             (LE200 "TB5")  (LE200 "TB6")  (LE200 "TB7")  (LE200 "TB8")
             (LE200 "TB9")  (LE200 "TB10") (LE200 "TB11") (LE200 "TB12")
             (LE200 "TB13") (LE200 "TB14") (LE200 "TB15")
          (build_window4_table_body A
             (LE200 "TA1")  (LE200 "TA2")  (LE200 "TA3")  (LE200 "TA4")
             (LE200 "TA5")  (LE200 "TA6")  (LE200 "TA7")  (LE200 "TA8")
             (LE200 "TA9")  (LE200 "TA10") (LE200 "TA11") (LE200 "TA12")
             (LE200 "TA13") (LE200 "TA14") (LE200 "TA15")
          (REdSeq
            (REdFor "i" 64
               (straus_iter s k
                  (LE200 "TB0")  (LE200 "TB1")  (LE200 "TB2")  (LE200 "TB3")
                  (LE200 "TB4")  (LE200 "TB5")  (LE200 "TB6")  (LE200 "TB7")
                  (LE200 "TB8")  (LE200 "TB9")  (LE200 "TB10") (LE200 "TB11")
                  (LE200 "TB12") (LE200 "TB13") (LE200 "TB14") (LE200 "TB15")
                  (LE200 "TA0")  (LE200 "TA1")  (LE200 "TA2")  (LE200 "TA3")
                  (LE200 "TA4")  (LE200 "TA5")  (LE200 "TA6")  (LE200 "TA7")
                  (LE200 "TA8")  (LE200 "TA9")  (LE200 "TA10") (LE200 "TA11")
                  (LE200 "TA12") (LE200 "TA13") (LE200 "TA14") (LE200 "TA15")
                  (LE200 "Q") (LE200 "lookup_buf") (LE200 "Q_plus")))
            (REdCallFn "xyzt_copy" dest [LE200 "Q"])
          )))))
        )))))))))))))))))))))))))))))))))))
    | _ => REdSkip
    end.

(* ================================================================ *)
(* §4.  Helper-presence predicate                                    *)
(* ================================================================ *)

Definition straus_2msm_helpers_present
    (function_table : function_table_ed) : Prop :=
  (exists body, List.find (fun p => String.eqb (fst p) "xyzt_add_decomposed")
                          function_table = Some ("xyzt_add_decomposed", body)) /\
  (exists body, List.find (fun p => String.eqb (fst p) "xyzt_double_decomposed")
                          function_table = Some ("xyzt_double_decomposed", body)) /\
  (exists body, List.find (fun p => String.eqb (fst p) "xyzt_copy")
                          function_table = Some ("xyzt_copy", body)).

(* ================================================================ *)
(* §5.  Correctness theorem (Admitted, PoC)                          *)
(* ================================================================ *)

(** [straus_2msm_body_correct] -- REMOVED.  It was not a theorem.

    What stood here was a [Theorem] whose conclusion, after eight
    hypotheses about helper presence and byte lengths, was [True],
    closed by [Proof. trivial. Qed.].  It established nothing, and
    because it was Qed rather than Admitted it did not appear in any
    admit count -- the file read as though the Straus double-scalar
    multiplication had been verified.

    There is nothing here to finish.  The specification the statement
    would need, [ed25519_straus_2msm_gallina], does not exist anywhere
    in the tree; the placeholder comment named it as a TODO against
    ScalarmultVerified.v, where it was never written.  A real statement
    has to be authored from that spec outwards, so keeping an empty
    shell of one only obscures the gap.

    The body [straus_2msm_body] and [straus_2msm_helpers_present] above
    are untouched and still typecheck; they are what a future statement
    would be about. *)
