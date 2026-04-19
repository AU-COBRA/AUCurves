(** * Strong-check test on a realistic MULX-heavy jasmin_cmd.

    Mimics the per-column MUL/MULHUU pattern of a schoolbook 4x4-limb
    scalar multiply (as used in XEdDSA's [scalar_muladd]).  The
    bedrock2 source is excluded from the standard build modules, so we
    reconstruct the pattern directly as [jasmin_cmd] to exercise
    [wf_mulx_list_strong_b] on representative code. *)

From Coq Require Import String List ZArith.
Import ListNotations.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Bitwidth.
Require Import Bedrock.Jasmin.Core.
Require Import Bedrock.Jasmin.MulxSoundness.

Local Open Scope string_scope.

(** Column 0 of a 4x4 schoolbook: [p0 := e0 * a0; carry := mulhuu e0 a0].
    This is the cleanest matching pair --- no intervening statements. *)
Definition col0_body : jasmin_cmd :=
  JCseq (JCset "p0"    (JEmul    (JEvar "e0") (JEvar "a0")))
        (JCset "carry" (JEmulhuu (JEvar "e0") (JEvar "a0"))).

(** Column 1: two MULs with intervening ADDs, then two MULHUUs.
    Tests that the scan can pair non-adjacent MUL/MULHUU through
    [JEadd] statements that don't touch the operand-read vars. *)
Definition col1_body : jasmin_cmd :=
  JCseq (JCset "t0" (JEmul    (JEvar "e0") (JEvar "a1")))
  (JCseq (JCset "p1" (JEadd   (JEvar "carry") (JEvar "t0")))
  (JCseq (JCset "t1" (JEmulhuu (JEvar "e0") (JEvar "a1")))
         (JCset "t2" (JEmul    (JEvar "e1") (JEvar "a0"))))).

Definition col0_list : list jasmin_cmd := cmd_to_list col0_body.
Definition col1_list : list jasmin_cmd := cmd_to_list col1_body.

(* Diagnostic: how many statements, how many MULX matches, does the
   strong check pass? *)
Eval vm_compute in length col0_list.
Eval vm_compute in scan_mulx_pairs col0_list.
Eval vm_compute in wf_mulx_list_strong_b col0_list.

Eval vm_compute in length col1_list.
Eval vm_compute in scan_mulx_pairs col1_list.
Eval vm_compute in wf_mulx_list_strong_b col1_list.

(* Concrete soundness at the Prop/jeval level must be stated under a
   word context, since jeval_list is parameterised. *)
Section Sound.
  Context {width : Z} {BW : Bitwidth width}
          {w : word.word width} {w_ok : word.ok w}.

  Lemma col0_strong_check : wf_mulx_list_strong_b col0_list = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma col1_strong_check : wf_mulx_list_strong_b col1_list = true.
  Proof. vm_compute. reflexivity. Qed.

  Theorem col0_lower_sound :
    forall (e e' : string -> w),
      @jeval_list width w e col0_list e' ->
      @jeval_list width w e (lower_mulx_pairs col0_list) e'.
  Proof.
    intros e e' H.
    apply lower_mulx_pairs_list_correct_via_scan_check; auto.
    apply scan_mulx_pairs_valid_strong.
    apply col0_strong_check.
  Qed.

  Theorem col1_lower_sound :
    forall (e e' : string -> w),
      @jeval_list width w e col1_list e' ->
      @jeval_list width w e (lower_mulx_pairs col1_list) e'.
  Proof.
    intros e e' H.
    apply lower_mulx_pairs_list_correct_via_scan_check; auto.
    apply scan_mulx_pairs_valid_strong.
    apply col1_strong_check.
  Qed.
End Sound.

(* =================================================================== *)
(* Full 4x4 schoolbook: 16 MUL/MULHUU pairs exercising many matches    *)
(* simultaneously.  Each pair uses distinct target names [p_ij/h_ij]   *)
(* so the matches are position-disjoint by construction.               *)
(*                                                                     *)
(* FINDING: with shared operands across columns (e.g. [e0] is read by  *)
(* all 4 (0,j) pairs), the [pair_names_disjoint_b] check FAILS.  The   *)
(* reason is that [cmd_touches] over-approximates as "writes OR reads" *)
(* — the [JCmulx] inserted for pair (0,0) contains [JEvar "e0"] and is *)
(* thus flagged as touching [e0], which appears in pair (0,1)'s operand*)
(* reads.  This is semantically sound (JCmulx doesn't modify [e0]) but *)
(* the strong check is over-conservative here.                         *)
(*                                                                     *)
(* The Qed'd pipeline still works on a subset with distinct operands   *)
(* per pair (see [mul4_distinct_ops] below).                           *)
(* =================================================================== *)

Definition ei (i : nat) : string :=
  match i with 0 => "e0" | 1 => "e1" | 2 => "e2" | _ => "e3" end%string.
Definition aj (j : nat) : string :=
  match j with 0 => "a0" | 1 => "a1" | 2 => "a2" | _ => "a3" end%string.
Definition pij (i j : nat) : string :=
  match i, j with
  | 0,0 => "p00" | 0,1 => "p01" | 0,2 => "p02" | 0,3 => "p03"
  | 1,0 => "p10" | 1,1 => "p11" | 1,2 => "p12" | 1,3 => "p13"
  | 2,0 => "p20" | 2,1 => "p21" | 2,2 => "p22" | 2,3 => "p23"
  | 3,0 => "p30" | 3,1 => "p31" | 3,2 => "p32" | _,_ => "p33"
  end%string.
Definition hij (i j : nat) : string :=
  match i, j with
  | 0,0 => "h00" | 0,1 => "h01" | 0,2 => "h02" | 0,3 => "h03"
  | 1,0 => "h10" | 1,1 => "h11" | 1,2 => "h12" | 1,3 => "h13"
  | 2,0 => "h20" | 2,1 => "h21" | 2,2 => "h22" | 2,3 => "h23"
  | 3,0 => "h30" | 3,1 => "h31" | 3,2 => "h32" | _,_ => "h33"
  end%string.

(** One MUL/MULHUU pair with intervening accumulator ADD, like the
    XEdDSA scalar_muladd column pattern. *)
Definition sb_pair (i j : nat) : list jasmin_cmd :=
  [ JCset (pij i j) (JEmul    (JEvar (ei i)) (JEvar (aj j)));
    JCset "acc"     (JEadd    (JEvar "acc")  (JEvar (pij i j)));
    JCset (hij i j) (JEmulhuu (JEvar (ei i)) (JEvar (aj j))) ].

Definition schoolbook_list : list jasmin_cmd :=
  List.flat_map (fun ij => sb_pair (fst ij) (snd ij))
    [ (0,0); (0,1); (0,2); (0,3);
      (1,0); (1,1); (1,2); (1,3);
      (2,0); (2,1); (2,2); (2,3);
      (3,0); (3,1); (3,2); (3,3) ]%nat.

(* Diagnostics *)
Eval vm_compute in length schoolbook_list.
Eval vm_compute in length (scan_mulx_pairs schoolbook_list).
Eval vm_compute in wf_mulx_list_strong_b schoolbook_list.

(* After fixing pair_names_disjoint_b to only check writes (not reads),
   the full 16-pair schoolbook now passes the strong check. *)
Example schoolbook_strong_check_passes :
  wf_mulx_list_strong_b schoolbook_list = true.
Proof. vm_compute. reflexivity. Qed.

Section SoundSchoolbook.
  Context {width : Z} {BW : Bitwidth width}
          {w : word.word width} {w_ok : word.ok w}.

  (** Full 16-pair schoolbook lowering is sound: after fixing
      pair_names_disjoint_b to only check writes, shared operands like
      [e0] across all column-0 pairs are no longer falsely rejected. *)
  Theorem schoolbook_lower_sound :
    forall (e e' : string -> w),
      @jeval_list width w e schoolbook_list e' ->
      @jeval_list width w e (lower_mulx_pairs schoolbook_list) e'.
  Proof.
    intros e e' H.
    apply lower_mulx_pairs_list_correct_via_scan_check; auto.
    apply scan_mulx_pairs_valid_strong.
    apply schoolbook_strong_check_passes.
  Qed.
End SoundSchoolbook.

(* ----- 4-pair subset with distinct operands per pair --------------- *)

(** Four independent pairs, each using a disjoint set of operand
    variables, so [pair_names_disjoint_b] is satisfied. *)
Definition mul4_distinct_ops : list jasmin_cmd :=
  [ JCset "q0" (JEmul    (JEvar "x0") (JEvar "y0"));
    JCset "r0" (JEmulhuu (JEvar "x0") (JEvar "y0"));
    JCset "q1" (JEmul    (JEvar "x1") (JEvar "y1"));
    JCset "r1" (JEmulhuu (JEvar "x1") (JEvar "y1"));
    JCset "q2" (JEmul    (JEvar "x2") (JEvar "y2"));
    JCset "r2" (JEmulhuu (JEvar "x2") (JEvar "y2"));
    JCset "q3" (JEmul    (JEvar "x3") (JEvar "y3"));
    JCset "r3" (JEmulhuu (JEvar "x3") (JEvar "y3")) ].

Eval vm_compute in length (scan_mulx_pairs mul4_distinct_ops).
Eval vm_compute in wf_mulx_list_strong_b mul4_distinct_ops.

Section SoundMul4.
  Context {width : Z} {BW : Bitwidth width}
          {w : word.word width} {w_ok : word.ok w}.

  Lemma mul4_strong_check :
    wf_mulx_list_strong_b mul4_distinct_ops = true.
  Proof. vm_compute. reflexivity. Qed.

  Theorem mul4_lower_sound :
    forall (e e' : string -> w),
      @jeval_list width w e mul4_distinct_ops e' ->
      @jeval_list width w e (lower_mulx_pairs mul4_distinct_ops) e'.
  Proof.
    intros e e' H.
    apply lower_mulx_pairs_list_correct_via_scan_check; auto.
    apply scan_mulx_pairs_valid_strong.
    apply mul4_strong_check.
  Qed.
End SoundMul4.
