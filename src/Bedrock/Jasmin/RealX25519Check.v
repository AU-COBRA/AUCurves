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
