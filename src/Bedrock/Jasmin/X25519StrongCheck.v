(** * Zero-conjecture soundness demo on extracted X25519 bedrock2 → Jasmin.

    Demonstrates the Phase 3 trust chain on selected functions drawn
    from the X25519-64 Montgomery-ladder bedrock2 sources:

      [wf_mulx_list_strong_b (cmd_to_list body) = true]
        — scan_mulx_pairs_valid_strong →
      [scan_output_valid_b (cmd_to_list body)]
        — lower_mulx_pairs_list_correct_via_scan_check →
      [jeval_list e cs e' → jeval_list e (lower_mulx_pairs cs) e']
        — MS_to_jeval + lower_mulx_pairs_cmd_correct_via_scan_check →
      [jeval env1 body env2 → jeval env1 (lower_mulx_pairs_cmd body) env2]

    No conjectures, no admits.  The check is a [vm_compute] reduction
    on the concrete extracted program.

    To keep compile cost bounded we pick the bedrock2 sources directly
    and avoid materializing the entire [funcs] list (which would
    [vm_compute] [tr_func_sized] over x25519, montladder, ladderstep,
    fe25519_mul, ...).  We translate only the handful of bodies used
    here.  (See [RealX25519Check.v] for pattern-heavy diagnostics.) *)

From Coq Require Import String List ZArith.
Import ListNotations.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Bitwidth.
Require Import Bedrock.Jasmin.Core.
Require Import Bedrock.Jasmin.MulxSoundness.
Require Import Bedrock.Jasmin.PolishProofs.
Require Import Bedrock.End2End.X25519_64.MontgomeryLadder64.

Local Open Scope string_scope.

(** Pick a named bedrock2 function from [funcs] and project its body
    to a [jasmin_cmd] via [tr_cmd].  No [tr_func_sized] applied — we
    only need the body for the strong check.

    This avoids materializing a [list jasmin_func] for all 16 bedrock2
    functions: the filter visits each entry of [funcs] but only the
    matched ones have their body translated, and [vm_compute] only
    fully reduces the [tr_cmd] application on the 6 bodies we name. *)

Definition lookup_body (name : string)
  (fs : list (string * (list string * list string * Syntax.cmd)))
  : jasmin_cmd :=
  match List.find (fun f => String.eqb (fst f) name) fs with
  | Some (_, (_, _, body)) => tr_cmd body
  | None => JCskip
  end.

Definition body_add   : jasmin_cmd := Eval vm_compute in lookup_body "fe25519_add"  funcs.
Definition body_sub   : jasmin_cmd := Eval vm_compute in lookup_body "fe25519_sub"  funcs.
Definition body_copy  : jasmin_cmd := Eval vm_compute in lookup_body "fe25519_copy" funcs.
Definition body_cswap : jasmin_cmd := Eval vm_compute in lookup_body "felem_cswap"  funcs.
Definition body_clamp : jasmin_cmd := Eval vm_compute in lookup_body "clamp_64"     funcs.
Definition body_mul   : jasmin_cmd := Eval vm_compute in lookup_body "fe25519_mul"  funcs.

(** Diagnostic: length / scan / strong-check result on each body.
    Expected: add/sub/copy/cswap/clamp pass vacuously (no MUL matches);
    mul has matches but fails the pair-names-disjoint check (shared
    operands across schoolbook columns — see [RealX25519Check.v]
    schoolbook_strong_check_fails for the same observation). *)
Eval vm_compute in length (cmd_to_list body_add).
Eval vm_compute in length (scan_mulx_pairs (cmd_to_list body_add)).
Eval vm_compute in wf_mulx_list_strong_b (cmd_to_list body_add).

Eval vm_compute in length (cmd_to_list body_sub).
Eval vm_compute in wf_mulx_list_strong_b (cmd_to_list body_sub).

Eval vm_compute in length (cmd_to_list body_copy).
Eval vm_compute in wf_mulx_list_strong_b (cmd_to_list body_copy).

Eval vm_compute in length (cmd_to_list body_cswap).
Eval vm_compute in wf_mulx_list_strong_b (cmd_to_list body_cswap).

Eval vm_compute in length (cmd_to_list body_clamp).
Eval vm_compute in wf_mulx_list_strong_b (cmd_to_list body_clamp).

Eval vm_compute in length (cmd_to_list body_mul).
Eval vm_compute in length (scan_mulx_pairs (cmd_to_list body_mul)).
Eval vm_compute in wf_mulx_list_strong_b (cmd_to_list body_mul).

Section Sound.
  Context {width : Z} {BW : Bitwidth width}
          {w : word.word width} {w_ok : word.ok w}.

  (** ** Strong checks pass on the 5 MUL-free ops in the working set. *)

  Lemma add_strong_check :
    wf_mulx_list_strong_b (cmd_to_list body_add) = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma sub_strong_check :
    wf_mulx_list_strong_b (cmd_to_list body_sub) = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma copy_strong_check :
    wf_mulx_list_strong_b (cmd_to_list body_copy) = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma cswap_strong_check :
    wf_mulx_list_strong_b (cmd_to_list body_cswap) = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma clamp_strong_check :
    wf_mulx_list_strong_b (cmd_to_list body_clamp) = true.
  Proof. vm_compute. reflexivity. Qed.

  (** ** Zero-conjecture end-to-end lowering soundness.

      For each of the 5 MUL-free functions above, we obtain
      [jeval env1 body env2 → jeval env1 (lower_mulx_pairs_cmd body) env2]
      by composing the concrete check with the two Phase 3 theorems
      [scan_mulx_pairs_valid_strong] and
      [lower_mulx_pairs_cmd_correct_via_scan_check]. *)

  Ltac lower_sound_from_check CHK :=
    let env1 := fresh "env1" in
    let env2 := fresh "env2" in
    let H := fresh "H" in
    intros env1 env2 H;
    apply MS_to_jeval;
    apply MulxSoundness.list_to_cmd_sound;
    apply MulxSoundness.lower_mulx_pairs_list_correct_via_scan_check;
    [ apply scan_mulx_pairs_valid_strong; exact CHK
    | apply MulxSoundness.cmd_to_list_sound;
      apply jeval_to_MS; exact H ].

  Theorem add_lower_sound :
    forall env1 env2,
      @jeval width w env1 body_add env2 ->
      @jeval width w env1 (lower_mulx_pairs_cmd body_add) env2.
  Proof. lower_sound_from_check add_strong_check. Qed.

  Theorem sub_lower_sound :
    forall env1 env2,
      @jeval width w env1 body_sub env2 ->
      @jeval width w env1 (lower_mulx_pairs_cmd body_sub) env2.
  Proof. lower_sound_from_check sub_strong_check. Qed.

  Theorem copy_lower_sound :
    forall env1 env2,
      @jeval width w env1 body_copy env2 ->
      @jeval width w env1 (lower_mulx_pairs_cmd body_copy) env2.
  Proof. lower_sound_from_check copy_strong_check. Qed.

  Theorem cswap_lower_sound :
    forall env1 env2,
      @jeval width w env1 body_cswap env2 ->
      @jeval width w env1 (lower_mulx_pairs_cmd body_cswap) env2.
  Proof. lower_sound_from_check cswap_strong_check. Qed.

  Theorem clamp_lower_sound :
    forall env1 env2,
      @jeval width w env1 body_clamp env2 ->
      @jeval width w env1 (lower_mulx_pairs_cmd body_clamp) env2.
  Proof. lower_sound_from_check clamp_strong_check. Qed.

  (** ** fe25519_mul now passes the strong check.

      After fixing [pair_names_disjoint_b] to only check writes (not
      reads), the 5×5-limb schoolbook multiplication passes.  The prior
      check required operand variables to be disjoint from the reads of
      other pairs' operands, but [JCmulx] only writes [hi] and [lo] —
      shared read-operands like [e0] reused across rows are safe. *)
  Lemma mul_strong_check :
    wf_mulx_list_strong_b (cmd_to_list body_mul) = true.
  Proof. vm_compute. reflexivity. Qed.

  Theorem mul_lower_sound :
    forall (e e' : string -> w),
      @jeval_list width w e (cmd_to_list body_mul) e' ->
      @jeval_list width w e (lower_mulx_pairs (cmd_to_list body_mul)) e'.
  Proof.
    intros e e' H.
    apply lower_mulx_pairs_list_correct_via_scan_check; auto.
    apply scan_mulx_pairs_valid_strong.
    apply mul_strong_check.
  Qed.
End Sound.
