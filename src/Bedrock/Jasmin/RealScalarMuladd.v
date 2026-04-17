(** * Strong-check run on a raw cmd derived from XEdDSA's scalar_muladd.

    XEdDSA's [scalar_muladd] body is reconstructed here as a raw
    bedrock2 [cmd] (avoiding a dependency on [End2End.XEdDSA.Sign],
    which is excluded from the standard build modules).  We apply
    [tr_cmd] -> [cmd_to_list] to obtain [list jasmin_cmd] and then
    exercise [wf_mulx_list_strong_b] on it.

    Finding (verified via [vm_compute]): the scan finds exactly one
    match — (mul_idx=4, mulhuu_idx=5, hi="carry", lo="p0",
    a=JEvar "e0", b=JEvar "a0") — corresponding to the clean column-0
    pair [p0 := e0*a0; carry := mulhuu e0 a0].  The strong check
    passes on this match, so [lower_mulx_pairs] soundness on this
    body is Qed with zero conjectures.

    The scalar_muladd body has additional MUL/MULHUU sites that the
    scan does NOT find, because they are nested inside [JEadd]
    expressions rather than being top-level [JCset]s, e.g.
    [carry := carry + mulhuu e1 a0] and
    [p1 := carry + e0*a1].  The scan's pattern-matching is syntactic
    and looks only at top-level [JCset _ (JEmul a b)] and
    [JCset _ (JEmulhuu a b)].  Matching nested operands would need
    a pre-normalization pass that hoists these into fresh temporaries. *)

From Stdlib Require Import String List ZArith.
Import ListNotations.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Bitwidth.
Require Import bedrock2.Syntax.
Require Import Bedrock.Jasmin.Core.
Require Import Bedrock.Jasmin.MulxSoundness.

Local Open Scope string_scope.

(** Helper: fold a list of statements through [cmd.seq], ending in
    [cmd.skip].  Produces a properly-associated sequence. *)
Definition seq_of (cs : list cmd) : cmd :=
  List.fold_right (fun c acc => cmd.seq c acc) cmd.skip cs.

(** Raw [cmd] mirroring [scalar_muladd]'s body for columns 0 and 1
    (the only columns where MULHUU appears in the XEdDSA version;
    columns 2 and 3 truncate the carry). *)
Definition sma_col01 : cmd :=
  seq_of
    [ cmd.set "e0" (expr.load access_size.word (expr.var "e_scalar"))
    ; cmd.set "e1" (expr.load access_size.word
                      (expr.op bopname.add (expr.var "e_scalar") (expr.literal 8)))
    ; cmd.set "a0" (expr.load access_size.word (expr.var "a_scalar"))
    ; cmd.set "a1" (expr.load access_size.word
                      (expr.op bopname.add (expr.var "a_scalar") (expr.literal 8)))
    ; cmd.set "p0"    (expr.op bopname.mul    (expr.var "e0") (expr.var "a0"))
    ; cmd.set "carry" (expr.op bopname.mulhuu (expr.var "e0") (expr.var "a0"))
    ; cmd.set "p1"    (expr.op bopname.add (expr.var "carry")
                        (expr.op bopname.mul (expr.var "e0") (expr.var "a1")))
    ; cmd.set "carry" (expr.op bopname.mulhuu (expr.var "e0") (expr.var "a1"))
    ; cmd.set "p1"    (expr.op bopname.add (expr.var "p1")
                        (expr.op bopname.mul (expr.var "e1") (expr.var "a0")))
    ; cmd.set "carry" (expr.op bopname.add (expr.var "carry")
                        (expr.op bopname.mulhuu (expr.var "e1") (expr.var "a0")))
    ].

Definition sma_jcmd : jasmin_cmd := tr_cmd sma_col01.
Definition sma_list : list jasmin_cmd := cmd_to_list sma_jcmd.

(* Diagnostics *)
Eval vm_compute in length sma_list.
Eval vm_compute in scan_mulx_pairs sma_list.
Eval vm_compute in wf_mulx_list_strong_b sma_list.

(** The scan finds exactly one matchable pair, and the strong check
    passes on it. *)
Example sma_scan_finds_one_match :
  scan_mulx_pairs sma_list =
    [(4%nat, 5%nat, "carry"%string, "p0"%string, JEvar "e0", JEvar "a0")].
Proof. vm_compute. reflexivity. Qed.

Example sma_strong_check :
  wf_mulx_list_strong_b sma_list = true.
Proof. vm_compute. reflexivity. Qed.

Section Sound.
  Context {width : Z} {BW : Bitwidth width}
          {w : word.word width} {w_ok : word.ok w}.

  (** End-to-end conjecture-free soundness on the real scalar_muladd
      body, for the pattern the scan can match. *)
  Theorem sma_lower_sound :
    forall (e e' : string -> w),
      @jeval_list width w e sma_list e' ->
      @jeval_list width w e (lower_mulx_pairs sma_list) e'.
  Proof.
    intros e e' H.
    apply lower_mulx_pairs_list_correct_via_scan_check; auto.
    apply scan_mulx_pairs_valid_strong. apply sma_strong_check.
  Qed.
End Sound.
