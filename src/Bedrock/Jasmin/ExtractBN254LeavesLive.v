(** * BN254 Fp leaves with liveness-chosen [#[spill]] hints.

    The same leaf list as [deprecated/ExtractBN254Text.v]
    ([bn254_add], [bn254_sub], [bn254_mul], [bn254_square],
    [bn254_select_znz], [bn254_felem_copy]), translated by
    [tr_func_sized 4] and [polish_func], printed three ways:

      - [bn254_leaves_rocq]: [pp_module], every register local [#[spill]]
        (the committed emission);
      - [bn254_leaves_live_rocq]: the same functions through
        [AdcChain.polish_func_adc] ([polish_func] plus the proved
        [adc_func] rewrite of fiat's carry and borrow windows into
        [#ADCX] / [#SBB] chains), printed by [pp_module_live] with hints
        chosen by
        [SpillLiveness.spill_choice] at [default_budget];
      - the hint report: per leaf, the hinted variables and the
        residual maximal register occupancy of the pressure model.

    Compile the emission with [jasminc -auto-spill].  The hints are
    inert: [bn254_leaves_live_erases] instantiates
    [SpillLiveness.pp_module_live_erases].

    The separately compiled leaves ([generated/bn254_leaves_live.jazz]) are
    [bn254_leaves_jasmin_ct]: the same ASTs after [CtSelect.ct_func], which
    rewrites the branches that remain after [polish_func_adc] (the carry and
    borrow copied into a word, the borrow mask of the subtraction, the final
    selection between [t] and [t - p], the selection of [select_znz]) into
    [#ADCX] / [#SBB] and mask arithmetic, with [CtSelect.ct_func_correct]
    against [AdcChain.run]; [bn254_leaves_ct_branch_free] checks by computation
    that no [if] is left, [bn254_leaves_ct_erases] that the hints are inert, and
    the module is printed by [pp_module_live_b bn254_leaf_ct_budget]. *)

From Stdlib Require Import String List ZArith.
Import ListNotations.
Require Import bedrock2.Syntax.
Require Import Bedrock.Field.Synthesis.Examples.bn254_prime.
Require Import Bedrock.Field.Synthesis.Examples.bn254_felem_copy.
Require Import Bedrock.Jasmin.Core.
Require Import Bedrock.Jasmin.SpillLiveness.
Require Import Bedrock.Jasmin.AdcChain.
Require Import Bedrock.Jasmin.CtSelect.
Local Open Scope string_scope.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Definition bn254_leaf_funcs : list function_t := Eval vm_compute in
  [ bn254_add; bn254_sub; bn254_mul; bn254_square; bn254_select_znz;
    ("bn254_felem_copy", bn254_felem_copy) ].

Definition bn254_leaves_jasmin : list jasmin_func := Eval vm_compute in
  List.map (fun f => polish_func (tr_func_sized 4 f)) bn254_leaf_funcs.

Definition bn254_leaves_jasmin_adc : list jasmin_func := Eval vm_compute in
  List.map (fun f => polish_func_adc (tr_func_sized 4 f)) bn254_leaf_funcs.

(** The hinted module, with its annotations erased, is the hint-free
    [pp_module_nospill] emission of the same AST. *)
Lemma bn254_leaves_live_erases :
  String.concat (LF ++ LF)
    (List.map (fun f => render (erase (emit (spill_choice default_budget f) f)))
              bn254_leaves_jasmin_adc)
  = pp_module_nospill bn254_leaves_jasmin_adc.
Proof. apply pp_module_live_erases. Qed.

(** ** The branch-free leaves

    [CtSelect.ct_func] after [polish_func_adc]: the separately compiled
    leaves. *)
Definition bn254_leaves_jasmin_ct : list jasmin_func := Eval vm_compute in
  List.map ct_func bn254_leaves_jasmin_adc.

Lemma bn254_leaves_jasmin_ct_eq :
  bn254_leaves_jasmin_ct = List.map ct_func bn254_leaves_jasmin_adc.
Proof. vm_compute. reflexivity. Qed.

(** Each branch-free leaf is [ct_func] of a [polish_func_adc] leaf, so
    [CtSelect.ct_func_correct] applies to it: whenever the [polish_func_adc]
    body runs ([AdcChain.run]), the branch-free body runs to the same final
    memory. *)
Lemma bn254_leaves_ct_of_adc : forall g, In g bn254_leaves_jasmin_ct ->
  exists f, In f bn254_leaves_jasmin_adc /\ g = ct_func f.
Proof.
  intros g Hg. rewrite bn254_leaves_jasmin_ct_eq in Hg.
  apply in_map_iff in Hg as [f [<- Hf]]. exists f. split; [exact Hf | reflexivity].
Qed.

(** No [if] and no [while] is left in any leaf: [pp_cmd] prints no
    conditional, so jasminc emits no conditional jump for them. *)
Lemma bn254_leaves_ct_branch_free : branch_free_funcs bn254_leaves_jasmin_ct = true.
Proof. vm_compute. reflexivity. Qed.

(** The hints are inert at every budget. *)
Lemma bn254_leaves_ct_erases : forall budget,
  String.concat (LF ++ LF)
    (List.map (fun f => render (erase (emit (spill_choice budget f) f)))
              bn254_leaves_jasmin_ct)
  = pp_module_nospill bn254_leaves_jasmin_ct.
Proof. intros. apply pp_module_live_erases. Qed.

(** The register budget of the branch-free leaves' hints.  Measured
    (rdtsc, serial chain, interleaved batches, this machine; old = the
    branching leaves at the default budget 16): budget 11: mul +6.5 / square
    +6.8 cycles over the old leaves, 12: +4.4 / +6.2, 13: +2.4 / +4.7,
    14: +2.4..2.7 / +3.2..4.1 (about 55 cycles against 52), 15: +6.1 / +6.2,
    16: register allocation fails.  The budget is lower than the branching
    leaves' because [SpillLiveness.linearize] counts an [if] as reading the
    variable it assigns, which kept the four select outputs live from the
    start of the function in the pressure model. *)
Definition bn254_leaf_ct_budget : nat := 14.

(** Hint report of the branch-free leaves. *)
Eval vm_compute in
  List.map (fun f => (jf_name f, analyse bn254_leaf_ct_budget f)) bn254_leaves_jasmin_ct.

(** Hint report: per leaf, (name, hinted variables, residual occupancy). *)
Eval vm_compute in
  List.map (fun f => (jf_name f, analyse default_budget f)) bn254_leaves_jasmin_adc.

Redirect "bn254_leaves_rocq" Eval vm_compute in pp_module bn254_leaves_jasmin.
Redirect "bn254_leaves_live_rocq" Eval vm_compute in pp_module_live bn254_leaves_jasmin_adc.
