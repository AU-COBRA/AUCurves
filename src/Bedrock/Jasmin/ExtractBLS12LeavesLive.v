(** * BLS12 Fp leaves with liveness-chosen [#[spill]] hints.

    The same leaf list as [deprecated/ExtractBLS12Text.v]
    ([bls12_add], [bls12_sub], [bls12_mul], [bls12_square],
    [bls12_select_znz], [bls12_felem_copy]), translated by
    [tr_func_sized 6] and [polish_func], printed three ways:

      - [bls12_leaves_rocq]: [pp_module], every register local [#[spill]]
        (the committed emission);
      - [bls12_leaves_live_rocq]: the same functions through
        [AdcChain.polish_func_adc] ([polish_func] plus the proved
        [adc_func] rewrite of fiat's carry and borrow windows into
        [#ADCX] / [#SBB] chains), printed by [pp_module_live] with hints
        chosen by
        [SpillLiveness.spill_choice] at [default_budget];
      - the hint report: per leaf, the hinted variables and the
        residual maximal register occupancy of the pressure model.

    Compile the emission with [jasminc -auto-spill].  The hints are
    inert: [bls12_leaves_live_erases] instantiates
    [SpillLiveness.pp_module_live_erases].

    The separately compiled leaves ([generated/bls12_leaves_live.jazz]) are
    [bls12_leaves_jasmin_ct]: the same ASTs after [CtSelect.ct_func], which
    rewrites the branches that remain after [polish_func_adc] (the carry and
    borrow copied into a word, the borrow mask of the subtraction, the final
    selection between [t] and [t - p], the selection of [select_znz]) into
    [#ADCX] / [#SBB] and mask arithmetic, with [CtSelect.ct_func_correct]
    against [AdcChain.run]; [bls12_leaves_ct_branch_free] checks by computation
    that no [if] is left, [bls12_leaves_ct_erases] that the hints are inert, and
    the module is printed by [pp_module_live_b bls12_leaf_ct_budget]. *)

From Stdlib Require Import String List ZArith.
Import ListNotations.
Require Import bedrock2.Syntax.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_felem_copy.
Require Import Bedrock.Jasmin.Core.
Require Import Bedrock.Jasmin.SpillLiveness.
Require Import Bedrock.Jasmin.AdcChain.
Require Import Bedrock.Jasmin.CtSelect.
Local Open Scope string_scope.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Definition bls12_leaf_funcs : list function_t := Eval vm_compute in
  [ bls12_add; bls12_sub; bls12_mul; bls12_square; bls12_select_znz;
    ("bls12_felem_copy", bls12_felem_copy) ].

Definition bls12_leaves_jasmin : list jasmin_func := Eval vm_compute in
  List.map (fun f => polish_func (tr_func_sized 6 f)) bls12_leaf_funcs.

Definition bls12_leaves_jasmin_adc : list jasmin_func := Eval vm_compute in
  List.map (fun f => polish_func_adc (tr_func_sized 6 f)) bls12_leaf_funcs.

(** The hinted module, with its annotations erased, is the hint-free
    [pp_module_nospill] emission of the same AST. *)
Lemma bls12_leaves_live_erases :
  String.concat (LF ++ LF)
    (List.map (fun f => render (erase (emit (spill_choice default_budget f) f)))
              bls12_leaves_jasmin_adc)
  = pp_module_nospill bls12_leaves_jasmin_adc.
Proof. apply pp_module_live_erases. Qed.

(** ** The branch-free leaves

    [CtSelect.ct_func] after [polish_func_adc]: the separately compiled
    leaves. *)
Definition bls12_leaves_jasmin_ct : list jasmin_func := Eval vm_compute in
  List.map ct_func bls12_leaves_jasmin_adc.

Lemma bls12_leaves_jasmin_ct_eq :
  bls12_leaves_jasmin_ct = List.map ct_func bls12_leaves_jasmin_adc.
Proof. vm_compute. reflexivity. Qed.

(** Each branch-free leaf is [ct_func] of a [polish_func_adc] leaf, so
    [CtSelect.ct_func_correct] applies to it: whenever the [polish_func_adc]
    body runs ([AdcChain.run]), the branch-free body runs to the same final
    memory. *)
Lemma bls12_leaves_ct_of_adc : forall g, In g bls12_leaves_jasmin_ct ->
  exists f, In f bls12_leaves_jasmin_adc /\ g = ct_func f.
Proof.
  intros g Hg. rewrite bls12_leaves_jasmin_ct_eq in Hg.
  apply in_map_iff in Hg as [f [<- Hf]]. exists f. split; [exact Hf | reflexivity].
Qed.

(** No [if] and no [while] is left in any leaf: [pp_cmd] prints no
    conditional, so jasminc emits no conditional jump for them. *)
Lemma bls12_leaves_ct_branch_free : branch_free_funcs bls12_leaves_jasmin_ct = true.
Proof. vm_compute. reflexivity. Qed.

(** The hints are inert at every budget. *)
Lemma bls12_leaves_ct_erases : forall budget,
  String.concat (LF ++ LF)
    (List.map (fun f => render (erase (emit (spill_choice budget f) f)))
              bls12_leaves_jasmin_ct)
  = pp_module_nospill bls12_leaves_jasmin_ct.
Proof. intros. apply pp_module_live_erases. Qed.

(** The register budget of the branch-free leaves' hints.  Measured
    (rdtsc, serial chain, interleaved batches, this machine; old = the
    branching leaves at budget 21): budget 13: mul +6.6 / square +7.9 cycles
    over the old leaves, 14: +2.8 / +3.2, 15: +0.1 / -0.3 (about 103 cycles),
    16 and above: register allocation fails.  The budget is lower than the
    branching leaves' 21 because [SpillLiveness.linearize] counts an [if] as
    reading the variable it assigns, which kept the six select outputs live
    from the start of the function in the pressure model. *)
Definition bls12_leaf_ct_budget : nat := 15.

(** Hint report of the branch-free leaves. *)
Eval vm_compute in
  List.map (fun f => (jf_name f, analyse bls12_leaf_ct_budget f)) bls12_leaves_jasmin_ct.

(** Hint report: per leaf, (name, hinted variables, residual occupancy). *)
Eval vm_compute in
  List.map (fun f => (jf_name f, analyse default_budget f)) bls12_leaves_jasmin_adc.

Redirect "bls12_leaves_rocq" Eval vm_compute in pp_module bls12_leaves_jasmin.
Redirect "bls12_leaves_live_rocq" Eval vm_compute in pp_module_live bls12_leaves_jasmin_adc.
