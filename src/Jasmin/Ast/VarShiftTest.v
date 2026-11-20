(** * A test of shifts by a variable amount through the whole translation.

    [shr_var] and [shl_var] are bedrock2 functions [r = x >> k] and [r = x << k] with [k] a
    variable.  [translate_prog] translates them ([vshift_translated]); the body of [shr_var]
    becomes [$t = x; $t = $t >> (k & 63); r = $t] ([shr_var_code]).  [shr_var_jasmin] and
    [shl_var_jasmin]: at bedrock2's concrete word ([BasicC64Semantics.word], [Naive.word 64]),
    [prog_correct] gives the Jasmin call of the translated program, returning
    [x >> (k mod 64)] (resp. [<<]), with no shift premise left: [naive_shift_masks] discharges
    it. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Jasmin Require Import utils wsize word memory_model low_memory expr psem_defs psem_core values
  varmap sem_type arch_extra x86_extra sem_params_of_arch_extra.
From Stdlib Require Import String ZArith.
Require Import bedrock2.Syntax bedrock2.BasicC64Semantics.
Require Import JasminBridge.Ast.PsemBig JasminBridge.Ast.Base JasminBridge.Ast.Trans
  JasminBridge.Ast.Comp JasminBridge.Ast.Sim JasminBridge.Ast.Fun JasminBridge.Ast.Prog.
Set SsrOldRewriteGoalsOrder.
Set Bullet Behavior "Strict Subproofs".
Local Open Scope string_scope.

Existing Instances Bitwidth64.BW64.

Definition shr_var : string * func :=
  ("shr_var", ([:: "x"; "k"], [:: "r"],
    cmd.set "r" (expr.op bopname.sru (expr.var "x") (expr.var "k")))).

Definition shl_var : string * func :=
  ("shl_var", ([:: "x"; "k"], [:: "r"],
    cmd.set "r" (expr.op bopname.slu (expr.var "x") (expr.var "k")))).

Definition vshift_funcs : list (string * func) := [:: shr_var; shl_var].

Local Notation fenv := (@coqutil.Map.Interface.map.of_list _ _ bedrock2.Semantics.env vshift_funcs).
Local Notation bword := (@coqutil.Word.Interface.word.rep 64 BasicC64Semantics.word).
Local Notation bmem := (@coqutil.Map.Interface.map.rep _ _ BasicC64Semantics.mem).

Section T.
  Context {atoI : arch_toIdent}.
  Context {syscall_state : Type} {sc_sem : syscall.syscall_sem syscall_state}.
  #[local] Existing Instance x86_extra.
  #[local] Existing Instance progUnit.
  Context {wsw : WithSubWord} {dc : DirectCall}.
  Variables (name : string -> Ident.ident) (fname : string -> funname)
            (finfo : string -> fun_info) (iinfo : positive -> instr_info).
  Hypothesis name_inj : injective name.
  Hypothesis fname_inj : injective fname.

  Lemma vshift_translated : isSome (translate_prog name fname finfo iinfo vshift_funcs).
  Proof. by vm_compute. Qed.

  (** The translated body: the amount is masked, [x >> (k & 63)]. *)
  Lemma shr_var_code :
    ccmdc name fname (snd (snd shr_var)) =
      Some [:: asg name (tmp 0) (pv name "x");
               asg name (tmp 0) (Papp2 (Olsr U64) (pv name (tmp 0)) (shamt name "k"));
               asg name "r" (pv name (tmp 0))].
  Proof. by []. Qed.

  (** A bedrock2 call of a one-statement function [r = op x k]. *)
  Lemma call_op fn o t m (x k : bword) :
    coqutil.Map.Interface.map.get fenv fn =
      Some ([:: "x"; "k"], [:: "r"], cmd.set "r" (expr.op o (expr.var "x") (expr.var "k"))) ->
    bedrock2.Semantics.call fenv fn t m [:: x; k]
      (fun t' m' rets => t' = t /\ m' = m /\ rets = [:: bedrock2.Semantics.interp_binop o x k]).
  Proof.
    move=> hget; do 3 eexists; split; first exact: hget.
    eexists; split; first reflexivity.
    econstructor; first reflexivity.
    by eexists; split; first reflexivity.
  Qed.

  Local Notation jcall P ev scs jm fn sp x k jm' r :=
    (PsemBig.sem_call P ev scs jm (fname fn) [:: Vword sp; Vword (jw x); Vword (jw k)] scs jm' [:: Vword r]).

  Theorem shr_var_jasmin P :
    translate_prog name fname finfo iinfo vshift_funcs = Some P ->
    forall ev scs jm (sp : u64) (x k : bword) (m : bmem), mem_rel m jm ->
      exists jm', jcall P ev scs jm "shr_var" sp x k jm' (wshr (jw x) (wunsigned (jw k) mod 64)) /\
        mem_rel m jm'.
  Proof.
    move=> hP ev scs jm sp x k m hm.
    have hrel := translate_prog_get name fname finfo iinfo vshift_funcs P fname_inj hP.
    have [jm' [vres [hcall [m' [rets [[_ [hm0 hr]] hv hm' _ _]]]]]] :=
      prog_correct name name_inj fname finfo iinfo P ev fenv hrel
        (fun _ _ _ _ _ _ => naive_shift_masks) "shr_var" nil m [:: x; k] _ jm scs sp
        (call_op "shr_var" bopname.sru nil m x k erefl) hm.
    subst; exists jm'; split => //; by rewrite -(jw_sru_var _ _ naive_shift_masks).
  Qed.

  Theorem shl_var_jasmin P :
    translate_prog name fname finfo iinfo vshift_funcs = Some P ->
    forall ev scs jm (sp : u64) (x k : bword) (m : bmem), mem_rel m jm ->
      exists jm', jcall P ev scs jm "shl_var" sp x k jm' (wshl (jw x) (wunsigned (jw k) mod 64)) /\
        mem_rel m jm'.
  Proof.
    move=> hP ev scs jm sp x k m hm.
    have hrel := translate_prog_get name fname finfo iinfo vshift_funcs P fname_inj hP.
    have [jm' [vres [hcall [m' [rets [[_ [hm0 hr]] hv hm' _ _]]]]]] :=
      prog_correct name name_inj fname finfo iinfo P ev fenv hrel
        (fun _ _ _ _ _ _ => naive_shift_masks) "shl_var" nil m [:: x; k] _ jm scs sp
        (call_op "shl_var" bopname.slu nil m x k erefl) hm.
    subst; exists jm'; split => //; by rewrite -(jw_slu_var _ _ naive_shift_masks).
  Qed.
End T.
