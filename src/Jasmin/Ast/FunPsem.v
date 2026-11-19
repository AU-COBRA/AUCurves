(** * The function theorems against Jasmin's own [psem].

    [Trans.run_sem], [Fun.jfun_correct] and [Fun2.jfun_correct2] conclude [PsemBig.sem] and
    [PsemBig.sem_call], so that they load with fiat-crypto's synthesis modules.  This file, in
    Jasmin's environment, states them for [psem.sem] and [psem.sem_call] (their statements
    before the switch to [PsemBig]), through [PsemBigIff]. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat ssralg seq.
From Jasmin Require Import utils wsize word memory_model low_memory expr psem_defs psem_core
  values varmap sem_type sopn arch_decl arch_extra x86_decl x86_instr_decl x86_extra
  sem_params_of_arch_extra.
From Jasmin Require psem.
From Stdlib Require Import ZArith Lia String.
Require coqutil.Word.Bitwidth.
Require bedrock2.Syntax bedrock2.Semantics.
Require coqutil.Map.Interface coqutil.Map.Properties.
Require Import JasminBridge.Ast.Base JasminBridge.Ast.Trans JasminBridge.Ast.Comp
  JasminBridge.Ast.Sim JasminBridge.Ast.Fun JasminBridge.Ast.Carry JasminBridge.Ast.Fun2
  JasminBridge.Ast.PsemBigIff.
Set SsrOldRewriteGoalsOrder.
Set Bullet Behavior "Strict Subproofs".

Import bedrock2.Syntax.
Module map := coqutil.Map.Interface.map.

Section R.
  Context {atoI : arch_toIdent}.
  Context {syscall_state : Type} {sc_sem : syscall.syscall_sem syscall_state}.
  #[local] Existing Instance x86_extra.
  Context {wsw : WithSubWord}.
  Context (gd : glob_decls).
  Context {dc : DirectCall} {pT : progT} {scP : semCallParams} (P : prog) (ev : extra_val_t).
  Hypothesis P_gd : p_globs P = gd.

  Lemma run_sem_psem s c s' : Trans.run gd s c = ok s' -> psem.sem P ev s c s'.
  Proof. move=> h; have hb := @run_sem _ _ _ _ gd dc pT scP P ev P_gd s c s' h; exact (proj1 (sem_iff P ev s c s') hb). Qed.
End R.

Section F.
  Context {atoI : arch_toIdent}.
  Context {syscall_state : Type} {sc_sem : syscall.syscall_sem syscall_state}.
  #[local] Existing Instance x86_extra.
  Context {wsw : WithSubWord}.
  #[local] Existing Instance progUnit.
  Variable name : string -> Ident.ident.
  Hypothesis name_inj : injective name.
  Variable cfn : Ident.ident.
  Variable iinfo : positive -> instr_info.
  Variable spillp : string -> bool.

  Context {W : coqutil.Word.Interface.word.word 64} {W_ok : coqutil.Word.Interface.word.ok W}.
  Context {BW : coqutil.Word.Bitwidth.Bitwidth 64}.
  Local Notation w64 := (@CW.rep 64 W).
  Context {Mem : map.map w64 coqutil.Byte.byte} {Mem_ok : map.ok Mem}.
  Context {L : map.map string w64} {L_ok : map.ok L}.
  Context {ext_spec : bedrock2.Semantics.ExtSpec}.
  Local Notation exec := (@bedrock2.Semantics.exec.exec 64 BW W Mem L ext_spec).

  Theorem jfun_correct_psem {dc : DirectCall} (P : uprog) ev fn fi ps jc body
      (fenv : @map.rep _ _ bedrock2.Semantics.env) t m args l0 post scs jm :
    get_fundef (p_funcs P) fn = Some (jfun name iinfo spillp fi ps jc) ->
    ccmd_sp name spillp body = Some jc -> (vsh_c body -> @shift_masks W) -> all ok_name ps ->
    map.of_list_zip ps args = Some l0 ->
    exec fenv body t m l0 post ->
    mem_rel m jm ->
    exists jm', psem.sem_call P ev scs jm fn [seq Vword (jw a) | a <- args] scs jm' [::] /\
      exists m' l', [/\ post t m' l', mem_rel m' jm',
        (forall k, map.get m' k = None <-> map.get m k = None) &
        (forall p, outside m p -> read jm' Aligned p U8 = read jm Aligned p U8)].
  Proof.
    move=> hf hc hS hok hz hex hm.
    have [jm' [hcall hpost]] := jfun_correct name name_inj iinfo spillp P ev fn fi ps jc body fenv
      t m args l0 post scs jm hf hc hS hok hz hex hm.
    by exists jm'; split => //; apply/sem_call_iff.
  Qed.

  Theorem jfun_correct2_psem {dc : DirectCall} (P : uprog) ev fn fi ps jc body
      (fenv : @map.rep _ _ bedrock2.Semantics.env) t m args l0 post scs jm :
    get_fundef (p_funcs P) fn = Some (jfun name iinfo spillp fi ps jc) ->
    xcmd name cfn spillp ps body = Some jc \/ ccmd_sp name spillp body = Some jc ->
    (vsh_c body -> @shift_masks W) ->
    all ok_name ps ->
    map.of_list_zip ps args = Some l0 ->
    exec fenv body t m l0 post ->
    mem_rel m jm ->
    exists jm', psem.sem_call P ev scs jm fn [seq Vword (jw a) | a <- args] scs jm' [::] /\
      exists m' l', [/\ post t m' l', mem_rel m' jm',
        (forall k, map.get m' k = None <-> map.get m k = None) &
        (forall p, outside m p -> read jm' Aligned p U8 = read jm Aligned p U8)].
  Proof.
    move=> hf hc hS hok hz hex hm.
    have [jm' [hcall hpost]] := jfun_correct2 name name_inj cfn iinfo spillp P ev fn fi ps jc body
      fenv t m args l0 post scs jm hf hc hS hok hz hex hm.
    by exists jm'; split => //; apply/sem_call_iff.
  Qed.
End F.
