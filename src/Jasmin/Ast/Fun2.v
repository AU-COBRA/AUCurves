(** * Functions translated by [Carry.xcmd] (or, when it fails, by [Comp.ccmd_sp]), called
    through Jasmin's [sem_call]. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat ssralg seq.
From Jasmin Require Import utils wsize word memory_model low_memory expr psem psem_facts
  values varmap sem_type sopn arch_decl arch_extra x86_decl x86_instr_decl x86_extra
  sem_params_of_arch_extra.
From Stdlib Require Import ZArith Lia String.
Require coqutil.Word.Bitwidth.
Require bedrock2.Syntax bedrock2.Semantics.
Require coqutil.Map.Interface coqutil.Map.Properties.
Require Import JasminBridge.Ast.Base JasminBridge.Ast.Trans JasminBridge.Ast.Comp JasminBridge.Ast.Sim
  JasminBridge.Ast.Fun JasminBridge.Ast.Carry JasminBridge.Ast.CarrySim.
Set SsrOldRewriteGoalsOrder.
Set Bullet Behavior "Strict Subproofs".

Import bedrock2.Syntax.
Module map := coqutil.Map.Interface.map.

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

  (** The function theorem for code produced by either translation. *)
  Theorem jfun_correct2 {dc : DirectCall} (P : uprog) ev fn fi ps jc body
      (fenv : @map.rep _ _ bedrock2.Semantics.env) t m args l0 post scs jm :
    get_fundef (p_funcs P) fn = Some (jfun name iinfo spillp fi ps jc) ->
    xcmd name cfn spillp ps body = Some jc \/ ccmd_sp name spillp body = Some jc ->
    all ok_name ps ->
    map.of_list_zip ps args = Some l0 ->
    exec fenv body t m l0 post ->
    mem_rel m jm ->
    exists jm', sem_call P ev scs jm fn [seq Vword (jw a) | a <- args] scs jm' [::] /\
      exists m' l', [/\ post t m' l', mem_rel m' jm',
        (forall k, map.get m' k = None <-> map.get m k = None) &
        (forall p, outside m p -> read jm' Aligned p U8 = read jm Aligned p U8)].
  Proof.
    move=> hf hc hok hz hex hm.
    have hsz := size_zip_args hz.
    pose (s0 := @Estate wsw syscall_state (@ep_of_asm_e _ _ _ _ _ _ _ x86_extra syscall_state sc_sem) scs jm Vm.init).
    pose (s1 := with_vm s0 (set_params name Vm.init ps args)).
    have hl1 : RL name l0 (evm s1).
    { apply: (RL_params name) hok hz; [exact: name_inj | exact: (RL_empty name)]. }
    have [s2 [hr [m' [l' [hpost hm2 hscs hdom hfr]]]]] : exists s2, Trans.run (p_globs P) s1 jc = ok s2 /\
      exists m' l', [/\ post t m' l', mem_rel m' (emem s2), escs s2 = escs s1,
        (forall k, map.get m' k = None <-> map.get m k = None) &
        (forall p, outside m p -> read (emem s2) Aligned p U8 = read (emem s1) Aligned p U8)].
    { case: hc => hc.
      - have [s2 [hr [m' [l' [hpost [hm2 hscs hdom hfr]]]]]] :=
          xcmd_correct name name_inj cfn (p_globs P) spillp fenv body ps jc hc t m l0 post hex s1 hl1
            (putmany_keys hz) hm.
        by exists s2; split => //; exists m', l'; split.
      - have [s2 [hr [m' [l' [hpost hl2 hm2 hscs [hdom hfr]]]]]] :=
          ccmd_sp_correct name name_inj (p_globs P) spillp fenv _ _ hc _ _ _ _ hex s1 hl1 hm.
        by exists s2; split => //; exists m', l'; split. }
    exists (emem s2); split; last by exists m', l'; split.
    eapply EcallRun with (f := jfun name iinfo spillp fi ps jc) (s0 := s0) (s1 := s1) (s2 := s2); try reflexivity.
    all: try exact hf.
    all: try (exact: truncate_args).
    all: try (exact: write_params).
    - apply: (run_sem _ P ev erefl); rewrite /jfun /= run_renumber run_cat run_spills; first exact: hr.
      exact: (RL_defined name hl1 (putmany_keys hz)).
    - by rewrite hscs.
  Qed.
End F.
