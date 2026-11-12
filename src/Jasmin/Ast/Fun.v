(** * Functions: a translated bedrock2 function, called through Jasmin's [sem_call]. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat ssralg seq.
From Jasmin Require Import utils wsize word memory_model low_memory expr psem psem_facts
  values varmap sem_type sopn arch_decl arch_extra x86_decl x86_instr_decl x86_extra
  sem_params_of_arch_extra.
From Stdlib Require Import ZArith Lia String.
Require coqutil.Word.Bitwidth.
Require bedrock2.Syntax bedrock2.Semantics.
Require coqutil.Map.Interface coqutil.Map.Properties.
Require Import JasminBridge.Ast.Base JasminBridge.Ast.Trans JasminBridge.Ast.Comp JasminBridge.Ast.Sim.
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
  (** Instruction information, one per instruction, supplied by the driver (the compiler's
      oracles key their tables on it); the semantics ignores it. *)
  Variable iinfo : positive -> instr_info.
  Variable spillp : string -> bool.

  Fixpoint renumber (k : positive) (c : jcmd) : jcmd :=
    match c with
    | [::] => [::]
    | MkI _ i :: c => MkI (iinfo k) i :: renumber (Pos.succ k) c
    end.

  Lemma run_i_ii gd s ii ii' i : run_i gd s (MkI ii i) = run_i gd s (MkI ii' i).
  Proof. by case: i. Qed.

  Lemma run_renumber gd s k c : run gd s (renumber k c) = run gd s c.
  Proof.
    elim: c s k => [|[ii i] c ih] s k //.
    cbn [renumber run]; rewrite (run_i_ii _ _ _ ii); case: run_i => //= s'; exact: ih.
  Qed.

  (** A Jasmin function with [u64] register parameters, no results (the leaves return through
      memory), body [jc]; [fi] is the function information supplied by the driver. *)
  Definition jfun (fi : fun_info) (ps : list string) (jc : jcmd) : ufundef :=
    {| f_info := fi; f_contract := None; f_tyin := [seq aword U64 | _ <- ps];
       f_params := [seq vi name p | p <- ps];
       f_body := renumber 1 (spills name spillp pseudo_operator.Spill ps ++ jc); f_tyout := [::]; f_res := [::];
       f_extra := tt |}.

  Context {W : coqutil.Word.Interface.word.word 64} {W_ok : coqutil.Word.Interface.word.ok W}.
  Context {BW : coqutil.Word.Bitwidth.Bitwidth 64}.
  Local Notation w64 := (@CW.rep 64 W).
  Context {Mem : map.map w64 coqutil.Byte.byte} {Mem_ok : map.ok Mem}.
  Context {L : map.map string w64} {L_ok : map.ok L}.
  Context {ext_spec : bedrock2.Semantics.ExtSpec}.
  Local Notation vv := (vv name).
  Local Notation get vm x := (Vm.get vm x).
  Local Notation exec := (@bedrock2.Semantics.exec.exec 64 BW W Mem L ext_spec).

  Fixpoint set_params (vm : Vm.t) (ps : list string) (args : list w64) : Vm.t :=
    match ps, args with
    | p :: ps, a :: args => set_params vm.[vv p <- Vword (jw a)] ps args
    | _, _ => vm
    end.

  Lemma write_params wdb (s : @estate wsw syscall_state (@ep_of_asm_e _ _ _ _ _ _ _ x86_extra syscall_state sc_sem)) ps args :
    size ps = size args ->
    write_vars wdb [seq vi name p | p <- ps] [seq Vword (jw a) | a <- args] s =
      ok (with_vm s (set_params (evm s) ps args)).
  Proof.
    elim: ps args s => [|p ps ih] [|a args] s //=; first by case: s.
    move=> [] /ih h; rewrite /write_var /set_var /=.
    have -> : DB wdb (Vword (jw a)) by case: wdb {h ih}.
    by rewrite !orbT /= h.
  Qed.

  Lemma RL_params l vm ps args l' :
    RL name l vm -> all ok_name ps ->
    map.putmany_of_list_zip ps args l = Some l' -> RL name l' (set_params vm ps args).
  Proof.
    elim: ps args l vm => [|p ps ih] [|a args] l vm //= hl.
    - by move=> _ [<-].
    - move=> /andP [hp hps] h; apply: (ih _ _ _ _ hps h).
      exact: RL_put.
  Qed.

  Lemma RL_empty vm : RL name (map.empty : @map.rep _ _ L) vm.
  Proof. by move=> x v; rewrite coqutil.Map.Interface.map.get_empty. Qed.

  Lemma size_zip_args {ps args} {l l' : @map.rep _ _ L} :
    map.putmany_of_list_zip ps args l = Some l' -> size ps = size args.
  Proof. elim: ps args l => [|p ps ih] [|a args] l //= h; by rewrite (ih _ _ h). Qed.

  Lemma putmany_keep {ps : list string} {args} {l l' : @map.rep _ _ L} {k v} :
    map.putmany_of_list_zip ps args l = Some l' -> map.get l k = Some v ->
    exists w, map.get l' k = Some w.
  Proof.
    elim: ps args l v => [|p ps ih] [|a args] l v //=; first by move=> [<-] h; exists v.
    move=> h hk; apply: (ih _ _ (if String.eqb p k then a else v) h).
    rewrite (@coqutil.Map.Properties.map.get_put_dec _ _ L L_ok String.eqb coqutil.Decidable.String.eqb_spec).
    by case: String.eqb.
  Qed.

  Lemma putmany_keys {ps : list string} {args} {l l' : @map.rep _ _ L} :
    map.putmany_of_list_zip ps args l = Some l' ->
    forall p, List.In p ps -> exists w, map.get l' p = Some w.
  Proof.
    elim: ps args l => [|p ps ih] [|a args] l //= h q [<- | hq].
    - apply: (putmany_keep h); exact: coqutil.Map.Interface.map.get_put_same.
    - exact: ih _ _ h q hq.
  Qed.

  Lemma truncate_args {dc : DirectCall} (ps : list string) (args : list w64) : size ps = size args ->
    mapM2 ErrType dc_truncate_val [seq eval_atype t | t <- [seq aword U64 | _ <- ps]]
      [seq Vword (jw a) | a <- args] = ok [seq Vword (jw a) | a <- args].
  Proof.
    elim: ps args => [|p ps ih] [|a args] //= [] /ih ->.
    by rewrite /dc_truncate_val; case: direct_call => //=; rewrite truncate_word64.
  Qed.

  (** The function theorem: if bedrock2 runs [body] on the arguments to [post], the Jasmin
      function [jfun fi ps jc] of any program [P] is called by Jasmin's [sem_call] on the same
      arguments and returns a memory related to a final bedrock2 memory satisfying [post]; no
      byte outside the bedrock2 domain changes, and the system-call state is unchanged. *)
  Theorem jfun_correct {dc : DirectCall} (P : uprog) ev fn fi ps jc body
      (fenv : @map.rep _ _ bedrock2.Semantics.env) t m args l0 post scs jm :
    get_fundef (p_funcs P) fn = Some (jfun fi ps jc) ->
    ccmd_sp name spillp body = Some jc -> all ok_name ps ->
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
    pose (s1 := with_vm s0 (set_params Vm.init ps args)).
    have hl1 : RL name l0 (evm s1) by apply: RL_params hok hz; apply: RL_empty.
    have [s2 [hr [m' [l' [hpost hl2 hm2 hscs hdf]]]]] :=
      ccmd_sp_correct name name_inj (p_globs P) spillp _ _ _ hc _ _ _ _ hex s1 hl1 hm.
    case: hdf => hdom hfr.
    exists (emem s2); split; last by exists m', l'; split.
    eapply EcallRun with (f := jfun fi ps jc) (s0 := s0) (s1 := s1) (s2 := s2); try reflexivity.
    all: try exact hf.
    all: try (exact: truncate_args).
    all: try (exact: write_params).
    - apply: (run_sem _ P ev erefl); rewrite /jfun /= run_renumber run_cat run_spills; first exact: hr.
      exact: (RL_defined name hl1 (putmany_keys hz)).
    - by rewrite hscs.
  Qed.
End F.
