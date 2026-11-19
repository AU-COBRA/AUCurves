(** * [PsemBig.sem_call] down to x86-64 assembly semantics: the Jasmin-side half of the leaf
    theorems of [BLS12LeafFiat].

    In Jasmin's environment: [PsemBigIff.sem_call_iff] turns a [PsemBig.sem_call] of the leaf
    programs into Jasmin's [psem.sem_call], and [BLS12LeafAsm.asm_of_sem] /
    [BLS12LeafAsm2.asm_of_sem2] (Jasmin's [compile_prog_to_asmP]) take it to assembly.  The
    theorems [bls12_*_asm_big] take as premise the statement that [BLS12LeafFiat.bls12_*_fiat]
    proves in fiat-crypto's environment (at [nosubword] and [indirect_c], the instances of
    Jasmin's compiler theorem); the two statements mention the same constants, so the chain from
    fiat-crypto's [bls12_*_correct] to assembly closes at the meta level, across the two
    environments that cannot be loaded together. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype finfun.
From Jasmin Require Import utils wsize word memory_model low_memory expr psem values varmap
  sem_type arch_decl arch_extra arch_sem x86_decl x86_extra x86_params x86_params_proof
  sem_params_of_arch_extra compiler compiler_proof x86_lowering stack_alloc_proof_1 asm_gen_proof.
From Stdlib Require Import String ZArith.
Require Import bedrock2.Syntax bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.JasminAst.BLS12LeafBodies Bedrock.JasminAst.BLS12LeafSpecs.
Require Import JasminBridge.Ast.Base JasminBridge.Ast.Trans JasminBridge.Ast.Comp
  JasminBridge.Ast.Sim JasminBridge.Ast.Fun JasminBridge.Ast.BLS12Leaves JasminBridge.Ast.BLS12LeafThms
  JasminBridge.Ast.BLS12Leaves2 JasminBridge.Ast.BLS12LeafThms2 JasminBridge.Ast.BLS12LeafAsm
  JasminBridge.Ast.BLS12LeafAsm2 JasminBridge.Ast.PsemBigIff.
Require JasminBridge.Ast.PsemBig.
Set SsrOldRewriteGoalsOrder.
Set Bullet Behavior "Strict Subproofs".
Local Open Scope string_scope.

Section A.
  Context {atoI : arch_toIdent}.
  Context {syscall_state : Type} {sc_sem : syscall.syscall_sem syscall_state}.
  Context {call_conv : calling_convention} {asm_scsem : asm_syscall_sem}.
  #[local] Existing Instance x86_extra.
  #[local] Existing Instance progUnit.

  Variable cparams : compiler_params lowering_options.
  Hypothesis print_uprogP : forall s p, cparams.(print_uprog) s p = p.
  Hypothesis print_sprogP : forall s p, cparams.(print_sprog) s p = p.
  Hypothesis print_linearP : forall s p, cparams.(print_linear) s p = p.

  Variables (name : string -> Ident.ident) (fname : string -> funname)
            (finfo : string -> fun_info) (iinfo : positive -> instr_info) (K : nat).
  Hypothesis name_inj : injective name.
  Hypothesis fname_inj : injective fname.

  Local Notation P := (bls12_leaves_prog name fname finfo iinfo K).
  Local Notation entries := (bls12_leaves_entries fname).

  Variable xp : asm_prog.
  Hypothesis ok_xp : compile_prog_to_asm x86_params cparams entries P = ok xp.

  Local Notation bmem := (@coqutil.Map.Interface.map.rep _ _ BasicC64Semantics.mem).
  Local Notation jargs xs := [seq Vword (jw a) | a <- xs].
  Local Notation xasmmem := (@asmmem syscall_state sc_sem _ _ _ _ _ _ (@_asm _ _ _ _ _ _ _ x86_extra)).
  Local Notation big_call := (PsemBig.sem_call (dc := indirect_c) (wsw := nosubword) P tt).

  Lemma asm_of_big fn va m m' (xm : xasmmem) :
    fn \in entries ->
    big_call (asm_scs xm) m fn va (asm_scs xm) m' [::] ->
    asm_call_ok name fname finfo iinfo K xp fn va m m' xm.
  Proof. by move=> hin /sem_call_iff hcall; exact: (asm_of_sem cparams print_uprogP print_sprogP print_linearP name fname finfo iinfo K xp ok_xp _ _ _ _ _ hin) hcall. Qed.

  Theorem bls12_add_asm_big :
    (forall ev scs jm pout px py x y out Rr m, binop_pre pout px py x y out Rr m -> mem_rel m jm ->
      exists jm', PsemBig.sem_call (dc := indirect_c) (wsw := nosubword) P ev scs jm (fname "bls12_add")
        (jargs [:: pout; px; py]) scs jm' [::] /\
        jasmin_post m jm jm' (result_post pout (F.add (eval_w x) (eval_w y)) Rr)) ->
    forall (xm : xasmmem) jm pout px py x y out Rr (m : bmem),
      binop_pre pout px py x y out Rr m -> mem_rel m jm ->
      exists jm', jasmin_post m jm jm' (result_post pout (F.add (eval_w x) (eval_w y)) Rr) /\
        asm_call_ok name fname finfo iinfo K xp (fname "bls12_add") (jargs [:: pout; px; py]) jm jm' xm.
  Proof.
    move=> H xm jm pout px py x y out Rr m hpre hm.
    have [jm' [hcall hpost]] := H tt (asm_scs xm) jm pout px py x y out Rr m hpre hm.
    exists jm'; split => //; apply: asm_of_big; last exact: hcall.
    by rewrite /bls12_leaves_entries !inE eqxx ?orbT.
  Qed.

  Theorem bls12_sub_asm_big :
    (forall ev scs jm pout px py x y out Rr m, binop_pre pout px py x y out Rr m -> mem_rel m jm ->
      exists jm', PsemBig.sem_call (dc := indirect_c) (wsw := nosubword) P ev scs jm (fname "bls12_sub")
        (jargs [:: pout; px; py]) scs jm' [::] /\
        jasmin_post m jm jm' (result_post pout (F.sub (eval_w x) (eval_w y)) Rr)) ->
    forall (xm : xasmmem) jm pout px py x y out Rr (m : bmem),
      binop_pre pout px py x y out Rr m -> mem_rel m jm ->
      exists jm', jasmin_post m jm jm' (result_post pout (F.sub (eval_w x) (eval_w y)) Rr) /\
        asm_call_ok name fname finfo iinfo K xp (fname "bls12_sub") (jargs [:: pout; px; py]) jm jm' xm.
  Proof.
    move=> H xm jm pout px py x y out Rr m hpre hm.
    have [jm' [hcall hpost]] := H tt (asm_scs xm) jm pout px py x y out Rr m hpre hm.
    exists jm'; split => //; apply: asm_of_big; last exact: hcall.
    by rewrite /bls12_leaves_entries !inE eqxx ?orbT.
  Qed.

  Theorem bls12_mul_asm_big :
    (forall ev scs jm pout px py x y out Rr m, binop_pre pout px py x y out Rr m -> mem_rel m jm ->
      exists jm', PsemBig.sem_call (dc := indirect_c) (wsw := nosubword) P ev scs jm (fname "bls12_mul")
        (jargs [:: pout; px; py]) scs jm' [::] /\
        jasmin_post m jm jm' (result_post pout (F.mul (eval_w x) (eval_w y)) Rr)) ->
    forall (xm : xasmmem) jm pout px py x y out Rr (m : bmem),
      binop_pre pout px py x y out Rr m -> mem_rel m jm ->
      exists jm', jasmin_post m jm jm' (result_post pout (F.mul (eval_w x) (eval_w y)) Rr) /\
        asm_call_ok name fname finfo iinfo K xp (fname "bls12_mul") (jargs [:: pout; px; py]) jm jm' xm.
  Proof.
    move=> H xm jm pout px py x y out Rr m hpre hm.
    have [jm' [hcall hpost]] := H tt (asm_scs xm) jm pout px py x y out Rr m hpre hm.
    exists jm'; split => //; apply: asm_of_big; last exact: hcall.
    by rewrite /bls12_leaves_entries !inE eqxx ?orbT.
  Qed.

  Theorem bls12_square_asm_big :
    (forall ev scs jm pout px x out Rr m, unop_pre pout px x out Rr m -> mem_rel m jm ->
      exists jm', PsemBig.sem_call (dc := indirect_c) (wsw := nosubword) P ev scs jm (fname "bls12_square")
        (jargs [:: pout; px]) scs jm' [::] /\
        jasmin_post m jm jm' (result_post pout (F.pow (eval_w x) 2) Rr)) ->
    forall (xm : xasmmem) jm pout px x out Rr (m : bmem),
      unop_pre pout px x out Rr m -> mem_rel m jm ->
      exists jm', jasmin_post m jm jm' (result_post pout (F.pow (eval_w x) 2) Rr) /\
        asm_call_ok name fname finfo iinfo K xp (fname "bls12_square") (jargs [:: pout; px]) jm jm' xm.
  Proof.
    move=> H xm jm pout px x out Rr m hpre hm.
    have [jm' [hcall hpost]] := H tt (asm_scs xm) jm pout px x out Rr m hpre hm.
    exists jm'; split => //; apply: asm_of_big; last exact: hcall.
    by rewrite /bls12_leaves_entries !inE eqxx ?orbT.
  Qed.
End A.

Section A2.
  Context {atoI : arch_toIdent}.
  Context {syscall_state : Type} {sc_sem : syscall.syscall_sem syscall_state}.
  Context {call_conv : calling_convention} {asm_scsem : asm_syscall_sem}.
  #[local] Existing Instance x86_extra.
  #[local] Existing Instance progUnit.

  Variable cparams : compiler_params lowering_options.
  Hypothesis print_uprogP : forall s p, cparams.(print_uprog) s p = p.
  Hypothesis print_sprogP : forall s p, cparams.(print_sprog) s p = p.
  Hypothesis print_linearP : forall s p, cparams.(print_linear) s p = p.

  Variables (name : string -> Ident.ident) (cfn : Ident.ident) (fname : string -> funname)
            (finfo : string -> fun_info) (iinfo : positive -> instr_info) (K : nat).
  Hypothesis name_inj : injective name.
  Hypothesis fname_inj : injective fname.

  Local Notation P := (bls12_leaves2_prog name cfn fname finfo iinfo K).
  Local Notation entries := (bls12_leaves_entries fname).

  Variable xp : asm_prog.
  Hypothesis ok_xp : compile_prog_to_asm x86_params cparams entries P = ok xp.

  Local Notation bmem := (@coqutil.Map.Interface.map.rep _ _ BasicC64Semantics.mem).
  Local Notation jargs xs := [seq Vword (jw a) | a <- xs].
  Local Notation xasmmem := (@asmmem syscall_state sc_sem _ _ _ _ _ _ (@_asm _ _ _ _ _ _ _ x86_extra)).
  Local Notation big_call := (PsemBig.sem_call (dc := indirect_c) (wsw := nosubword) P tt).

  Lemma asm_of_big2 fn va m m' (xm : xasmmem) :
    fn \in entries ->
    big_call (asm_scs xm) m fn va (asm_scs xm) m' [::] ->
    asm_call_ok2 name cfn fname finfo iinfo K xp fn va m m' xm.
  Proof. by move=> hin /sem_call_iff hcall; exact: (asm_of_sem2 cparams print_uprogP print_sprogP print_linearP name cfn fname finfo iinfo K xp ok_xp _ _ _ _ _ hin) hcall. Qed.

  Theorem bls12_add_asm_big2 :
    (forall ev scs jm pout px py x y out Rr m, binop_pre pout px py x y out Rr m -> mem_rel m jm ->
      exists jm', PsemBig.sem_call (dc := indirect_c) (wsw := nosubword) P ev scs jm (fname "bls12_add")
        (jargs [:: pout; px; py]) scs jm' [::] /\
        jasmin_post m jm jm' (result_post pout (F.add (eval_w x) (eval_w y)) Rr)) ->
    forall (xm : xasmmem) jm pout px py x y out Rr (m : bmem),
      binop_pre pout px py x y out Rr m -> mem_rel m jm ->
      exists jm', jasmin_post m jm jm' (result_post pout (F.add (eval_w x) (eval_w y)) Rr) /\
        asm_call_ok2 name cfn fname finfo iinfo K xp (fname "bls12_add") (jargs [:: pout; px; py]) jm jm' xm.
  Proof.
    move=> H xm jm pout px py x y out Rr m hpre hm.
    have [jm' [hcall hpost]] := H tt (asm_scs xm) jm pout px py x y out Rr m hpre hm.
    exists jm'; split => //; apply: asm_of_big2; last exact: hcall.
    by rewrite /bls12_leaves_entries !inE eqxx ?orbT.
  Qed.

  Theorem bls12_sub_asm_big2 :
    (forall ev scs jm pout px py x y out Rr m, binop_pre pout px py x y out Rr m -> mem_rel m jm ->
      exists jm', PsemBig.sem_call (dc := indirect_c) (wsw := nosubword) P ev scs jm (fname "bls12_sub")
        (jargs [:: pout; px; py]) scs jm' [::] /\
        jasmin_post m jm jm' (result_post pout (F.sub (eval_w x) (eval_w y)) Rr)) ->
    forall (xm : xasmmem) jm pout px py x y out Rr (m : bmem),
      binop_pre pout px py x y out Rr m -> mem_rel m jm ->
      exists jm', jasmin_post m jm jm' (result_post pout (F.sub (eval_w x) (eval_w y)) Rr) /\
        asm_call_ok2 name cfn fname finfo iinfo K xp (fname "bls12_sub") (jargs [:: pout; px; py]) jm jm' xm.
  Proof.
    move=> H xm jm pout px py x y out Rr m hpre hm.
    have [jm' [hcall hpost]] := H tt (asm_scs xm) jm pout px py x y out Rr m hpre hm.
    exists jm'; split => //; apply: asm_of_big2; last exact: hcall.
    by rewrite /bls12_leaves_entries !inE eqxx ?orbT.
  Qed.

  Theorem bls12_mul_asm_big2 :
    (forall ev scs jm pout px py x y out Rr m, binop_pre pout px py x y out Rr m -> mem_rel m jm ->
      exists jm', PsemBig.sem_call (dc := indirect_c) (wsw := nosubword) P ev scs jm (fname "bls12_mul")
        (jargs [:: pout; px; py]) scs jm' [::] /\
        jasmin_post m jm jm' (result_post pout (F.mul (eval_w x) (eval_w y)) Rr)) ->
    forall (xm : xasmmem) jm pout px py x y out Rr (m : bmem),
      binop_pre pout px py x y out Rr m -> mem_rel m jm ->
      exists jm', jasmin_post m jm jm' (result_post pout (F.mul (eval_w x) (eval_w y)) Rr) /\
        asm_call_ok2 name cfn fname finfo iinfo K xp (fname "bls12_mul") (jargs [:: pout; px; py]) jm jm' xm.
  Proof.
    move=> H xm jm pout px py x y out Rr m hpre hm.
    have [jm' [hcall hpost]] := H tt (asm_scs xm) jm pout px py x y out Rr m hpre hm.
    exists jm'; split => //; apply: asm_of_big2; last exact: hcall.
    by rewrite /bls12_leaves_entries !inE eqxx ?orbT.
  Qed.

  Theorem bls12_square_asm_big2 :
    (forall ev scs jm pout px x out Rr m, unop_pre pout px x out Rr m -> mem_rel m jm ->
      exists jm', PsemBig.sem_call (dc := indirect_c) (wsw := nosubword) P ev scs jm (fname "bls12_square")
        (jargs [:: pout; px]) scs jm' [::] /\
        jasmin_post m jm jm' (result_post pout (F.pow (eval_w x) 2) Rr)) ->
    forall (xm : xasmmem) jm pout px x out Rr (m : bmem),
      unop_pre pout px x out Rr m -> mem_rel m jm ->
      exists jm', jasmin_post m jm jm' (result_post pout (F.pow (eval_w x) 2) Rr) /\
        asm_call_ok2 name cfn fname finfo iinfo K xp (fname "bls12_square") (jargs [:: pout; px]) jm jm' xm.
  Proof.
    move=> H xm jm pout px x out Rr m hpre hm.
    have [jm' [hcall hpost]] := H tt (asm_scs xm) jm pout px x out Rr m hpre hm.
    exists jm'; split => //; apply: asm_of_big2; last exact: hcall.
    by rewrite /bls12_leaves_entries !inE eqxx ?orbT.
  Qed.
End A2.
