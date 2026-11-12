(** * The optimised BLS12-381 Fp leaves ([BLS12Leaves2]) down to x86-64 assembly semantics.

    Composition of [BLS12LeafThms2] (contract -> Jasmin source semantics) with Jasmin's
    compiler-correctness theorem [compiler_proof.compile_prog_to_asmP] (source semantics ->
    assembly semantics of the compiled program).  The compiler parameters [cparams] are the
    oracles the OCaml driver supplies (register allocation, stack allocation, ...): the theorem
    holds for every choice, given that its printing hooks are identities (as Jasmin's own
    theorem requires).  [xp] is any successful result of the extracted compiler. *)
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
  JasminBridge.Ast.BLS12Leaves2 JasminBridge.Ast.BLS12LeafThms2 JasminBridge.Ast.BLS12LeafAsm.
Set SsrOldRewriteGoalsOrder.
Set Bullet Behavior "Strict Subproofs".
Local Open Scope string_scope.

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
            (finfo : string -> fun_info) (iinfo : positive -> instr_info) (budget : nat).
  Hypothesis name_inj : injective name.
  Hypothesis fname_inj : injective fname.

  Local Notation P := (bls12_leaves2_prog name cfn fname finfo iinfo budget).
  Local Notation bls12_leaves_entries := (bls12_leaves_entries fname).

  Variable xp : asm_prog.
  Hypothesis ok_xp : compile_prog_to_asm x86_params cparams bls12_leaves_entries P = ok xp.

  Local Notation bmem := (@coqutil.Map.Interface.map.rep _ _ BasicC64Semantics.mem).
  Local Notation jargs xs := [seq Vword (jw a) | a <- xs].
  Local Notation xasmmem := (@asmmem syscall_state sc_sem _ _ _ _ _ _ (@_asm _ _ _ _ _ _ _ x86_extra)).

  (** The assembly-level conclusion of [compile_prog_to_asmP] for a call of [fn] on [va] from
      Jasmin memory [m] that returns memory [m'], no results. *)
  Definition asm_call_ok2 (fn : funname) (va : seq value) (m m' : low_memory.mem) (xm : xasmmem) : Prop :=
    forall mi,
      mem_agreement_with_ghost m (asm_mem xm) (asm_rip xm) (asm_globs xp) mi ->
      enough_stack_space xp fn (top_stack m) (asm_mem xm) ->
      exists xd : asm_fundef,
        [/\ get_fundef (asm_funcs xp) fn = Some xd, asm_fd_export xd &
            asm_reg xm ad_rsp = top_stack m ->
            wf_args (Z.of_nat (size (asm_globs xp))) (asm_rip xm) m mi
              (get_wptrs P fn) (get_asm_align_args xp fn) va (get_typed_reg_values xm (asm_fd_arg xd)) ->
            Forall3 (value_uincl_or_in_mem (asm_mem xm)) (get_wptrs P fn) va
              (get_typed_reg_values xm (asm_fd_arg xd)) ->
            exists xm', asmsem_exportcall xp fn xm xm' /\
              mem_agreement m' (asm_mem xm') (asm_rip xm') (asm_globs xp) /\
              asm_scs xm' = asm_scs xm].

  Lemma asm_of_sem2 fn va m m' (xm : xasmmem) :
    fn \in bls12_leaves_entries ->
    psem.sem_call (dc := indirect_c) (wsw := nosubword) P tt (asm_scs xm) m fn va (asm_scs xm) m' [::] ->
    asm_call_ok2 fn va m m' xm.
  Proof.
    move=> hin hcall mi hmi hstk.
    have [xd [hget hexp hasm]] :=
      compile_prog_to_asmP x86_h_params print_uprogP print_sprogP print_linearP ok_xp hin hcall hmi hstk.
    exists xd; split => // hrsp hwf hincl.
    have [xm' [hexec hagree hscs _ _]] := hasm erefl hrsp hwf hincl.
    by exists xm'.
  Qed.

  Theorem bls12_mul_asm2 : bls12_mul_contract ->
    forall (xm : xasmmem) jm pout px py x y out Rr (m : bmem),
      binop_pre pout px py x y out Rr m -> mem_rel m jm ->
      exists jm', jasmin_post m jm jm' (result_post pout (F.mul (eval_w x) (eval_w y)) Rr) /\
        asm_call_ok2 (fname "bls12_mul") (jargs [:: pout; px; py]) jm jm' xm.
  Proof.
    move=> H xm jm pout px py x y out Rr m hpre hm.
    have [jm' [hcall hpost]] :=
      bls12_mul_jasmin2 (wsw := nosubword) (dc := indirect_c) name cfn fname finfo iinfo budget name_inj fname_inj
        H tt (asm_scs xm) jm pout px py x y out Rr m hpre hm.
    exists jm'; split => //; apply: asm_of_sem2; last exact: hcall.
    by rewrite /bls12_leaves_entries !inE eqxx ?orbT.
  Qed.

  Theorem bls12_square_asm2 : bls12_square_contract ->
    forall (xm : xasmmem) jm pout px x out Rr (m : bmem),
      unop_pre pout px x out Rr m -> mem_rel m jm ->
      exists jm', jasmin_post m jm jm' (result_post pout (F.pow (eval_w x) 2) Rr) /\
        asm_call_ok2 (fname "bls12_square") (jargs [:: pout; px]) jm jm' xm.
  Proof.
    move=> H xm jm pout px x out Rr m hpre hm.
    have [jm' [hcall hpost]] :=
      bls12_square_jasmin2 (wsw := nosubword) (dc := indirect_c) name cfn fname finfo iinfo budget name_inj fname_inj
        H tt (asm_scs xm) jm pout px x out Rr m hpre hm.
    exists jm'; split => //; apply: asm_of_sem2; last exact: hcall.
    by rewrite /bls12_leaves_entries !inE eqxx ?orbT.
  Qed.

  Theorem bls12_add_asm2 : bls12_add_contract ->
    forall (xm : xasmmem) jm pout px py x y out Rr (m : bmem),
      binop_pre pout px py x y out Rr m -> mem_rel m jm ->
      exists jm', jasmin_post m jm jm' (result_post pout (F.add (eval_w x) (eval_w y)) Rr) /\
        asm_call_ok2 (fname "bls12_add") (jargs [:: pout; px; py]) jm jm' xm.
  Proof.
    move=> H xm jm pout px py x y out Rr m hpre hm.
    have [jm' [hcall hpost]] :=
      bls12_add_jasmin2 (wsw := nosubword) (dc := indirect_c) name cfn fname finfo iinfo budget name_inj
        H tt (asm_scs xm) jm pout px py x y out Rr m hpre hm.
    exists jm'; split => //; apply: asm_of_sem2; last exact: hcall.
    by rewrite /bls12_leaves_entries !inE eqxx ?orbT.
  Qed.

  Theorem bls12_sub_asm2 : bls12_sub_contract ->
    forall (xm : xasmmem) jm pout px py x y out Rr (m : bmem),
      binop_pre pout px py x y out Rr m -> mem_rel m jm ->
      exists jm', jasmin_post m jm jm' (result_post pout (F.sub (eval_w x) (eval_w y)) Rr) /\
        asm_call_ok2 (fname "bls12_sub") (jargs [:: pout; px; py]) jm jm' xm.
  Proof.
    move=> H xm jm pout px py x y out Rr m hpre hm.
    have [jm' [hcall hpost]] :=
      bls12_sub_jasmin2 (wsw := nosubword) (dc := indirect_c) name cfn fname finfo iinfo budget name_inj fname_inj
        H tt (asm_scs xm) jm pout px py x y out Rr m hpre hm.
    exists jm'; split => //; apply: asm_of_sem2; last exact: hcall.
    by rewrite /bls12_leaves_entries !inE eqxx ?orbT.
  Qed.
End A2.
