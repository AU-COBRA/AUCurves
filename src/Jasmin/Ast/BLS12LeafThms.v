(** * The BLS12-381 Fp leaves: from fiat-crypto's contracts to Jasmin's semantics. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Jasmin Require Import utils wsize word memory_model low_memory expr psem values varmap
  sem_type arch_extra x86_extra sem_params_of_arch_extra.
From Stdlib Require Import String ZArith.
Require Import bedrock2.Syntax bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.JasminAst.BLS12LeafBodies Bedrock.JasminAst.BLS12LeafSpecs.
Require Import JasminBridge.Ast.Base JasminBridge.Ast.Trans JasminBridge.Ast.Comp
  JasminBridge.Ast.Sim JasminBridge.Ast.Fun JasminBridge.Ast.BLS12Leaves JasminBridge.Ast.PsemBigIff.
Require Export JasminBridge.Ast.BLS12LeafBig.
Set SsrOldRewriteGoalsOrder.
Set Bullet Behavior "Strict Subproofs".
Local Open Scope string_scope.

Section T.
  Context {atoI : arch_toIdent}.
  Context {syscall_state : Type} {sc_sem : syscall.syscall_sem syscall_state}.
  #[local] Existing Instance x86_extra.
  #[local] Existing Instance progUnit.
  Context {wsw : WithSubWord} {dc : DirectCall}.
  Variables (name : string -> Ident.ident) (fname : string -> funname)
            (finfo : string -> fun_info) (iinfo : positive -> instr_info) (K : nat).
  Hypothesis name_inj : injective name.
  Hypothesis fname_inj : injective fname.

  Local Notation P := (bls12_leaves_prog name fname finfo iinfo K).

  (** [fname_neq], [get_add], [get_sub], [get_mul], [get_square] and [jasmin_post] are in
      [BLS12LeafBig]; the theorems below are its theorems for [psem.sem_call]. *)

  Local Notation leafd fn ps b :=
    (jfun name iinfo (spill_choice K ps b) (finfo fn) ps (leaf_code name K ps b)).

  Local Notation jargs xs := [seq Vword (jw a) | a <- xs].

  Lemma binop_jasmin fn body model :
    get_fundef (p_funcs P) (fname fn) = Some (leafd fn params3 body) ->
    ccmd_sp name (spill_choice K params3 body) body = Some (leaf_code name K params3 body) ->
    binop_contract body model ->
    forall ev scs jm pout px py x y out Rr m,
      binop_pre pout px py x y out Rr m -> mem_rel m jm ->
      exists jm', sem_call P ev scs jm (fname fn) (jargs [:: pout; px; py]) scs jm' [::] /\
        jasmin_post m jm jm' (result_post pout (model (eval_w x) (eval_w y)) Rr).
  Proof.
    move=> hget hc H ev scs jm pout px py x y out Rr m hpre hm.
    have [jm' [hcall hpost]] := binop_big name fname finfo iinfo K name_inj fn body model hget hc H ev scs jm
      pout px py x y out Rr m hpre hm.
    by exists jm'; split => //; apply/sem_call_iff.
  Qed.

  Lemma unop_jasmin fn body model :
    get_fundef (p_funcs P) (fname fn) = Some (leafd fn params2 body) ->
    ccmd_sp name (spill_choice K params2 body) body = Some (leaf_code name K params2 body) ->
    unop_contract body model ->
    forall ev scs jm pout px x out Rr m,
      unop_pre pout px x out Rr m -> mem_rel m jm ->
      exists jm', sem_call P ev scs jm (fname fn) (jargs [:: pout; px]) scs jm' [::] /\
        jasmin_post m jm jm' (result_post pout (model (eval_w x)) Rr).
  Proof.
    move=> hget hc H ev scs jm pout px x out Rr m hpre hm.
    have [jm' [hcall hpost]] := unop_big name fname finfo iinfo K name_inj fn body model hget hc H ev scs jm
      pout px x out Rr m hpre hm.
    by exists jm'; split => //; apply/sem_call_iff.
  Qed.

  (** The four leaves.  Premise: fiat-crypto's contract of the leaf, as a bedrock2 execution
      ([BLS12LeafSpecsProof] proves it from bls12_*_correct in fiat-crypto's environment). *)
  Theorem bls12_add_jasmin : bls12_add_contract ->
    forall ev scs jm pout px py x y out Rr m, binop_pre pout px py x y out Rr m -> mem_rel m jm ->
    exists jm', sem_call P ev scs jm (fname "bls12_add") (jargs [:: pout; px; py]) scs jm' [::] /\
      jasmin_post m jm jm' (result_post pout (F.add (eval_w x) (eval_w y)) Rr).
  Proof. exact: binop_jasmin (get_add name fname finfo iinfo K) (ccmd_add name K). Qed.

  Theorem bls12_sub_jasmin : bls12_sub_contract ->
    forall ev scs jm pout px py x y out Rr m, binop_pre pout px py x y out Rr m -> mem_rel m jm ->
    exists jm', sem_call P ev scs jm (fname "bls12_sub") (jargs [:: pout; px; py]) scs jm' [::] /\
      jasmin_post m jm jm' (result_post pout (F.sub (eval_w x) (eval_w y)) Rr).
  Proof. exact: binop_jasmin (get_sub name fname finfo iinfo K fname_inj) (ccmd_sub name K). Qed.

  Theorem bls12_mul_jasmin : bls12_mul_contract ->
    forall ev scs jm pout px py x y out Rr m, binop_pre pout px py x y out Rr m -> mem_rel m jm ->
    exists jm', sem_call P ev scs jm (fname "bls12_mul") (jargs [:: pout; px; py]) scs jm' [::] /\
      jasmin_post m jm jm' (result_post pout (F.mul (eval_w x) (eval_w y)) Rr).
  Proof. exact: binop_jasmin (get_mul name fname finfo iinfo K fname_inj) (ccmd_mul name K). Qed.

  Theorem bls12_square_jasmin : bls12_square_contract ->
    forall ev scs jm pout px x out Rr m, unop_pre pout px x out Rr m -> mem_rel m jm ->
    exists jm', sem_call P ev scs jm (fname "bls12_square") (jargs [:: pout; px]) scs jm' [::] /\
      jasmin_post m jm jm' (result_post pout (F.pow (eval_w x) 2) Rr).
  Proof. exact: unop_jasmin (get_square name fname finfo iinfo K fname_inj) (ccmd_square name K). Qed.
End T.
