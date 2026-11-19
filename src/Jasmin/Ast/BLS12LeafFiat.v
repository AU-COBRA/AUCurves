(** * The BLS12-381 Fp leaves: from fiat-crypto's theorems to Jasmin's big-step semantics, in one
    Rocq environment.

    This file loads fiat-crypto's bedrock2 synthesis of the BLS12-381 field
    ([Bedrock.Field.Synthesis.Examples.bls12_prime], through [BLS12LeafSpecsProof]) together with
    the bedrock2 -> Jasmin translation and [PsemBig], the copy of Jasmin's big-step semantics
    without ITree (Jasmin's [psem] cannot be loaded here: universe inconsistency between ITree's
    template universes and fiat-crypto's [Morphisms.Proper]).  The theorems carry no contract
    premise: [bls12_*_contract_proof] derive the contracts from fiat-crypto's [bls12_*_correct].

    The remaining step, [PsemBig.sem_call] -> x86-64 assembly, is [BLS12LeafAsmBig] in Jasmin's
    environment ([PsemBigIff.sem_call_iff] and Jasmin's [compile_prog_to_asmP]).  Both files
    refer to the same constant [JasminBridge.Ast.PsemBig.sem_call]. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Jasmin Require Import utils wsize word memory_model low_memory expr psem_defs psem_core values
  varmap sem_type arch_extra x86_extra sem_params_of_arch_extra.
From Stdlib Require Import String ZArith.
Require Import bedrock2.Syntax bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.JasminAst.BLS12LeafBodies Bedrock.JasminAst.BLS12LeafSpecs.
Require Bedrock.JasminAst.BLS12LeafSpecsProof.
Require Import JasminBridge.Ast.PsemBig JasminBridge.Ast.Base JasminBridge.Ast.Trans
  JasminBridge.Ast.Comp JasminBridge.Ast.Sim JasminBridge.Ast.Fun JasminBridge.Ast.BLS12Leaves
  JasminBridge.Ast.BLS12Leaves2 JasminBridge.Ast.BLS12LeafBig JasminBridge.Ast.BLS12LeafBig2.
Set SsrOldRewriteGoalsOrder.
Set Bullet Behavior "Strict Subproofs".
Local Open Scope string_scope.

Module SP := Bedrock.JasminAst.BLS12LeafSpecsProof.

Section T.
  Context {atoI : arch_toIdent}.
  Context {syscall_state : Type} {sc_sem : syscall.syscall_sem syscall_state}.
  #[local] Existing Instance x86_extra.
  #[local] Existing Instance progUnit.
  Context {wsw : WithSubWord} {dc : DirectCall}.
  Variables (name : string -> Ident.ident) (cfn : Ident.ident) (fname : string -> funname)
            (finfo : string -> fun_info) (iinfo : positive -> instr_info) (K : nat).
  Hypothesis name_inj : injective name.
  Hypothesis fname_inj : injective fname.

  Local Notation jargs xs := [seq Vword (jw a) | a <- xs].
  Local Notation P := (bls12_leaves_prog name fname finfo iinfo K).
  Local Notation P2 := (bls12_leaves2_prog name cfn fname finfo iinfo K).

  (** ** [BLS12Leaves]: the leaves translated by [Comp.ccmd_sp]. *)
  Theorem bls12_add_fiat :
    forall ev scs jm pout px py x y out Rr m, binop_pre pout px py x y out Rr m -> mem_rel m jm ->
    exists jm', PsemBig.sem_call P ev scs jm (fname "bls12_add") (jargs [:: pout; px; py]) scs jm' [::] /\
      jasmin_post m jm jm' (result_post pout (F.add (eval_w x) (eval_w y)) Rr).
  Proof. exact: bls12_add_big name_inj SP.bls12_add_contract_proof. Qed.

  Theorem bls12_sub_fiat :
    forall ev scs jm pout px py x y out Rr m, binop_pre pout px py x y out Rr m -> mem_rel m jm ->
    exists jm', PsemBig.sem_call P ev scs jm (fname "bls12_sub") (jargs [:: pout; px; py]) scs jm' [::] /\
      jasmin_post m jm jm' (result_post pout (F.sub (eval_w x) (eval_w y)) Rr).
  Proof. exact: bls12_sub_big name_inj fname_inj SP.bls12_sub_contract_proof. Qed.

  Theorem bls12_mul_fiat :
    forall ev scs jm pout px py x y out Rr m, binop_pre pout px py x y out Rr m -> mem_rel m jm ->
    exists jm', PsemBig.sem_call P ev scs jm (fname "bls12_mul") (jargs [:: pout; px; py]) scs jm' [::] /\
      jasmin_post m jm jm' (result_post pout (F.mul (eval_w x) (eval_w y)) Rr).
  Proof. exact: bls12_mul_big name_inj fname_inj SP.bls12_mul_contract_proof. Qed.

  Theorem bls12_square_fiat :
    forall ev scs jm pout px x out Rr m, unop_pre pout px x out Rr m -> mem_rel m jm ->
    exists jm', PsemBig.sem_call P ev scs jm (fname "bls12_square") (jargs [:: pout; px]) scs jm' [::] /\
      jasmin_post m jm jm' (result_post pout (F.pow (eval_w x) 2) Rr).
  Proof. exact: bls12_square_big name_inj fname_inj SP.bls12_square_contract_proof. Qed.

  (** ** [BLS12Leaves2]: the optimised leaves ([Carry.xcmd], else [Comp.ccmd_sp]). *)
  Theorem bls12_add_fiat2 :
    forall ev scs jm pout px py x y out Rr m, binop_pre pout px py x y out Rr m -> mem_rel m jm ->
    exists jm', PsemBig.sem_call P2 ev scs jm (fname "bls12_add") (jargs [:: pout; px; py]) scs jm' [::] /\
      jasmin_post m jm jm' (result_post pout (F.add (eval_w x) (eval_w y)) Rr).
  Proof. exact: bls12_add_big2 name_inj SP.bls12_add_contract_proof. Qed.

  Theorem bls12_sub_fiat2 :
    forall ev scs jm pout px py x y out Rr m, binop_pre pout px py x y out Rr m -> mem_rel m jm ->
    exists jm', PsemBig.sem_call P2 ev scs jm (fname "bls12_sub") (jargs [:: pout; px; py]) scs jm' [::] /\
      jasmin_post m jm jm' (result_post pout (F.sub (eval_w x) (eval_w y)) Rr).
  Proof. exact: bls12_sub_big2 name_inj fname_inj SP.bls12_sub_contract_proof. Qed.

  Theorem bls12_mul_fiat2 :
    forall ev scs jm pout px py x y out Rr m, binop_pre pout px py x y out Rr m -> mem_rel m jm ->
    exists jm', PsemBig.sem_call P2 ev scs jm (fname "bls12_mul") (jargs [:: pout; px; py]) scs jm' [::] /\
      jasmin_post m jm jm' (result_post pout (F.mul (eval_w x) (eval_w y)) Rr).
  Proof. exact: bls12_mul_big2 name_inj fname_inj SP.bls12_mul_contract_proof. Qed.

  Theorem bls12_square_fiat2 :
    forall ev scs jm pout px x out Rr m, unop_pre pout px x out Rr m -> mem_rel m jm ->
    exists jm', PsemBig.sem_call P2 ev scs jm (fname "bls12_square") (jargs [:: pout; px]) scs jm' [::] /\
      jasmin_post m jm jm' (result_post pout (F.pow (eval_w x) 2) Rr).
  Proof. exact: bls12_square_big2 name_inj fname_inj SP.bls12_square_contract_proof. Qed.
End T.
