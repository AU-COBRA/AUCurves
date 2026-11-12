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
  JasminBridge.Ast.Sim JasminBridge.Ast.Fun JasminBridge.Ast.BLS12Leaves.
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

  Lemma fname_neq a b : String.eqb a b = false -> (fname a == fname b) = false.
  Proof. by move=> h; apply/eqP => /fname_inj e; move: h; rewrite e String.eqb_refl. Qed.

  Local Notation leafd fn ps b :=
    (jfun name iinfo (spill_choice K ps b) (finfo fn) ps (leaf_code name K ps b)).

  Lemma get_add : get_fundef (p_funcs P) (fname "bls12_add") = Some (leafd "bls12_add" params3 bls12_add_body).
  Proof. by rewrite /get_fundef /= eqxx. Qed.
  Lemma get_sub : get_fundef (p_funcs P) (fname "bls12_sub") = Some (leafd "bls12_sub" params3 bls12_sub_body).
  Proof. by rewrite /get_fundef /= fname_neq // eqxx. Qed.
  Lemma get_mul : get_fundef (p_funcs P) (fname "bls12_mul") = Some (leafd "bls12_mul" params3 bls12_mul_body).
  Proof. by rewrite /get_fundef /= fname_neq // fname_neq // eqxx. Qed.
  Lemma get_square : get_fundef (p_funcs P) (fname "bls12_square") = Some (leafd "bls12_square" params2 bls12_square_body).
  Proof. by rewrite /get_fundef /= fname_neq // fname_neq // fname_neq // eqxx. Qed.

  Local Notation jargs xs := [seq Vword (jw a) | a <- xs].

  (** What the Jasmin call establishes: the final Jasmin memory is related to a bedrock2 memory
      satisfying the contract's postcondition, and no byte outside the bedrock2 domain changed. *)
  Local Notation bmem := (@coqutil.Map.Interface.map.rep _ _ BasicC64Semantics.mem).
  Definition jasmin_post (m : bmem) (jm jm' : low_memory.mem) (Q : bmem -> Prop) : Prop :=
    exists m', [/\ Q m', mem_rel m' jm' &
      forall p, outside m p -> read jm' Aligned p U8 = read jm Aligned p U8].

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
    have [fenv [l [hl hex]]] := H pout px py x y out Rr nil m hpre.
    have [jm' [hcall [m' [l' [[_ hpost] hm' _ hfr]]]]] :=
      jfun_correct name name_inj iinfo _ P ev _ _ _ _ _ fenv _ _ _ _ _ scs jm
        hget hc isT hl hex hm.
    by exists jm'; split => //; exists m'; split.
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
    have [fenv [l [hl hex]]] := H pout px x out Rr nil m hpre.
    have [jm' [hcall [m' [l' [[_ hpost] hm' _ hfr]]]]] :=
      jfun_correct name name_inj iinfo _ P ev _ _ _ _ _ fenv _ _ _ _ _ scs jm
        hget hc isT hl hex hm.
    by exists jm'; split => //; exists m'; split.
  Qed.

  (** The four leaves.  Premise: fiat-crypto's contract of the leaf, as a bedrock2 execution
      ([BLS12LeafSpecsProof] proves it from bls12_*_correct in fiat-crypto's environment). *)
  Theorem bls12_add_jasmin : bls12_add_contract ->
    forall ev scs jm pout px py x y out Rr m, binop_pre pout px py x y out Rr m -> mem_rel m jm ->
    exists jm', sem_call P ev scs jm (fname "bls12_add") (jargs [:: pout; px; py]) scs jm' [::] /\
      jasmin_post m jm jm' (result_post pout (F.add (eval_w x) (eval_w y)) Rr).
  Proof. exact: binop_jasmin get_add (ccmd_add name K). Qed.

  Theorem bls12_sub_jasmin : bls12_sub_contract ->
    forall ev scs jm pout px py x y out Rr m, binop_pre pout px py x y out Rr m -> mem_rel m jm ->
    exists jm', sem_call P ev scs jm (fname "bls12_sub") (jargs [:: pout; px; py]) scs jm' [::] /\
      jasmin_post m jm jm' (result_post pout (F.sub (eval_w x) (eval_w y)) Rr).
  Proof. exact: binop_jasmin get_sub (ccmd_sub name K). Qed.

  Theorem bls12_mul_jasmin : bls12_mul_contract ->
    forall ev scs jm pout px py x y out Rr m, binop_pre pout px py x y out Rr m -> mem_rel m jm ->
    exists jm', sem_call P ev scs jm (fname "bls12_mul") (jargs [:: pout; px; py]) scs jm' [::] /\
      jasmin_post m jm jm' (result_post pout (F.mul (eval_w x) (eval_w y)) Rr).
  Proof. exact: binop_jasmin get_mul (ccmd_mul name K). Qed.

  Theorem bls12_square_jasmin : bls12_square_contract ->
    forall ev scs jm pout px x out Rr m, unop_pre pout px x out Rr m -> mem_rel m jm ->
    exists jm', sem_call P ev scs jm (fname "bls12_square") (jargs [:: pout; px]) scs jm' [::] /\
      jasmin_post m jm jm' (result_post pout (F.pow (eval_w x) 2) Rr).
  Proof. exact: unop_jasmin get_square (ccmd_square name K). Qed.
End T.
