(** * BLS12-381 Fp functions as one translated Jasmin program, in fiat-crypto's environment.

    Loads fiat-crypto's bedrock2 synthesis of the BLS12-381 field ([bls12_prime],
    [BLS12_FpExtra], [bls12_felem_copy]) with [Prog] (the translation with calls) and [PsemBig]
    (Jasmin's big-step semantics without ITree).

    - [bls12_prog_funcs] are translated by [translate_prog]: the four leaves, select_znz, the
      Montgomery conversions, opp, felem_copy and from_word (which calls to_mont).
      from_bytes/to_bytes are not (byte loads and stores).
    - [bls12_from_word_jasmin]: from fiat-crypto's spec of from_word (proved by
      [bls12_from_word_correct] from the call to [bls12_to_mont]), [prog_correct] gives the
      Jasmin call of the translated program, which runs the translated call to to_mont.
    - [bls12_mul_jasmin_prog]: the same for mul, through [prog_correct].
    - [QE_*_translated]: the bodies of the generic quadratic extension's copy, zero, one and
      opp ([GenericQuadratic]) are translated, for every base field and names; its add, sub,
      mul, square and select_znz use [stackalloc] and are not, nor is [bls12_Fp2_mul_xi]. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Jasmin Require Import utils wsize word memory_model low_memory expr psem_defs psem_core values
  varmap sem_type arch_extra x86_extra sem_params_of_arch_extra.
From Stdlib Require Import String ZArith.
Require Import bedrock2.Syntax bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_FpExtra.
Require Bedrock.Field.Synthesis.Examples.bls12_felem_copy.
Require Bedrock.Field.FieldExtensions.GenericQuadratic.
Require Import JasminBridge.Ast.PsemBig JasminBridge.Ast.Base JasminBridge.Ast.Trans
  JasminBridge.Ast.Comp JasminBridge.Ast.Sim JasminBridge.Ast.Fun JasminBridge.Ast.Prog.
Set SsrOldRewriteGoalsOrder.
Set Bullet Behavior "Strict Subproofs".
Local Open Scope string_scope.

Existing Instances Bitwidth64.BW64 bls12_field_parameters bls12_frep.

Definition bls12_prog_funcs : list (string * func) :=
  [:: bls12_add; bls12_sub; bls12_mul; bls12_square; bls12_select_znz; bls12_from_mont;
      bls12_to_mont; bls12_opp; ("bls12_felem_copy", bls12_felem_copy.bls12_felem_copy);
      bls12_from_word].

Local Notation functions_contain functions f :=
  (coqutil.Map.Interface.map.get functions (fst f) = Some (snd f)).

Local Notation fenv := (@coqutil.Map.Interface.map.of_list _ _ bedrock2.Semantics.env bls12_prog_funcs).

Lemma fenv_from_word : functions_contain fenv bls12_from_word.
Proof. by vm_compute. Qed.

Lemma fenv_to_mont : functions_contain fenv bls12_to_mont.
Proof. by vm_compute. Qed.

Lemma fenv_mul : functions_contain fenv bls12_mul.
Proof. by vm_compute. Qed.

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

  Local Notation jargs xs := [seq Vword (jw a) | a <- xs].

  Lemma bls12_prog_translated : isSome (translate_prog name fname finfo iinfo bls12_prog_funcs).
  Proof. by vm_compute. Qed.

  (** fiat-crypto's postcondition of from_word. *)
  Local Notation bword := (@coqutil.Word.Interface.word.rep 64 BasicC64Semantics.word).
  Local Notation bmem := (@coqutil.Map.Interface.map.rep _ _ BasicC64Semantics.mem).
  Definition from_word_post (pout x : bword) (R : bmem -> Prop) (tr : bedrock2.Semantics.trace) :=
    fun (tr' : bedrock2.Semantics.trace) (mem' : bmem) (rets : list bword) =>
      rets = nil /\ tr = tr' /\
      (exists X : felem,
         feval (felem_to_list X) = ModularArithmetic.F.of_Z M_pos (word.unsigned x) /\
         bounded_by tight_bounds (felem_to_list X) /\
         Separation.sep (FElem pout X) R mem').

  Theorem bls12_from_word_jasmin P :
    translate_prog name fname finfo iinfo bls12_prog_funcs = Some P ->
    forall ev scs jm (sp : u64) pout x out R t m,
      Separation.sep (Separation.sepclause_of_map (OfListWord.map.of_list_word_at pout out)) R m /\
      Datatypes.length out = Z.to_nat felem_size_in_bytes ->
      mem_rel m jm ->
      exists jm' vres,
        PsemBig.sem_call P ev scs jm (fname "bls12_from_word") (Vword sp :: jargs [:: pout; x]) scs jm' vres /\
        exists m' rets, [/\ from_word_post pout x R t t m' rets, vres = jargs rets, mem_rel m' jm',
          (forall k, coqutil.Map.Interface.map.get m' k = None <-> coqutil.Map.Interface.map.get m k = None) &
          (forall p, outside m p -> read jm' Aligned p U8 = read jm Aligned p U8)].
  Proof.
    move=> hP ev scs jm sp pout x out R t m hpre hm.
    have hrel := translate_prog_get name fname finfo iinfo bls12_prog_funcs P fname_inj hP.
    have hcall := bls12_from_word_correct fenv fenv_from_word fenv_to_mont pout x out R t m hpre.
    exact: (prog_correct name name_inj fname finfo iinfo P ev fenv hrel
      (fun _ _ _ _ _ _ => naive_shift_masks) "bls12_from_word" t m
      [:: pout; x] _ jm scs sp hcall hm).
  Qed.

  Theorem bls12_mul_jasmin_prog P :
    translate_prog name fname finfo iinfo bls12_prog_funcs = Some P ->
    forall ev scs jm (sp : u64) pout px py t m post,
      (forall functions, functions_contain functions bls12_mul ->
         bedrock2.Semantics.call functions "bls12_mul" t m [:: pout; px; py] post) ->
      mem_rel m jm ->
      exists jm' vres,
        PsemBig.sem_call P ev scs jm (fname "bls12_mul") (Vword sp :: jargs [:: pout; px; py]) scs jm' vres /\
        exists m' rets, [/\ post t m' rets, vres = jargs rets, mem_rel m' jm',
          (forall k, coqutil.Map.Interface.map.get m' k = None <-> coqutil.Map.Interface.map.get m k = None) &
          (forall p, outside m p -> read jm' Aligned p U8 = read jm Aligned p U8)].
  Proof.
    move=> hP ev scs jm sp pout px py t m post H hm.
    have hrel := translate_prog_get name fname finfo iinfo bls12_prog_funcs P fname_inj hP.
    exact: (prog_correct name name_inj fname finfo iinfo P ev fenv hrel
      (fun _ _ _ _ _ _ => naive_shift_masks) "bls12_mul" t m
      [:: pout; px; py] post jm scs sp (H fenv fenv_mul) hm).
  Qed.
  (** ** The quadratic extension's copy, zero, one and opp: two calls each. *)
  (** ** The quadratic extension's copy, zero, one and opp: two calls each. *)
  Lemma QE_felem_copy_translated width BW word mem BaseField base_fp base_repr nonresidue prefix
      eq_dec_base :
    isSome (translate_fun name fname finfo iinfo
      (@GenericQuadratic.QE_felem_copy width BW word mem BaseField base_fp base_repr nonresidue prefix
         eq_dec_base)).
  Proof. by vm_compute. Qed.

  Lemma QE_zero_translated width BW word mem BaseField base_fp base_repr nonresidue prefix
      eq_dec_base QE_names base_names :
    isSome (translate_fun name fname finfo iinfo
      (@GenericQuadratic.QE_zero_func width BW word mem BaseField base_fp base_repr nonresidue prefix
         eq_dec_base QE_names base_names)).
  Proof. by vm_compute. Qed.

  Lemma QE_one_translated width BW word mem BaseField base_fp base_repr nonresidue prefix
      eq_dec_base QE_names base_names :
    isSome (translate_fun name fname finfo iinfo
      (@GenericQuadratic.QE_one_func width BW word mem BaseField base_fp base_repr nonresidue prefix
         eq_dec_base QE_names base_names)).
  Proof. by vm_compute. Qed.

  Lemma QE_opp_translated width BW word mem BaseField base_fp base_repr nonresidue prefix
      eq_dec_base :
    isSome (translate_fun name fname finfo iinfo
      (@GenericQuadratic.QE_opp width BW word mem BaseField base_fp base_repr nonresidue prefix
         eq_dec_base)).
  Proof. by vm_compute. Qed.

End T.
