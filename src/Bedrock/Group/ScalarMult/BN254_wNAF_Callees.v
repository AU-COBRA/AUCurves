(** * BN254 callee-spec discharges for the single-scalar wNAF chain.

    [BN254_wNAF_Instance.wnaf_single_full] and
    [BN254_wNAF_Laws.bn254_wnaf_single_full] take their point-operation
    callees as Section hypotheses:

      HCurveDouble, HCurveAddInplace, HFelemCopy, HOpp, HOppInplace,
      HStoreZero, Hdigit_load.

    This file discharges the ones that follow from a BN254 function
    table plus the fiat-crypto leaf specs, using the curve-generic
    wrapper lemmas of [NistWnafWrappers.v] — the same route
    [P256_wNAF_Instance.v] §4 takes for P-256.

    Discharged here:
      Hdigit_load     [digit_load_from_array]   (no table entry needed)
      HStoreZero      [store_zero_from_word_ok] + "store_zero" entry
      HOpp            [opp_inplace_ok] fst      + "opp_inplace" entry
      HOppInplace     [opp_inplace_ok] snd      + "opp_inplace" entry
      HFelemCopy      [felem_copy_HFelemCopy]   + spec_of_felem_copy

    NOT discharged here: [HCurveDouble] and [HCurveAddInplace].  Both
    of the generic wrappers that produce them
    ([NistWnafWrappers.curve_double_general_ok] /
    [curve_add_inplace_general_ok]) call the derived general-a RCB
    addition at the bedrock2 name "curve_add_general", i.e. they need
    [spec_of_rcb_add_general three_b a_const functions].  No BN curve
    has an instantiation of [CurveAddGeneralA.v] yet: there is no
    "bn254_three_b" loader FUNCTION anywhere (only the name, used
    inside [ladderstep_body] / [rcb_double_a0_body]), no "a_const"
    loader, and no [bn254_curve_add_general_func].  See the report at
    the end of this file for the recipe. *)

From Stdlib Require Import ZArith Lia List.
Require Import Rupicola.Lib.Api.
Import bedrock2.WeakestPrecondition.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Bedrock.Field.Synthesis.Examples.bn254_prime.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_wNAF_ProcessDigits.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_wNAF_GLV_Instance.
Require Import Bedrock.Group.CurveAdd.StoreZero.
Require Import Bedrock.Group.ScalarMult.NistWnafWrappers.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Section BN254_Callees.

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters
    Defaults64.default_parameters_ok
    bn254_field_parameters
    bn254_field_parameters_ok
    bn254_frep
    bn254_frep_ok.

  Local Notation word := BasicC64Semantics.word.
  Local Notation F := (F M_pos).
  Local Notation FElem := (Compilation2.FElem).

  Lemma bn254_bounds_eq :
    loose_bounds (FieldRepresentation:=bn254_frep)
    = tight_bounds (FieldRepresentation:=bn254_frep).
  Proof. reflexivity. Qed.

  (* ============================================================== *)
  (* §1. The wrapper functions at BN254                              *)
  (* ============================================================== *)

  Definition bn254_opp_inplace_func : function_t := opp_inplace_func.
  Definition bn254_store_zero_func : function_t := store_zero_from_word_func.

  (** Table membership for the two wrapper bodies this file needs.
      The wNAF driver calls the negation at the parametric [opp_name],
      which for BN254 is "opp_inplace" (the aliasing-tolerant wrapper),
      and the identity store at "store_zero". *)
  Definition bn254_wnaf_wrapper_table (functions : Semantics.env) : Prop :=
    map.get functions "store_zero" = Some (snd bn254_store_zero_func)
    /\ map.get functions "opp_inplace" = Some (snd bn254_opp_inplace_func).

  (** The synthesized leaves the wrappers call.  [spec_of_UnOp un_opp]
      and [spec_of_from_word] come from the fiat-crypto synthesis at
      [bn254_frep]; [spec_of_felem_copy] from
      [Examples.bn254_felem_copy.felem_copy_ok]. *)
  Definition bn254_wnaf_leaf_specs (functions : Semantics.env) : Prop :=
    spec_of_UnOp un_opp functions
    /\ spec_of_from_word functions
    /\ spec_of_felem_copy functions.

  (* ============================================================== *)
  (* §2. Discharges                                                  *)
  (* ============================================================== *)

  (** [Hdigit_load] — no table entry, no leaf spec: the digit array is
      a plain word array and the load is [digit_load_from_array]. *)
  Lemma bn254_Hdigit_load : forall (dk : list Z) (n : nat) (base : word)
      (m : BasicC64Semantics.mem) R,
    (n < length dk)%nat ->
    (@DigitArray _ word BasicC64Semantics.mem base dk ⋆ R) m ->
    Memory.load access_size.word m
      (word.add base (word.mul (word.of_Z (Z.of_nat n))
        (word.of_Z (Memory.bytes_per_word 64)))) =
    Some (encode_digit (nth n dk 0)).
  Proof.
    intros. eapply digit_load_from_array; eassumption.
  Qed.

  (** [HStoreZero]. *)
  Lemma bn254_HStoreZero :
    forall functions,
      bn254_wnaf_wrapper_table functions ->
      bn254_wnaf_leaf_specs functions ->
      @StoreZero.spec_of_store_zero _ _ _ _ _ _
        bn254_field_parameters bn254_frep functions.
  Proof.
    intros functions (Hsz & _) (_ & Hfw & _).
    (* Fully applied: [store_zero_from_word_ok] takes, after Section
       discharge, six bedrock2 parameters, four ok-classes, the field
       parameters and representation, [FieldRepresentation_ok], then
       [functions] and the two premises.  Written as [exact] rather than
       [eapply] so the cost is one conversion, not a conclusion search. *)
    exact (@store_zero_from_word_ok _ _ _ _ _ _ _ _ _ _ _ _ _
             functions Hsz Hfw).
  Qed.

  (** [HOpp] and [HOppInplace], both at the name "opp_inplace". *)
  Lemma bn254_HOppInplace_spec :
    forall functions,
      bn254_wnaf_wrapper_table functions ->
      bn254_wnaf_leaf_specs functions ->
      spec_of_opp_inplace functions.
  Proof.
    intros functions (_ & Hoi) (Hopp & _ & Hcopy).
    exact (@opp_inplace_ok _ _ _ _ _ _ _ _ _ _ _ _ _
             bn254_bounds_eq functions Hoi Hopp Hcopy).
  Qed.

  (** [HFelemCopy]. *)
  Lemma bn254_HFelemCopy :
    forall functions,
      bn254_wnaf_leaf_specs functions ->
      forall pDst pSrc (v : F) (old : F) R0 tr0 m0,
        (FElem (Some tight_bounds) pSrc v
         ⋆ FElem (Some tight_bounds) pDst old ⋆ R0) m0 ->
        Semantics.call functions felem_copy tr0 m0 [pDst; pSrc]
          (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
            (FElem (Some tight_bounds) pSrc v
             ⋆ FElem (Some tight_bounds) pDst v ⋆ R0) m').
  Proof.
    intros functions (_ & _ & Hcopy).
    exact (felem_copy_HFelemCopy functions Hcopy).
  Qed.

End BN254_Callees.
