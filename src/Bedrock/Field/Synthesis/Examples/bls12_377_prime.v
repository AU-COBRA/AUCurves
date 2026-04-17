Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Synthesis.New.ComputedOp.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Bedrock.Specs.Field.
Import ListNotations.
Require Import Crypto.Bedrock.Field.Translation.Proofs.ValidComputable.Func.
Require Import Bedrock.Field.Synthesis.Examples.bls12_377_prime_certif.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.Syntax.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Local Open Scope string_scope.
Local Infix "*" := sep : sep_scope.
Delimit Scope sep_scope with sep.
Local Notation function_t := ((String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type).
Local Notation functions_t := (list function_t).
Local Open Scope sep_scope.
Local Open Scope Z_scope.

(* Parameters for BLS12-377 field. *)
Section Field.
  (* BLS12-377: u = 0x8508c00000000001 (positive, unlike BLS12-381's negative u) *)
  Definition n : nat := 6.
  Definition u := 0x8508c00000000001.
  Definition p_of_u u := (((u - 1)^2 * (u^4 - u^2 + 1)) / 3) + u.
  Definition m : Z := Eval vm_compute in (p_of_u u).
  (* m = 258664426012969094010652733694893533536393512754914660539884262666720468348340822774968888139573360124440321458177 *)
  (* 377 bits, 6 × 64-bit words *)

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters
    Defaults64.default_parameters_ok.

  Definition prefix : string := "bls377_"%string.

  Instance bls377_field_parameters : FieldParameters.
  Proof using Type.
    let M := (eval vm_compute in (Z.to_pos m)) in
    let a := constr:(F.of_Z M 0) in
    let prefix := constr:("bls377_"%string) in
    eapply
      (field_parameters_prefixed
         M a prefix).
  Defined.

  Instance bls377_field_parameters_ok : FieldParameters_ok.
  Proof using Type.
    constructor.
    exact prime_bls12_377.
  Qed.

  Definition to_mont_string := prefix ++ "to_mont".
  Definition from_mont_string := prefix ++ "from_mont".

  (* Call fiat-crypto pipeline on all field operations *)
  Instance bls377_ops : @word_by_word_Montgomery_ops from_mont_string to_mont_string _ _ _ _ _ _ _ _ _ _ (WordByWordMontgomery.n m machine_wordsize) m.
  Proof using Type. Time constructor; make_computed_op. Defined.

  Instance bls377_frep : FieldRepresentation := field_representation m.
  Instance bls377_frep_raw : FieldRepresentation := field_representation_raw m.
  Instance bls377_frep_ok : FieldRepresentation_ok (field_representation:=bls377_frep).
  Proof.
    apply Crypto.Bedrock.Field.Synthesis.New.Signature.field_representation_ok.
    intros. assumption.
    let c := eval lazy in felem_size_in_bytes in change felem_size_in_bytes with c.
    Lia.lia.
  Defined.
  Instance bls377_frep_raw_ok : FieldRepresentation_ok (field_representation:=bls377_frep_raw).
  Proof.
    apply Crypto.Bedrock.Field.Synthesis.New.Signature.field_representation_ok.
    intros. assumption.
    let c := eval lazy in felem_size_in_bytes in change felem_size_in_bytes with c.
    Lia.lia.
  Defined.

  (**** Translate each field operation into bedrock2 ****)

  Local Notation functions_contain functions f :=
    (Interface.map.get functions (fst f) = Some (snd f)).

  Local Ltac begin_derive_bedrock2_func :=
    lazymatch goal with
    | |- context [spec_of_BinOp bin_mul] => eapply mul_func_correct
    | |- context [spec_of_UnOp un_square] => eapply square_func_correct
    | |- context [spec_of_BinOp bin_add] => eapply add_func_correct
    | |- context [spec_of_BinOp bin_sub] => eapply sub_func_correct
    | |- context [spec_of_UnOp un_opp] => eapply opp_func_correct
    | |- context [spec_of_from_bytes] => eapply from_bytes_func_correct
    | |- context [spec_of_to_bytes] => eapply to_bytes_func_correct
    end.

  Ltac epair :=
    lazymatch goal with
    | f := _ : string * Syntax.func |- _ =>
      let p := open_constr:((_, _)) in
      unify f p;
      subst f
    end.

  Ltac derive_bedrock2_func op :=
    epair;
    begin_derive_bedrock2_func;
    try lazymatch goal with
      | |- _ = b2_func _ => vm_compute; reflexivity
      end;
    lazymatch goal with
    | |- _ = @ErrorT.Success ?ErrT unit tt =>
      abstract (vm_cast_no_check (@eq_refl _ (@ErrorT.Success ErrT unit tt)))
    | |- Func.valid_func _ =>
      eapply Func.valid_func_bool_iff;
      abstract vm_cast_no_check (eq_refl true)
    | |- (_ = _)%Z => vm_compute; reflexivity
    | |- (felem_size_in_bytes <= 2 ^ _)%Z => apply felem_size_ok
    end.

  Derive bls377_from_bytes
         SuchThat (forall functions,
                      functions_contain functions bls377_from_bytes ->
                      spec_of_from_bytes
                        (field_representation:=bls377_frep_raw)
                        functions)
         As bls377_from_bytes_correct.
  Proof. Time derive_bedrock2_func from_bytes_op. Qed.

  Derive bls377_to_bytes
         SuchThat (forall functions,
                      functions_contain functions bls377_to_bytes ->
                      spec_of_to_bytes
                        (field_representation:=bls377_frep_raw)
                        functions)
         As bls377_to_bytes_correct.
  Proof. Time derive_bedrock2_func to_bytes_op. Qed.

  Derive bls377_mul
         SuchThat (forall functions,
                      functions_contain functions bls377_mul ->
                      spec_of_BinOp bin_mul
                        (field_representation:=bls377_frep)
                        functions)
         As bls377_mul_correct.
  Proof. Time derive_bedrock2_func mul_op. Qed.

  Derive bls377_square
         SuchThat (forall functions,
                      functions_contain functions bls377_square ->
                      spec_of_UnOp un_square
                        (field_representation:=bls377_frep)
                        functions)
         As bls377_square_correct.
  Proof. Time derive_bedrock2_func square_op. Qed.

  Derive bls377_add
         SuchThat (forall functions,
                      functions_contain functions bls377_add ->
                      spec_of_BinOp bin_add
                        (field_representation:=bls377_frep)
                        functions)
         As bls377_add_correct.
  Proof. Time derive_bedrock2_func add_op. Qed.

  Derive bls377_sub
         SuchThat (forall functions,
                      functions_contain functions bls377_sub ->
                      spec_of_BinOp bin_sub
                        (field_representation:=bls377_frep)
                        functions)
         As bls377_sub_correct.
  Proof. Time derive_bedrock2_func sub_op. Qed.

  Derive bls377_from_mont
         SuchThat (forall functions,
                      functions_contain functions bls377_from_mont ->
                      spec_of_UnOp un_from_mont
                        (field_representation:=bls377_frep)
                        functions)
         As bls377_from_mont_correct.
  Proof.
    epair.
    eapply (from_mont_func_correct _ _ _ from_mont_string to_mont_string).
        - vm_compute; reflexivity.
        - apply felem_size_ok.
        - eapply Func.valid_func_bool_iff. abstract vm_cast_no_check (eq_refl true).
          Unshelve.
            + auto.
            + auto.
  Qed.

  Derive bls377_to_mont
         SuchThat (forall functions,
                      functions_contain functions bls377_to_mont ->
                      spec_of_UnOp un_to_mont
                        (field_representation:=bls377_frep)
                        functions)
         As bls377_to_mont_correct.
  Proof.
    epair.
    eapply (to_mont_func_correct _ _ _ from_mont_string to_mont_string).
        - vm_compute; reflexivity.
        - apply felem_size_ok.
        - eapply Func.valid_func_bool_iff. abstract vm_cast_no_check (eq_refl true).
          Unshelve. all: auto.
   Qed.

  Derive bls377_select_znz
           SuchThat (forall functions,
                      functions_contain functions bls377_select_znz ->
                      spec_of_selectznz
                        (field_representation:=bls377_frep)
                        functions)
         As bls377_select_znz_correct.
  Proof.
    epair.
    eapply select_znz_func_correct. 1,2:auto.
        - vm_compute; reflexivity.
        - apply felem_size_ok.
        - eapply Func.valid_func_bool_iff. abstract vm_cast_no_check (eq_refl true).
   Qed.

End Field.
