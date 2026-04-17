(** * Curve25519 field arithmetic — 64-bit, 5-limb unsaturated Solinas.
 *
 * This is the 64-bit/x86-64 counterpart of fiat-crypto's
 * [Bedrock.End2End.X25519.Field25519] which uses 32-bit/10-limb for RISC-V.
 *
 * The fiat-crypto pipeline synthesizes the same proven field operations,
 * just with different limb count and machine word size.
 *)

Require Import Crypto.Spec.Curve25519.
From Coq Require Import String. Local Open Scope string_scope.
From Coq Require Import List.
From Coq Require Import ZArith.
Require Import bedrock2.BasicC64Semantics.
Require Import coqutil.Macros.WithBaseName.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Common.Names.VarnameGenerator.
Require Import Crypto.Bedrock.Field.Interface.Representation.
Require Import Crypto.Bedrock.Field.Synthesis.New.ComputedOp.
Require Import Crypto.Bedrock.Field.Synthesis.New.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Bedrock.Specs.Field.
Import ListNotations.

(* 64-bit word instances from BasicC64Semantics *)
#[export]
Existing Instances BasicC64Semantics.word BasicC64Semantics.wordok Bitwidth64.BW64.
#[export]
Existing Instances BasicC64Semantics.mem BasicC64Semantics.mapok.

(* Parameters for Curve25519 field (64-bit machine). *)
Section Field.
  Local Existing Instances default_parameters default_parameters_ok.

  (* 5 limbs × 64 bits = unsaturated Solinas for 2^255-19 *)
  Definition n : nat := 5.
  Definition s : Z := 2^255.
  Definition c : list (Z * Z) := [(1, 19)]%Z.

  Definition prefix : string := "fe25519_"%string.

  Instance field_parameters : FieldParameters :=
    field_parameters_prefixed Curve25519.p Curve25519.M.a24 "fe25519_"%string.

  #[export] Instance frep25519 : FieldRepresentation := field_representation n s c.

  (* Call fiat-crypto pipeline on all field operations *)
  Instance fe25519_ops : unsaturated_solinas_ops n s c.
  Proof using Type. Time constructor; make_computed_op. Defined.

  #[export] Instance frep25519_ok : FieldRepresentation_ok(field_representation:=frep25519).
  Proof.
    apply Crypto.Bedrock.Field.Synthesis.New.Signature.field_representation_ok.
    apply UnsaturatedSolinas.relax_valid.
    change felem_size_in_bytes with 40%Z. Lia.lia.
  Qed.

  (**** Translate each field operation into bedrock2 ****)

  Derive fe25519_from_bytes
    SuchThat (forall functions,
      Interface.map.get functions "fe25519_from_bytes" = Some fe25519_from_bytes ->
      spec_of_from_bytes (field_representation:=frep25519) functions)
    As fe25519_from_bytes_correct.
  Proof. Time derive_bedrock2_func from_bytes_op. Qed.

  Derive fe25519_to_bytes
    SuchThat (forall functions,
      Interface.map.get functions "fe25519_to_bytes" = Some fe25519_to_bytes ->
      spec_of_to_bytes (field_representation:=frep25519) functions)
    As fe25519_to_bytes_correct.
  Proof. Time derive_bedrock2_func to_bytes_op. Qed.

  Derive fe25519_copy
    SuchThat (forall functions,
      Interface.map.get functions "fe25519_copy" = Some fe25519_copy ->
      spec_of_felem_copy (field_representation:=frep25519) functions)
    As fe25519_copy_correct.
  Proof. Time derive_bedrock2_func felem_copy_op. Qed.

  Derive fe25519_from_word
    SuchThat (forall functions,
      Interface.map.get functions "fe25519_from_word" = Some fe25519_from_word ->
      spec_of_from_word (field_representation:=frep25519) functions)
    As fe25519_from_word_correct.
  Proof. Time derive_bedrock2_func from_word_op. Qed.

  Derive fe25519_mul
    SuchThat (forall functions,
      Interface.map.get functions "fe25519_mul" = Some fe25519_mul ->
      spec_of_BinOp bin_mul (field_representation:=frep25519) functions)
    As fe25519_mul_correct.
  Proof. Time derive_bedrock2_func mul_op. Qed.

  Derive fe25519_square
    SuchThat (forall functions,
      Interface.map.get functions "fe25519_square" = Some fe25519_square ->
      spec_of_UnOp un_square (field_representation:=frep25519) functions)
    As fe25519_square_correct.
  Proof. Time derive_bedrock2_func square_op. Qed.

  Derive fe25519_add
    SuchThat (forall functions,
      Interface.map.get functions "fe25519_add" = Some fe25519_add ->
      spec_of_BinOp bin_add (field_representation:=frep25519) functions)
    As fe25519_add_correct.
  Proof. Time derive_bedrock2_func add_op. Qed.

  Derive fe25519_sub
    SuchThat (forall functions,
      Interface.map.get functions "fe25519_sub" = Some fe25519_sub ->
      spec_of_BinOp bin_sub (field_representation:=frep25519) functions)
    As fe25519_sub_correct.
  Proof. Time derive_bedrock2_func sub_op. Qed.

  Derive fe25519_carry_add
    SuchThat (forall functions,
      Interface.map.get functions "fe25519_carry_add" = Some fe25519_carry_add ->
      spec_of_BinOp bin_carry_add (field_representation:=frep25519) functions)
    As fe25519_carry_add_correct.
  Proof. Time derive_bedrock2_func carry_add_op. Qed.

  Derive fe25519_carry_sub
    SuchThat (forall functions,
      Interface.map.get functions "fe25519_carry_sub" = Some fe25519_carry_sub ->
      spec_of_BinOp bin_carry_sub (field_representation:=frep25519) functions)
    As fe25519_carry_sub_correct.
  Proof. Time derive_bedrock2_func carry_sub_op. Qed.

  Derive fe25519_scmula24
    SuchThat (forall functions,
      Interface.map.get functions "fe25519_scmula24" = Some fe25519_scmula24 ->
      spec_of_UnOp un_scmula24 (field_representation:=frep25519) functions)
    As fe25519_scmula24_correct.
  Proof. Time derive_bedrock2_func scmula24_op. Qed.

End Field.
