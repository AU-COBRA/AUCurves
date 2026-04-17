(** * Curve Instance Factory for BLS12-family pairing proofs.

    Provides Fp2/Fp6/Fp12 extension field instances given Fp-level
    parameters. Eliminates ~60 lines of boilerplate per proof file.

    Usage:
    <<
      (* Caller provides Fp-level setup *)
      Let M_pos := Eval vm_compute in (Z.to_pos my_prime.m).
      Instance my_pf_params : PrimeFieldParameters := ...
      Instance my_Fp_rep : AbstractField.FieldRepresentation (F:=Fp) := ...

      (* Factory provides Fp2/Fp6/Fp12 *)
      Let beta := F.of_Z PrimeField.M_pos (-5).
      Let xi_re := @F.zero PrimeField.M_pos.
      Let xi_im := @F.one PrimeField.M_pos.
      Let prefix := "bls377_".
      Include BLS12_ExtInstances.
    >>
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensions.

Import BinInt String.

Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* Extension field instances from Fp-level params + curve constants *)
(* ================================================================ *)

Section BLS12_ExtInstances.

  Context {pf_params : PrimeFieldParameters}.
  Existing Instance pf_params.
  Context {pf_params_ok : PrimeFieldParameters_ok}.
  Existing Instance prime_field_parameters.
  Context {Fp_rep : AbstractField.FieldRepresentation
            (F:=F PrimeField.M_pos)}.

  Variable beta : F PrimeField.M_pos.
  Variable xi_re xi_im : F PrimeField.M_pos.
  Variable func_prefix : string.

  Let fp2_prefix := (func_prefix ++ "Fp2_")%string.
  Let fp6_prefix := (func_prefix ++ "Fp6_")%string.
  Let fp12_prefix := (func_prefix ++ "Fp12_")%string.

  Local Notation Fp := (F PrimeField.M_pos).
  Local Notation Fp2 := ((Fp * Fp)%type).
  Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
  Local Notation Fp12 := ((Fp6 * Fp6)%type).

  (* Fp2 *)
  Instance ext_Fp2_params : AbstractField.FieldParameters Fp2 :=
    Fp2_field_parameters beta fp2_prefix.
  Instance ext_Fp2_rep : AbstractField.FieldRepresentation (F:=Fp2) :=
    Fp2_field_representation beta fp2_prefix.
  Instance ext_Fp2_names : FieldNames (F:=Fp2) :=
    field_names_prefixed fp2_prefix.

  (* Fp6 *)
  Instance ext_Fp6_params : AbstractField.FieldParameters Fp6 :=
    Fp6_field_parameters beta xi_re xi_im (fp6_prefix:=fp6_prefix).
  Instance ext_Fp6_rep : AbstractField.FieldRepresentation (F:=Fp6) :=
    Fp6_field_representation beta xi_re xi_im
      (fp6_prefix:=fp6_prefix) (fp2_prefix:=fp2_prefix).
  Instance ext_Fp6_names : FieldNames (F:=Fp6) :=
    field_names_prefixed fp6_prefix.

  (* Fp12 *)
  Instance ext_Fp12_params : AbstractField.FieldParameters Fp12 :=
    Fp12_field_parameters beta xi_re xi_im (fp12_prefix:=fp12_prefix).
  Instance ext_Fp12_rep : AbstractField.FieldRepresentation (F:=Fp12) :=
    Fp12_field_representation beta xi_re xi_im
      (fp12_prefix:=fp12_prefix) (fp6_prefix:=fp6_prefix) (fp2_prefix:=fp2_prefix).
  Instance ext_Fp12_names : FieldNames (F:=Fp12) :=
    field_names_prefixed fp12_prefix.

  (* Fp *)
  Instance ext_Fp_names : FieldNames (F:=Fp) :=
    field_names_prefixed func_prefix.

End BLS12_ExtInstances.
