(** * BW6-761 Fp3 = cubic-over-Fp — type-level acceptance test.

    Goal: confirm that [GenericCubic.CE_funcs] accepts BaseField=Fp
    (a primitive Z/pZ field) without modification, matching the way
    it currently accepts BaseField=Fp8 (chained quadratic tower) in
    BLS24-509's Fp24 instantiation.

    This file does NOT instantiate the full BW6-761 Fp3 wiring (that
    requires the bedrock2 body for [bw6_761_Fp3_mul_by_nr], which is
    a follow-up task in the (B+C) phase of the pairing-tower plan).
    Instead, it sets up a Section that mirrors the BLS24-509 Fp24
    skeleton with BaseField=Fp instead of BaseField=Fp8, and applies
    [CE_funcs] symbolically.  If the file builds, the generic
    mechanism is confirmed to accept cubic-over-Fp.

    Verdict (mechanised on successful build): the existing
    [GenericCubic.CE_funcs] is parametric over the base field via
    [Context {BaseField : Type}] + [Context {base_fp : FieldParameters
    BaseField}] + [Context {base_repr : FieldRepresentation _}].  The
    cubic-over-Fp shape is a strict simplification of the
    cubic-over-Fp8 shape already in use, so no modification is
    required. *)

From Stdlib Require Import Strings.String ZArith.ZArith.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Bedrock.Field.FieldExtensions.GenericCubic.
Require Import Bedrock.Field.FieldExtensions.GenericCubicSpecs.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.Syntax.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.

Import BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Section BW6_761_Fp3_TypeTest.

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters
    Defaults64.default_parameters_ok.

  (** Abstract base-field context — exactly what CE_funcs consumes. *)
  Context {bw6_prime_params : PrimeFieldParameters}.
  Context {bw6_prime_params_ok : PrimeFieldParameters_ok}.
  Existing Instance prime_field_parameters.

  Context {bw6_Fp_repr : AbstractField.FieldRepresentation
    (F := F PrimeField.M_pos)}.
  Context {bw6_Fp_repr_ok : AbstractField.FieldRepresentation_ok
    (F := F PrimeField.M_pos)}.
  Context {bw6_Fp_names : FieldNames (F := F PrimeField.M_pos)}.

  Local Notation Fp := (F PrimeField.M_pos).

  (** Cubic non-residue model: multiplication by -4 in Fp.
      Per gnark-crypto bw6-761/fp/element.go. *)
  Definition bw6_Fp_mul_by_nr_model (x : Fp) : Fp :=
    F.mul (F.opp (F.of_Z _ 4)) x.

  (** Decidable equality on Fp *)
  Definition bw6_Fp_eq_dec : forall x y : Fp, {x = y} + {x <> y} :=
    @F.eq_dec PrimeField.M_pos.

  Let fp3_prefix := "bw6_761_Fp3_".

  (** Build Fp3's [FieldParameters] / [FieldRepresentation] / names
      via the CE_* constructors — same as BLS24 does for Fp24
      (just over Fp instead of Fp8). *)
  Instance bw6_Fp3_params : AbstractField.FieldParameters (Fp * Fp * Fp) :=
    @CE_field_parameters Fp prime_field_parameters
      bw6_Fp_mul_by_nr_model fp3_prefix bw6_Fp_eq_dec.

  Instance bw6_Fp3_repr : AbstractField.FieldRepresentation
    (F := Fp * Fp * Fp) :=
    @CE_field_representation _ _ _ _ Fp prime_field_parameters bw6_Fp_repr
      bw6_Fp_mul_by_nr_model fp3_prefix bw6_Fp_eq_dec.

  Instance bw6_Fp3_repr_ok : AbstractField.FieldRepresentation_ok
    (F := Fp * Fp * Fp) :=
    @CE_field_representation_ok _ _ _ _ Fp prime_field_parameters
      bw6_Fp_repr bw6_Fp_repr_ok
      bw6_Fp_mul_by_nr_model fp3_prefix bw6_Fp_eq_dec.

  Instance bw6_Fp3_names : FieldNames (F := Fp * Fp * Fp) :=
    field_names_prefixed fp3_prefix.

  (** The mul_by_nr bedrock2 body — abstract for this type test.
      In the full instantiation (follow-up), this would be a bedrock2
      function that takes [out, x] and computes [out := (-4) * x] in
      Fp via the base [bw6_761_opp] + [bw6_761_add] (since -4·x =
      neg(2·2·x), expressible with 1 opp + 2 adds, OR via a direct
      bw6_761_mul with a precomputed -4 constant). *)
  Variable bw6_Fp_mul_by_nr_name : string.
  Variable bw6_Fp_mul_by_nr_func : function_t.

  (** *** The key acceptance test ***
      If this definition typechecks, [GenericCubic.CE_funcs] accepts
      cubic-over-Fp without any modification to the generic
      mechanism. *)
  Definition bw6_761_Fp3_funcs_skeleton : list function_t :=
    GenericCubic.CE_funcs
      (CE_names := bw6_Fp3_names)
      (base_names := bw6_Fp_names)
      bw6_Fp_mul_by_nr_model
      fp3_prefix
      bw6_Fp_eq_dec
      bw6_Fp_mul_by_nr_name
      bw6_Fp_mul_by_nr_func.

End BW6_761_Fp3_TypeTest.

(** *** Verdict (mechanised) ***
    The file builds, so [GenericCubic.CE_funcs] mechanically accepts
    cubic-over-Fp without modification.  The existing generic
    extension machinery is sufficient for the BW6-761 Fp3 layer of
    the (B+C) plan.

    Next step (in the (B+C) phase): write the concrete
    [BW6_761_Instances.v] (parallel to [BLS24_509_Instances.v]
    lines 49-110) with:
      - [bw6_prime_params : PrimeFieldParameters] from bw6_761_prime.v
      - [bw6_Fp_repr / _ok] bridging Field.FieldRepresentation to
        AbstractField.FieldRepresentation
      - [bw6_Fp_names] via [field_names_prefixed "bw6_761_"]
      - The concrete bedrock2 body for [bw6_761_Fp3_mul_by_nr]
        (compute [(-4) * x] using base [bw6_761_mul] with the -4
        constant in Montgomery form).
    Estimated ~80 LoC mechanical mirror of the BLS24-509 file. *)
