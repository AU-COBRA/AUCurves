(** Thin Pallas wrapper over [WbwMontgomeryG1_BignumSpecs] functor.

    Replaces the ~100 LoC clone file [PallasCurve_G1_BignumSpecs.v] with
    a ~15 LoC functor application. Once validated, the original file
    can be deleted (or kept as a compatibility shim exposing the
    old lowercase pallas_* names). *)

Require Import Bedrock.Field.Synthesis.Examples.pallas_prime.
Require Import Bedrock.Curve.WbwMontgomeryG1_BignumSpecs.

Existing Instance pallas_prime.pallas_field_parameters.

Module PallasParams <: FIELD_REP_PARAMS.
  Definition frep    := pallas_prime.pallas_frep.
  Definition frep_ok := pallas_prime.pallas_frep_ok.
End PallasParams.

Module Pallas_Bignum := WbwMontgomeryG1_BignumSpecs PallasParams.

(** Backward-compat aliases for the old [pallas_*] names. *)

Notation pallas_n                      := Pallas_Bignum.n.
Notation pallas_FElem_iff_Bignum       := Pallas_Bignum.FElem_iff_Bignum.
Notation pallas_Bignum_to_FElem        := Pallas_Bignum.Bignum_to_FElem.
Notation pallas_feval_unfold           := Pallas_Bignum.feval_unfold.
Notation pallas_tight_bounds_iff_valid := Pallas_Bignum.tight_bounds_iff_valid.
