(** Thin BN-254 wrapper over [WbwMontgomeryG1_BignumSpecs]. *)

Require Import Crypto.Bedrock.Specs.Field.
Require Import Bedrock.Field.Synthesis.Examples.bn254_prime.
Require Import Bedrock.Curve.WbwMontgomeryG1_BignumSpecs.

Existing Instance bn254_prime.bn254_field_parameters.
Existing Instance bn254_prime.bn254_frep.
Existing Instance bn254_prime.bn254_frep_ok.

(** Backward-compat aliases. *)
Notation bn254_n                      := (felem_size_in_words (FieldRepresentation := bn254_prime.bn254_frep)).
Notation bn254_FElem_iff_Bignum       := G1_FElem_iff_Bignum.
Notation bn254_Bignum_to_FElem        := G1_Bignum_to_FElem.
Notation bn254_feval_unfold           := G1_feval_unfold.
Notation bn254_tight_bounds_iff_valid := G1_tight_bounds_iff_valid.
