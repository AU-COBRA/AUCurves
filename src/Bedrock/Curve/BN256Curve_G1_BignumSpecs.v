(** Thin BN-256 wrapper over [WbwMontgomeryG1_BignumSpecs]. *)

Require Import Crypto.Bedrock.Specs.Field.
Require Import Bedrock.Field.Synthesis.Examples.bn256_prime.
Require Import Bedrock.Curve.WbwMontgomeryG1_BignumSpecs.

Existing Instance bn256_prime.bn256_field_parameters.
Existing Instance bn256_prime.bn256_frep.
Existing Instance bn256_prime.bn256_frep_ok.

(** Backward-compat aliases. *)
Notation bn256_n                      := (felem_size_in_words (FieldRepresentation := bn256_prime.bn256_frep)).
Notation bn256_FElem_iff_Bignum       := G1_FElem_iff_Bignum.
Notation bn256_Bignum_to_FElem        := G1_Bignum_to_FElem.
Notation bn256_feval_unfold           := G1_feval_unfold.
Notation bn256_tight_bounds_iff_valid := G1_tight_bounds_iff_valid.
