(** Thin BN-446 wrapper over [WbwMontgomeryG1_BignumSpecs]. *)

Require Import Crypto.Bedrock.Specs.Field.
Require Import Bedrock.Field.Synthesis.Examples.bn446_prime.
Require Import Bedrock.Curve.WbwMontgomeryG1_BignumSpecs.

Existing Instance bn446_prime.bn446_field_parameters.
Existing Instance bn446_prime.bn446_frep.
Existing Instance bn446_prime.bn446_frep_ok.

(** Backward-compat aliases. *)
Notation bn446_n                      := (felem_size_in_words (FieldRepresentation := bn446_prime.bn446_frep)).
Notation bn446_FElem_iff_Bignum       := G1_FElem_iff_Bignum.
Notation bn446_Bignum_to_FElem        := G1_Bignum_to_FElem.
Notation bn446_feval_unfold           := G1_feval_unfold.
Notation bn446_tight_bounds_iff_valid := G1_tight_bounds_iff_valid.
