(** Thin Pallas wrapper over the generic [WbwMontgomeryG1_BignumSpecs]
    Section. Replaces the ~100 LoC clone file with a ~15 LoC import +
    re-export under the legacy [pallas_*] names. *)

Require Import Crypto.Bedrock.Specs.Field.
Require Import Bedrock.Field.Synthesis.Examples.pallas_prime.
Require Import Bedrock.Curve.WbwMontgomeryG1_BignumSpecs.

Existing Instance pallas_prime.pallas_field_parameters.
Existing Instance pallas_prime.pallas_frep.
Existing Instance pallas_prime.pallas_frep_ok.

(** Backward-compat aliases for the old [pallas_*] names. *)
Notation pallas_n                      := (felem_size_in_words (FieldRepresentation := pallas_prime.pallas_frep)).
Notation pallas_FElem_iff_Bignum       := G1_FElem_iff_Bignum.
Notation pallas_Bignum_to_FElem        := G1_Bignum_to_FElem.
Notation pallas_feval_unfold           := G1_feval_unfold.
Notation pallas_tight_bounds_iff_valid := G1_tight_bounds_iff_valid.
