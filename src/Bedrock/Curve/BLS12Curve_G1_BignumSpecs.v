(** Thin BLS12 wrapper over the generic [WbwMontgomeryG1_BignumSpecs]
    Section. Collapses the old ~100 LoC clone file to a ~15 LoC
    import + re-export under legacy bls12_* names. *)

Require Import Crypto.Bedrock.Specs.Field.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Curve.WbwMontgomeryG1_BignumSpecs.

Existing Instance bls12_prime.bls12_field_parameters.
Existing Instance bls12_prime.bls12_frep.
Existing Instance bls12_prime.bls12_frep_ok.

(** Backward-compat aliases for the old bls12_* names. *)
Notation bls12_n                      := (felem_size_in_words (FieldRepresentation := bls12_prime.bls12_frep)).
Notation bls12_FElem_iff_Bignum       := G1_FElem_iff_Bignum.
Notation bls12_Bignum_to_FElem        := G1_Bignum_to_FElem.
Notation bls12_feval_unfold           := G1_feval_unfold.
Notation bls12_tight_bounds_iff_valid := G1_tight_bounds_iff_valid.
