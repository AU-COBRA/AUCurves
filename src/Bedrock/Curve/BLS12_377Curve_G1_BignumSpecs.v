(** Thin BLS12_377 wrapper over the generic [WbwMontgomeryG1_BignumSpecs]
    Section. Collapses the old ~100 LoC clone file to a ~15 LoC
    import + re-export under legacy bls377_* names. *)

Require Import Crypto.Bedrock.Specs.Field.
Require Import Bedrock.Field.Synthesis.Examples.bls12_377_prime.
Require Import Bedrock.Curve.WbwMontgomeryG1_BignumSpecs.

Existing Instance bls12_377_prime.bls377_field_parameters.
Existing Instance bls12_377_prime.bls377_frep.
Existing Instance bls12_377_prime.bls377_frep_ok.

(** Backward-compat aliases for the old bls377_* names. *)
Notation bls377_n                      := (felem_size_in_words (FieldRepresentation := bls12_377_prime.bls377_frep)).
Notation bls377_FElem_iff_Bignum       := G1_FElem_iff_Bignum.
Notation bls377_Bignum_to_FElem        := G1_Bignum_to_FElem.
Notation bls377_feval_unfold           := G1_feval_unfold.
Notation bls377_tight_bounds_iff_valid := G1_tight_bounds_iff_valid.
