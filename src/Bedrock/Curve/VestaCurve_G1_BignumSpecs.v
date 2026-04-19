(** Thin Vesta wrapper over the generic [WbwMontgomeryG1_BignumSpecs]
    Section. Collapses the old ~100 LoC clone file to a ~15 LoC
    import + re-export under legacy vesta_* names. *)

Require Import Crypto.Bedrock.Specs.Field.
Require Import Bedrock.Field.Synthesis.Examples.vesta_prime.
Require Import Bedrock.Curve.WbwMontgomeryG1_BignumSpecs.

Existing Instance vesta_prime.vesta_field_parameters.
Existing Instance vesta_prime.vesta_frep.
Existing Instance vesta_prime.vesta_frep_ok.

(** Backward-compat aliases for the old vesta_* names. *)
Notation vesta_n                      := (felem_size_in_words (FieldRepresentation := vesta_prime.vesta_frep)).
Notation vesta_FElem_iff_Bignum       := G1_FElem_iff_Bignum.
Notation vesta_Bignum_to_FElem        := G1_Bignum_to_FElem.
Notation vesta_feval_unfold           := G1_feval_unfold.
Notation vesta_tight_bounds_iff_valid := G1_tight_bounds_iff_valid.
