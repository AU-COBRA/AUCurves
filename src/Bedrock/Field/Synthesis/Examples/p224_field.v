(** * P-224 (secp224r1) field synthesis via fiat-crypto Montgomery pipeline
    Generates bedrock2 bodies for field mul, square, add, sub, opp, etc.
    over the NIST P-224 prime: p = 2^224 - 2^96 + 1.

    P-224 analogue of [p256_prime.v].  Differences from the P-256 file:
      - primality comes from [prime_p224] in [p224_prime.v], proved by
        the Pocklington certificate in [p224_prime_certif.v];
      - same 4 limbs of 64 bits, so the upstream vm_compute
        [make_computed_op] tactic is used unchanged (the native_compute
        variant of [p384_field.v] is only needed at 6 limbs). *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Synthesis.New.ComputedOp.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Bedrock.Specs.Field.
Import ListNotations.
Require Import Crypto.Bedrock.Field.Translation.Proofs.ValidComputable.Func.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.Syntax.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.

(* Axiomatized primality (repo policy for P-224). *)
Require Import Bedrock.Field.Synthesis.Examples.p224_prime.

Local Open Scope string_scope.
Local Infix "*" := sep : sep_scope.
Delimit Scope sep_scope with sep.
Local Open Scope sep_scope.
Local Open Scope Z_scope.

Section Field.
  (* P-224 prime: 2^224 - 2^96 + 1 *)
  Definition m : Z := p224_prime.p224_modulus.

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters
    Defaults64.default_parameters_ok.

  Definition prefix : string := "p224_coord_".

  Instance p224_field_parameters : FieldParameters.
  Proof using Type.
    let M := (eval vm_compute in (Z.to_pos m)) in
    let a := constr:(F.of_Z M 0) in
    let prefix := constr:("p224_coord_"%string) in
    eapply (field_parameters_prefixed M a prefix).
  Defined.

  Instance p224_field_parameters_ok : FieldParameters_ok.
  Proof using Type.
    constructor.
    exact prime_p224.
  Qed.

  Definition to_mont_string := prefix ++ "to_mont".
  Definition from_mont_string := prefix ++ "from_mont".

  (* Synthesize all field operations via the fiat-crypto word-by-word
     Montgomery pipeline for P-224 with 4 limbs of 64 bits, producing
     bedrock2 bodies + correctness proofs for: mul, square, add, sub,
     opp, from_bytes, to_bytes, from_word, etc. *)
  Instance p224_ops : @word_by_word_Montgomery_ops
    from_mont_string to_mont_string _ _ _ _ _ _ _ _ _ _
    (WordByWordMontgomery.n m machine_wordsize) m.
  Proof using Type. Time constructor; make_computed_op. Defined.

  Instance p224_frep : FieldRepresentation := field_representation m.

  Instance p224_frep_ok : FieldRepresentation_ok (field_representation:=p224_frep).
  Proof.
    apply Crypto.Bedrock.Field.Synthesis.New.Signature.field_representation_ok.
    intros. assumption.
    let c := eval lazy in felem_size_in_bytes in change felem_size_in_bytes with c.
    Lia.lia.
  Defined.

End Field.
