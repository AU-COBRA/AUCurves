(** * P-256 (secp256r1) field synthesis via fiat-crypto Montgomery pipeline
    Generates bedrock2 bodies for field mul, square, add, sub, opp, etc.
    over the NIST P-256 prime: p = 2^256 - 2^224 + 2^192 + 2^96 - 1.

    This file bridges the gap between the axiomatized p256_coord_mul/sqr
    in src/Bedrock/P256.v and fiat-crypto's verified synthesis. *)

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

(* For primality certificate *)
From Coqprime.PrimalityTest Require Import Pocklington PocklingtonCertificat.

Local Open Scope string_scope.
Local Infix "*" := sep : sep_scope.
Delimit Scope sep_scope with sep.
Local Open Scope sep_scope.
Local Open Scope Z_scope.
Local Open Scope positive_scope.

Section Field.
  (* P-256 prime: 2^256 - 2^224 + 2^192 + 2^96 - 1 *)
  Definition p256_modulus : Z :=
    Eval vm_compute in (2^256 - 2^224 + 2^192 + 2^96 - 1)%Z.

  Definition m : Z := p256_modulus.

  (* Primality proof via Pocklington certificate *)
  Local Open Scope positive_scope.
  Instance prime_p256 : prime m.
  Proof.
    remember prime; vm_compute; subst.
    simple refine (Pocklington_refl
      (Pock_certif _ 6 [(6700417,1);(490463,1);(65537,1);(641,1);(257,1);(17,1);(5,2);(3,1);(2,1)] 0x6f199ff1e192ee086c186e)
      [ Pock_certif 6700417 5 [(3,1);(2,7)] 552;
        Pock_certif 490463 7 [(53,1);(2,1)] 174;
        Pock_certif 65537 3 [(2,16)] 1;
        Pock_certif 641 3 [(2,7)] 1;
        Pock_certif 257 3 [(2,8)] 1;
        Pock_certif 53 2 [(2,2)] 4;
        Pock_certif 17 3 [(2,4)] 1;
        Pock_certif 5 2 [(2,2)] 1;
        Proof_certif 3 prime_3;
        Proof_certif 2 prime_2] _)%positive.
    native_cast_no_check (@eq_refl bool true).
  Qed.

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters
    Defaults64.default_parameters_ok.

  Definition prefix : string := "p256_coord_".

  Instance p256_field_parameters : FieldParameters.
  Proof using Type.
    let M := (eval vm_compute in (Z.to_pos m)) in
    let a := constr:(F.of_Z M 0) in
    let prefix := constr:("p256_coord_"%string) in
    eapply (field_parameters_prefixed M a prefix).
  Defined.

  Instance p256_field_parameters_ok : FieldParameters_ok.
  Proof using Type.
    constructor.
    exact prime_p256.
  Qed.

  Definition to_mont_string := prefix ++ "to_mont".
  Definition from_mont_string := prefix ++ "from_mont".

  (* Synthesize all field operations via fiat-crypto pipeline.
     This runs the fiat-crypto word-by-word Montgomery pipeline for P-256
     with 4 limbs of 64 bits, producing bedrock2 bodies + correctness proofs
     for: mul, square, add, sub, opp, from_bytes, to_bytes, from_word, etc. *)
  Instance p256_ops : @word_by_word_Montgomery_ops
    from_mont_string to_mont_string _ _ _ _ _ _ _ _ _ _
    (WordByWordMontgomery.n m machine_wordsize) m.
  Proof using Type. Time constructor; make_computed_op. Defined.

  Instance p256_frep : FieldRepresentation := field_representation m.

  Instance p256_frep_ok : FieldRepresentation_ok (field_representation:=p256_frep).
  Proof.
    apply Crypto.Bedrock.Field.Synthesis.New.Signature.field_representation_ok.
    intros. assumption.
    let c := eval lazy in felem_size_in_bytes in change felem_size_in_bytes with c.
    Lia.lia.
  Defined.

End Field.
