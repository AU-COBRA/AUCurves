(** * P-384 (secp384r1) field synthesis via fiat-crypto Montgomery pipeline
    Generates bedrock2 bodies for field mul, square, add, sub, opp, etc.
    over the NIST P-384 prime: p = 2^384 - 2^128 - 2^96 + 2^32 - 1.

    P-384 analogue of [p256_prime.v].  Differences from the P-256 file:
      - 6 limbs of 64 bits instead of 4;
      - primality comes from [prime_p384] in [p384_prime.v], proved by
        the Pocklington certificate in [p384_prime_certif.v];
      - the synthesis step uses a local native_compute variant of
        [make_computed_op], copied from [bls12_377_prime.v] — the
        upstream vm_compute tactic is too slow on 6-limb primes. *)

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

(* Axiomatized primality (repo policy for P-384). *)
Require Import Bedrock.Field.Synthesis.Examples.p384_prime.

Local Open Scope string_scope.
Local Infix "*" := sep : sep_scope.
Delimit Scope sep_scope with sep.
Local Open Scope sep_scope.
Local Open Scope Z_scope.

Section Field.
  (* P-384 prime: 2^384 - 2^128 - 2^96 + 2^32 - 1 *)
  Definition m : Z := p384_prime.p384_modulus.

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters
    Defaults64.default_parameters_ok.

  Definition prefix : string := "p384_coord_".

  Instance p384_field_parameters : FieldParameters.
  Proof using Type.
    let M := (eval vm_compute in (Z.to_pos m)) in
    let a := constr:(F.of_Z M 0) in
    let prefix := constr:("p384_coord_"%string) in
    eapply (field_parameters_prefixed M a prefix).
  Defined.

  Instance p384_field_parameters_ok : FieldParameters_ok.
  Proof using Type.
    constructor.
    exact prime_p384.
  Qed.

  Definition to_mont_string := prefix ++ "to_mont".
  Definition from_mont_string := prefix ++ "from_mont".

  (* Synthesize all field operations via the fiat-crypto word-by-word
     Montgomery pipeline for P-384 with 6 limbs of 64 bits.

     Local native_compute variant of make_computed_op — the WBW synthesis
     on a 6-limb prime is far too slow under the upstream vm_compute
     (see bls12_377_prime.v, also a 6-limb prime).  Logically identical
     to the upstream make_computed_op tactic; only the reduction
     strategy differs. *)
  Local Ltac make_computed_op_native :=
    eapply Build_computed_op;
    lazymatch goal with
    | |- _ = ErrorT.Success _ => native_compute; reflexivity
    | _ => idtac
    end;
    native_compute; reflexivity.

  Instance p384_ops : @word_by_word_Montgomery_ops
    from_mont_string to_mont_string _ _ _ _ _ _ _ _ _ _
    (WordByWordMontgomery.n m machine_wordsize) m.
  Proof using Type. Time constructor; make_computed_op_native. Defined.

  Instance p384_frep : FieldRepresentation := field_representation m.

  Instance p384_frep_ok : FieldRepresentation_ok (field_representation:=p384_frep).
  Proof.
    apply Crypto.Bedrock.Field.Synthesis.New.Signature.field_representation_ok.
    intros. assumption.
    let c := eval lazy in felem_size_in_bytes in change felem_size_in_bytes with c.
    Lia.lia.
  Defined.

End Field.
