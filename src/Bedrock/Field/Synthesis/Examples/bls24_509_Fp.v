(** * BLS24-509 base field (Fp) synthesis via word-by-word Montgomery.
    509-bit prime, 8 × 64-bit limbs. *)

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
Require Import Bedrock.Field.Synthesis.Examples.bls24_509_prime.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.Syntax.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Local Open Scope string_scope.
Local Infix "*" := sep : sep_scope.
Delimit Scope sep_scope with sep.
Local Notation function_t := ((String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type).
Local Notation functions_t := (list function_t).
Local Open Scope sep_scope.
Local Open Scope Z_scope.

Section Field.
  (* BLS24-509: 509 bits = 8 × 64-bit words *)
  Definition n : nat := 8.
  Definition m : Z := bls24_509_modulus.

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters
    Defaults64.default_parameters_ok.

  Definition prefix : string := "bls24_509_"%string.

  Instance bls24_509_field_parameters : FieldParameters.
  Proof using Type.
    let M := (eval vm_compute in (Z.to_pos m)) in
    (* curve a parameter: a = 0 for y² = x³ + 1 *)
    let a := constr:(F.of_Z M 0) in
    let prefix := constr:("bls24_509_"%string) in
    eapply
      (field_parameters_prefixed
         M ((a - F.of_Z _ 2) / F.of_Z _ 4)%F prefix).
  Defined.

  Definition to_mont_string := prefix ++ "to_mont".
  Definition from_mont_string := prefix ++ "from_mont".

  (* Synthesize all field operations via word-by-word Montgomery *)
  Instance bls24_509_ops : @word_by_word_Montgomery_ops
    from_mont_string to_mont_string _ _ _ _ _ _ _ _ _ _
    (WordByWordMontgomery.n m machine_wordsize) m.
  Proof using Type. Time constructor; make_computed_op. Defined.

End Field.
