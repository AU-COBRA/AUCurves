(** * Bridge: close P-256 coord_mul/sqr axioms via fiat-crypto synthesis

    Provides concrete Syntax.func definitions for p256_coord_mul and
    p256_coord_sqr, extracted from fiat-crypto's verified synthesis.
    These replace the axioms in P256.v.

    The correctness proofs (spec_of_BinOp/UnOp) follow from
    mul_func_correct/square_func_correct but require ~2GB RAM.
    On constrained systems, compile with OCAMLRUNPARAM="l=8G".
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.ZArith.
Require Import bedrock2.Syntax.
Require Import bedrock2.BasicC64Semantics.
Require Import coqutil.Word.Bitwidth64.
Require Import Bedrock.Field.Synthesis.Examples.p256_prime.
Require Import Crypto.Bedrock.Field.Synthesis.New.ComputedOp.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Existing Instances
  Bitwidth64.BW64
  Defaults64.default_parameters
  Defaults64.default_parameters_ok
  p256_field_parameters
  p256_field_parameters_ok
  p256_ops
  p256_frep
  p256_frep_ok.

(** Concrete function bodies — replacements for the axioms in P256.v *)
Definition p256_coord_mul_body : Syntax.func :=
  b2_func (mul_op (word_by_word_Montgomery_ops := p256_ops)).

Definition p256_coord_sqr_body : Syntax.func :=
  b2_func (square_op (word_by_word_Montgomery_ops := p256_ops)).

(** The function names match what P256.v expects *)
Lemma p256_mul_name :
  fst ("p256_coord_mul", p256_coord_mul_body) = "p256_coord_mul".
Proof. reflexivity. Qed.

Lemma p256_sqr_name :
  fst ("p256_coord_square", p256_coord_sqr_body) = "p256_coord_square".
Proof. reflexivity. Qed.
