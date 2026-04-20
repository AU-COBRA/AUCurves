(** Wired Bignum-style spec instances for BW6_761 field operations.

    Uses the shared WbwMontgomeryG1_* functors:
    - [WbwMontgomeryG1_BignumSpecBodies] for the 5 spec bodies
    - [WbwMontgomeryG1_Transports] for the 5 transport lemmas

    BW6-761: 12 x 64-bit words, 761-bit prime. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Memory.
Require Import bedrock2.Semantics.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.BasicC64Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.ArrayCasts.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Bedrock.Field.Synthesis.Examples.bw6_761_prime.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Theory.WordByWordMontgomery.BignumFElemBridge.
Require Import Bedrock.Curve.BW6_761Curve_G1_BignumSpecs.

Import ListNotations.
Local Open Scope Z_scope.

Existing Instance bw6_761_prime.bw6_761_field_parameters.
Existing Instance bw6_761_prime.bw6_761_frep.
Existing Instance bw6_761_prime.bw6_761_frep_ok.

Local Notation m := 0x122e824fb83ce0ad187c94004faff3eb926186a81d14688528275ef8087be41707ba638e584e91903cebaff25b423048689c8ed12f9fd9071dcd3dc73ebff2e98a116c25667a8f8160cf8aeeaf0a437e6913e6870000082f49d00000000008b%Z.
Local Notation n := 12%nat.
Local Notation bw := 64%Z.
Local Notation bw6_761_m' := (@Field.m' bw bw6_761_field_parameters).
Notation eval := (@WordByWordMontgomery.WordByWordMontgomery.eval bw n).
Notation from_mont := (@WordByWordMontgomery.from_montgomerymod bw n m bw6_761_m').
Local Notation toZ := (List.map Interface.word.unsigned).

(** ** Concrete spec_of instances — use shared predicate bodies. *)

Require Import Bedrock.Curve.WbwMontgomeryG1_BignumSpecBodies.

Instance spec_of_bw6_761_mul_bignum    : spec_of "bw6_761_coord_mul"    := binop_mul_body.
Instance spec_of_bw6_761_add_bignum    : spec_of "bw6_761_coord_add"    := binop_add_body.
Instance spec_of_bw6_761_sub_bignum    : spec_of "bw6_761_coord_sub"    := binop_sub_body.
Instance spec_of_bw6_761_square_bignum : spec_of "bw6_761_coord_square" := unop_square_body.
Instance spec_of_bw6_761_opp_bignum    : spec_of "bw6_761_coord_opp"    := unop_opp_body.

(** ** Bridge + transport — use shared functors. *)

Require Import Bedrock.Curve.WbwMontgomeryG1_WiredBridges.
Require Import Bedrock.Curve.WbwMontgomeryG1_Transports.

Local Lemma feval_wbw_def :
  forall ws, feval ws = F.of_Z M_pos (eval (from_mont (toZ ws))).
Proof. reflexivity. Qed.

(** For WBW curves, [bounded_by tight_bounds], [bounded_by loose_bounds]
    and [WordByWordMontgomery.valid] coincide definitionally. *)
Local Lemma tight_of_valid :
  forall ws, WordByWordMontgomery.valid bw n m (toZ ws) ->
             bounded_by tight_bounds ws.
Proof. intros ws H; exact H. Qed.
Local Lemma valid_of_tight :
  forall ws, bounded_by tight_bounds ws ->
             WordByWordMontgomery.valid bw n m (toZ ws).
Proof. intros ws H; exact H. Qed.
Local Lemma valid_of_loose :
  forall ws, bounded_by loose_bounds ws ->
             WordByWordMontgomery.valid bw n m (toZ ws).
Proof. intros ws H; exact H. Qed.
Local Lemma loose_of_valid :
  forall ws, WordByWordMontgomery.valid bw n m (toZ ws) ->
             bounded_by loose_bounds ws.
Proof. intros ws H; exact H. Qed.

(** ** Transport lemmas -- via shared transport functor. *)

Definition bw6_761_mul_bignum_correct :
  forall functions,
    spec_of_BinOp bin_mul (field_representation:=bw6_761_frep) functions ->
    spec_of_bw6_761_mul_bignum functions
  := mul_bignum_transport feval_wbw_def tight_of_valid valid_of_tight.

Definition bw6_761_add_bignum_correct :
  forall functions,
    spec_of_BinOp bin_add (field_representation:=bw6_761_frep) functions ->
    spec_of_bw6_761_add_bignum functions
  := add_bignum_transport feval_wbw_def tight_of_valid valid_of_loose.

Definition bw6_761_sub_bignum_correct :
  forall functions,
    spec_of_BinOp bin_sub (field_representation:=bw6_761_frep) functions ->
    spec_of_bw6_761_sub_bignum functions
  := sub_bignum_transport feval_wbw_def tight_of_valid valid_of_loose.

Definition bw6_761_square_bignum_correct :
  forall functions,
    spec_of_UnOp un_square (field_representation:=bw6_761_frep) functions ->
    spec_of_bw6_761_square_bignum functions
  := square_bignum_transport feval_wbw_def valid_of_tight loose_of_valid.

Definition bw6_761_opp_bignum_correct :
  forall functions,
    spec_of_UnOp un_opp (field_representation:=bw6_761_frep) functions ->
    spec_of_bw6_761_opp_bignum functions
  := opp_bignum_transport feval_wbw_def tight_of_valid valid_of_loose.
