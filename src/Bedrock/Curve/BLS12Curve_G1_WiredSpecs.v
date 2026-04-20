(** Wired Bignum-style spec instances for BLS12 field operations.

    BLS12 analogue of [Secp256k1_Wired_Specs.v]. Uses the
    [bls12_frep] field representation from
    [Bedrock.Field.Synthesis.Examples.bls12_prime] and exposes
    the synthesized [bls12_mul], [bls12_add], etc. as Bignum-style
    [spec_of] instances for AUCurves callers. *)

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
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Theory.WordByWordMontgomery.BignumFElemBridge.
Require Import Bedrock.Curve.BLS12Curve_G1_BignumSpecs.

Import ListNotations.
Local Open Scope Z_scope.

Existing Instance bls12_prime.bls12_field_parameters.
Existing Instance bls12_prime.bls12_frep.
Existing Instance bls12_prime.bls12_frep_ok.

Local Notation m := 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab%Z.
Local Notation n := 6%nat.
Local Notation bw := 64%Z.
Local Notation bls12_m' := (@Field.m' bw bls12_field_parameters).
Notation eval := (@WordByWordMontgomery.WordByWordMontgomery.eval bw n).
Notation from_mont := (@WordByWordMontgomery.from_montgomerymod bw n m bls12_m').
Local Notation toZ := (List.map Interface.word.unsigned).

(** ** Concrete spec_of instances — use shared predicate bodies from
    [WbwMontgomeryG1_BignumSpecBodies]. *)

Require Import Bedrock.Curve.WbwMontgomeryG1_BignumSpecBodies.

Instance spec_of_bls12_mul_bignum    : spec_of "bls12_coord_mul"    := binop_mul_body.
Instance spec_of_bls12_add_bignum    : spec_of "bls12_coord_add"    := binop_add_body.
Instance spec_of_bls12_sub_bignum    : spec_of "bls12_coord_sub"    := binop_sub_body.
Instance spec_of_bls12_square_bignum : spec_of "bls12_coord_square" := unop_square_body.
Instance spec_of_bls12_opp_bignum    : spec_of "bls12_coord_opp"    := unop_opp_body.

(** ** Bridge lemmas — use shared WbwMontgomeryG1_WiredBridges functor.
    Replaces ~80 LoC of identical-per-curve bridge lemmas with a functor
    application. *)

Require Import Bedrock.Curve.WbwMontgomeryG1_WiredBridges.

Local Lemma feval_wbw_def :
  forall ws, feval ws = F.of_Z M_pos (eval (from_mont (toZ ws))).
Proof. reflexivity. Qed.

Require Import Bedrock.Curve.WbwMontgomeryG1_Transports.

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

Definition bls12_mul_bignum_correct :
  forall functions,
    spec_of_BinOp bin_mul (field_representation:=bls12_frep) functions ->
    spec_of_bls12_mul_bignum functions
  := mul_bignum_transport feval_wbw_def tight_of_valid valid_of_tight.

Definition bls12_add_bignum_correct :
  forall functions,
    spec_of_BinOp bin_add (field_representation:=bls12_frep) functions ->
    spec_of_bls12_add_bignum functions
  := add_bignum_transport feval_wbw_def tight_of_valid valid_of_loose.

Definition bls12_sub_bignum_correct :
  forall functions,
    spec_of_BinOp bin_sub (field_representation:=bls12_frep) functions ->
    spec_of_bls12_sub_bignum functions
  := sub_bignum_transport feval_wbw_def tight_of_valid valid_of_loose.

Definition bls12_square_bignum_correct :
  forall functions,
    spec_of_UnOp un_square (field_representation:=bls12_frep) functions ->
    spec_of_bls12_square_bignum functions
  := square_bignum_transport feval_wbw_def valid_of_tight loose_of_valid.

Definition bls12_opp_bignum_correct :
  forall functions,
    spec_of_UnOp un_opp (field_representation:=bls12_frep) functions ->
    spec_of_bls12_opp_bignum functions
  := opp_bignum_transport feval_wbw_def tight_of_valid valid_of_loose.
