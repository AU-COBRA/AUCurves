(** Wired Bignum-style spec instances for BN446 field operations.

    BN446 analogue of [Secbn446k1_Wired_Specs.v]. Uses the
    [bn446_frep] field representation from
    [Bedrock.Field.Synthesis.Examples.bn446_prime] and exposes
    the synthesized [bn446_mul], [bn446_add], etc. as Bignum-style
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
Require Import Bedrock.Field.Synthesis.Examples.bn446_prime.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Theory.WordByWordMontgomery.BignumFElemBridge.
Require Import Bedrock.Curve.BN446Curve_G1_BignumSpecs.

Import ListNotations.
Local Open Scope Z_scope.

Existing Instance bn446_prime.bn446_field_parameters.
Existing Instance bn446_prime.bn446_frep.
Existing Instance bn446_prime.bn446_frep_ok.

Local Notation m := 0x2400000000000000002400000002d00000000d800000021c0000001800000000870000000b0400000057c00000015c000000132000000067%Z.
Local Notation n := 7%nat.
Local Notation bw := 64%Z.
Local Notation bn446_m' := (@Field.m' bw bn446_field_parameters).
Notation eval := (@WordByWordMontgomery.WordByWordMontgomery.eval bw n).
Notation from_mont := (@WordByWordMontgomery.from_montgomerymod bw n m bn446_m').
Local Notation toZ := (List.map Interface.word.unsigned).

(** ** Concrete spec_of instances — use shared predicate bodies from
    [WbwMontgomeryG1_BignumSpecBodies]. *)

Require Import Bedrock.Curve.WbwMontgomeryG1_BignumSpecBodies.

Instance spec_of_bn446_mul_bignum    : spec_of "bn446_coord_mul"    := binop_mul_body.
Instance spec_of_bn446_add_bignum    : spec_of "bn446_coord_add"    := binop_add_body.
Instance spec_of_bn446_sub_bignum    : spec_of "bn446_coord_sub"    := binop_sub_body.
Instance spec_of_bn446_square_bignum : spec_of "bn446_coord_square" := unop_square_body.
Instance spec_of_bn446_opp_bignum    : spec_of "bn446_coord_opp"    := unop_opp_body.

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

Definition bn446_mul_bignum_correct :
  forall functions,
    spec_of_BinOp bin_mul (field_representation:=bn446_frep) functions ->
    spec_of_bn446_mul_bignum functions
  := mul_bignum_transport feval_wbw_def tight_of_valid valid_of_tight.

Definition bn446_add_bignum_correct :
  forall functions,
    spec_of_BinOp bin_add (field_representation:=bn446_frep) functions ->
    spec_of_bn446_add_bignum functions
  := add_bignum_transport feval_wbw_def tight_of_valid valid_of_loose.

Definition bn446_sub_bignum_correct :
  forall functions,
    spec_of_BinOp bin_sub (field_representation:=bn446_frep) functions ->
    spec_of_bn446_sub_bignum functions
  := sub_bignum_transport feval_wbw_def tight_of_valid valid_of_loose.

Definition bn446_square_bignum_correct :
  forall functions,
    spec_of_UnOp un_square (field_representation:=bn446_frep) functions ->
    spec_of_bn446_square_bignum functions
  := square_bignum_transport feval_wbw_def valid_of_tight loose_of_valid.

Definition bn446_opp_bignum_correct :
  forall functions,
    spec_of_UnOp un_opp (field_representation:=bn446_frep) functions ->
    spec_of_bn446_opp_bignum functions
  := opp_bignum_transport feval_wbw_def tight_of_valid valid_of_loose.
