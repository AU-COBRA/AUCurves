(** Wired Bignum-style spec instances for P-256 field operations.

    P-256 analogue of [Secp256k1_Wired_Specs.v]. Uses the
    [p256_frep] field representation from
    [Crypto.Bedrock.Field.Synthesis.Examples.p256_prime] and exposes
    the synthesized [p256_mul], [p256_add], etc. as Bignum-style
    [spec_of] instances for AUCurves callers.

    See [Secp256k1_Wired_Specs.v] for the full composition recipe;
    P-256 is identical except for the modulus and the p256_*
    function names. *)

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
Require Import bedrock2.Syntax.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Bitwidth64.

Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.p256_prime.

Require Import Theory.WordByWordMontgomery.BignumFElemBridge.
Require Import Bedrock.Curve.P256_Bignum_Specs.
Require Import Bedrock.Curve.Secp256k1_Wired_Specs.
  (* re-uses bignum_binop_spec / bignum_unop_spec templates *)

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Section P256_Wired_Specs.

  Existing Instance p256_prime.p256_field_parameters.
  Existing Instance p256_prime.p256_frep.
  Existing Instance p256_prime.p256_frep_ok.

  (* P-256 modulus: m = 2^256 - 2^224 + 2^192 + 2^96 - 1 *)
  Local Notation p256_m :=
    (2^256 - 2^224 + 2^192 + 2^96 - 1)%Z.
  Local Notation p256_n := 4%nat.

  (** ** Concrete spec_of instances for the P-256 field operations *)

  Instance spec_of_p256_mul_bignum :
    spec_of "p256_mul" :=
    bignum_binop_spec p256_n p256_m
      (fun a b => (a * b) mod p256_m) "p256_mul".

  Instance spec_of_p256_add_bignum :
    spec_of "p256_add" :=
    bignum_binop_spec p256_n p256_m
      (fun a b => (a + b) mod p256_m) "p256_add".

  Instance spec_of_p256_sub_bignum :
    spec_of "p256_sub" :=
    bignum_binop_spec p256_n p256_m
      (fun a b => (a - b) mod p256_m) "p256_sub".

  Instance spec_of_p256_square_bignum :
    spec_of "p256_square" :=
    bignum_unop_spec p256_n p256_m
      (fun a => (a * a) mod p256_m) "p256_square".

  Instance spec_of_p256_opp_bignum :
    spec_of "p256_opp" :=
    bignum_unop_spec p256_n p256_m
      (fun a => (- a) mod p256_m) "p256_opp".

  (** ** Per-op transport statements (analogous to secp256k1) *)

  Definition p256_mul_bignum_correct_stmt :=
    forall functions,
      (forall functions',
          Interface.map.get functions' "p256_mul" =
          Interface.map.get functions "p256_mul" ->
          spec_of_BinOp bin_mul (field_representation:=p256_frep) functions') ->
      spec_of_p256_mul_bignum functions.

  Definition p256_add_bignum_correct_stmt :=
    forall functions,
      (forall functions',
          Interface.map.get functions' "p256_add" =
          Interface.map.get functions "p256_add" ->
          spec_of_BinOp bin_add (field_representation:=p256_frep) functions') ->
      spec_of_p256_add_bignum functions.

  Definition p256_sub_bignum_correct_stmt :=
    forall functions,
      (forall functions',
          Interface.map.get functions' "p256_sub" =
          Interface.map.get functions "p256_sub" ->
          spec_of_BinOp bin_sub (field_representation:=p256_frep) functions') ->
      spec_of_p256_sub_bignum functions.

  Definition p256_square_bignum_correct_stmt :=
    forall functions,
      (forall functions',
          Interface.map.get functions' "p256_square" =
          Interface.map.get functions "p256_square" ->
          spec_of_UnOp un_square (field_representation:=p256_frep) functions') ->
      spec_of_p256_square_bignum functions.

  Definition p256_opp_bignum_correct_stmt :=
    forall functions,
      (forall functions',
          Interface.map.get functions' "p256_opp" =
          Interface.map.get functions "p256_opp" ->
          spec_of_UnOp un_opp (field_representation:=p256_frep) functions') ->
      spec_of_p256_opp_bignum functions.

End P256_Wired_Specs.

(** Composition recipe (identical to secp256k1):

    To prove that the fiat-crypto-derived P-256 functions satisfy
    these Bignum-style instances, follow the recipe documented in
    [Secp256k1_Wired_Specs.v], substituting [p256_*_correct] for
    [secp256k1_*_correct] and [p256_FElem_iff_Bignum] for
    [secp256k1_FElem_iff_Bignum]. The bridge lemmas are identical
    in shape; only the field instance changes. *)
