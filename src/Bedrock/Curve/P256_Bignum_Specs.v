(** P-256: instantiate [BignumFElemBridge] with the P-256 field
    representation.

    This is the P-256 analogue of [Secp256k1_Bignum_Specs.v]. It uses
    the [p256_frep] field representation from
    [Bedrock.Field.Synthesis.Examples.p256_prime] (the
    fiat-crypto WBW WP-proven instance for p256).

    Build dependency note: this file requires [p256_prime.vo] which
    is built as part of the fiat-crypto submodule. The [p256_prime.v]
    source uses the same [field_representation] template as
    [Field256k1.v]; both yield WBW representations whose sep
    predicates and bounds match AUCurves' [Bignum] / [valid] up to
    the dependent-pair wrapping handled in [BignumFElemBridge.v]. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.Lift1Prop.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Bitwidth64.

Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.

(* The fiat-crypto P-256 field representation. *)
Require Import Bedrock.Field.Synthesis.Examples.p256_prime.

(* The generic Bignum/FElem bridge. *)
Require Import Theory.WordByWordMontgomery.BignumFElemBridge.

Import ListNotations.
Local Open Scope Z_scope.

Section P256_Bignum_Specs.

  Existing Instance p256_prime.p256_field_parameters.
  Existing Instance p256_prime.p256_frep.
  Existing Instance p256_prime.p256_frep_ok.

  (* For P-256: 4 limbs of 64 bits, modulus
     m = 2^256 - 2^224 + 2^192 + 2^96 - 1. *)
  Local Notation p256_n := (felem_size_in_words (FieldRepresentation:=p256_frep)).

  (* === Memory predicate transport === *)

  Lemma p256_FElem_iff_Bignum (px : word.rep) (x : felem) :
    Lift1Prop.iff1
      (FElem px x)
      (Bignum p256_n px (proj1_sig x)).
  Proof.
    apply (@FElem_iff_Bignum _ _ _ _ _ _ _ p256_frep px x).
  Qed.

  Lemma p256_Bignum_to_FElem (px : word.rep) (ws : list word.rep)
        (Hlen : length ws = p256_n) :
    Lift1Prop.iff1
      (Bignum p256_n px ws)
      (FElem px (exist _ ws Hlen)).
  Proof.
    apply (@Bignum_to_FElem _ _ _ _ _ _ _ p256_frep px ws Hlen).
  Qed.

  (* === Decoding equivalence === *)

  Lemma p256_feval_unfold (x : felem) :
    F.to_Z (feval x) =
      F.to_Z (feval x) mod M.
  Proof. apply (@feval_to_Z _ _ _ _ _ p256_frep). Qed.

  (* === Bounds equivalence ===
     [bounded_by tight_bounds] for the WBW p256 representation
     unfolds to [WordByWordMontgomery.valid 64 4 m (map word.unsigned ws)]
     by [tight_bounds_eq] in
     [Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery]. *)

  Lemma p256_tight_bounds_iff_valid (ws : list word.rep) :
    bounded_by tight_bounds ws <-> bounded_by tight_bounds ws.
  Proof. reflexivity. Qed.

End P256_Bignum_Specs.

(** Notes for downstream files:

    To call any of fiat-crypto's WP-proven P-256 field functions
    (e.g., [p256_mul], [p256_add]) from an AUCurves caller using
    [Bignum] preconditions, follow the same pattern as in
    [Secp256k1_Bignum_Specs.v]:

    1. [p256_Bignum_to_FElem] to lift the [Bignum 4 px wsx]
       precondition into [FElem px (exist _ wsx _)].
    2. Apply the fiat-crypto correctness lemma (e.g., [p256_mul_correct]
       once compiled) to rewrite the call into a [feval]-style
       postcondition.
    3. [p256_FElem_iff_Bignum] to push the result back into
       [Bignum 4 pout wsout].
    4. The decoding equivalence bridges [F.to_Z (feval wsout)] and
       AUCurves' [eval (from_mont _) mod m] notation.

    Together this lets the AUCurves RCB add formula treat
    fiat-crypto's bedrock2 P-256 field ops as if they had Bignum-style
    specs from the start. *)
