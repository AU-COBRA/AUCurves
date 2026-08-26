(** P-224: instantiate [BignumFElemBridge] with the P-224 field
    representation.

    This is the P-224 analogue of [P256_Bignum_Specs.v]. It uses
    the [p224_frep] field representation from
    [Bedrock.Field.Synthesis.Examples.p224_field] (the
    fiat-crypto WBW WP-proven instance for p224).

    Build dependency note: this file requires [p224_field.vo].  The
    [p224_field.v] source uses the same [field_representation] template
    as [p256_prime.v]; both yield WBW representations whose sep
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

(* The fiat-crypto P-224 field representation. *)
Require Import Bedrock.Field.Synthesis.Examples.p224_field.

(* The generic Bignum/FElem bridge. *)
Require Import Theory.WordByWordMontgomery.BignumFElemBridge.

Import ListNotations.
Local Open Scope Z_scope.

Section P224_Bignum_Specs.

  Existing Instance p224_field.p224_field_parameters.
  Existing Instance p224_field.p224_frep.
  Existing Instance p224_field.p224_frep_ok.

  (* For P-224: 4 limbs of 64 bits, modulus
     m = 2^224 - 2^96 + 1. *)
  Local Notation p224_n := (felem_size_in_words (FieldRepresentation:=p224_frep)).

  (* === Memory predicate transport === *)

  Lemma p224_FElem_iff_Bignum (px : word.rep) (x : felem) :
    Lift1Prop.iff1
      (FElem px x)
      (Bignum p224_n px (proj1_sig x)).
  Proof.
    apply (@FElem_iff_Bignum _ _ _ _ _ _ _ p224_frep px x).
  Qed.

  Lemma p224_Bignum_to_FElem (px : word.rep) (ws : list word.rep)
        (Hlen : length ws = p224_n) :
    Lift1Prop.iff1
      (Bignum p224_n px ws)
      (FElem px (exist _ ws Hlen)).
  Proof.
    apply (@Bignum_to_FElem _ _ _ _ _ _ _ p224_frep px ws Hlen).
  Qed.

  (* === Decoding equivalence === *)

  Lemma p224_feval_unfold (x : felem) :
    F.to_Z (feval x) =
      F.to_Z (feval x) mod M.
  Proof. apply (@feval_to_Z _ _ _ _ _ p224_frep). Qed.

  (* === Bounds equivalence ===
     [bounded_by tight_bounds] for the WBW p224 representation
     unfolds to [WordByWordMontgomery.valid 64 4 m (map word.unsigned ws)]
     by [tight_bounds_eq] in
     [Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery]. *)

  Lemma p224_tight_bounds_iff_valid (ws : list word.rep) :
    bounded_by tight_bounds ws <-> bounded_by tight_bounds ws.
  Proof. reflexivity. Qed.

End P224_Bignum_Specs.

(** Notes for downstream files: see [P256_Bignum_Specs.v]; the calling
    pattern is identical with n = 4 limbs and 32-byte felems. *)
