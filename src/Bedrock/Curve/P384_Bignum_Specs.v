(** P-384: instantiate [BignumFElemBridge] with the P-384 field
    representation.

    This is the P-384 analogue of [P256_Bignum_Specs.v]. It uses
    the [p384_frep] field representation from
    [Bedrock.Field.Synthesis.Examples.p384_field] (the
    fiat-crypto WBW WP-proven instance for p384).

    Build dependency note: this file requires [p384_field.vo].  The
    [p384_field.v] source uses the same [field_representation] template
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

(* The fiat-crypto P-384 field representation. *)
Require Import Bedrock.Field.Synthesis.Examples.p384_field.

(* The generic Bignum/FElem bridge. *)
Require Import Theory.WordByWordMontgomery.BignumFElemBridge.

Import ListNotations.
Local Open Scope Z_scope.

Section P384_Bignum_Specs.

  Existing Instance p384_field.p384_field_parameters.
  Existing Instance p384_field.p384_frep.
  Existing Instance p384_field.p384_frep_ok.

  (* For P-384: 6 limbs of 64 bits, modulus
     m = 2^384 - 2^128 - 2^96 + 2^32 - 1. *)
  Local Notation p384_n := (felem_size_in_words (FieldRepresentation:=p384_frep)).

  (* === Memory predicate transport === *)

  Lemma p384_FElem_iff_Bignum (px : word.rep) (x : felem) :
    Lift1Prop.iff1
      (FElem px x)
      (Bignum p384_n px (proj1_sig x)).
  Proof.
    apply (@FElem_iff_Bignum _ _ _ _ _ _ _ p384_frep px x).
  Qed.

  Lemma p384_Bignum_to_FElem (px : word.rep) (ws : list word.rep)
        (Hlen : length ws = p384_n) :
    Lift1Prop.iff1
      (Bignum p384_n px ws)
      (FElem px (exist _ ws Hlen)).
  Proof.
    apply (@Bignum_to_FElem _ _ _ _ _ _ _ p384_frep px ws Hlen).
  Qed.

  (* === Decoding equivalence === *)

  Lemma p384_feval_unfold (x : felem) :
    F.to_Z (feval x) =
      F.to_Z (feval x) mod M.
  Proof. apply (@feval_to_Z _ _ _ _ _ p384_frep). Qed.

  (* === Bounds equivalence ===
     [bounded_by tight_bounds] for the WBW p384 representation
     unfolds to [WordByWordMontgomery.valid 64 6 m (map word.unsigned ws)]
     by [tight_bounds_eq] in
     [Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery]. *)

  Lemma p384_tight_bounds_iff_valid (ws : list word.rep) :
    bounded_by tight_bounds ws <-> bounded_by tight_bounds ws.
  Proof. reflexivity. Qed.

End P384_Bignum_Specs.

(** Notes for downstream files: see [P256_Bignum_Specs.v]; the calling
    pattern is identical with n = 6 limbs and 48-byte felems. *)
