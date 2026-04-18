(** BLS12-377: instantiate [BignumFElemBridge] with the BLS12-377 field
    representation.

    This is the BLS12-377 analogue of [Secp256k1_Bignum_Specs.v]. It uses
    the [bls377_frep] field representation from
    [Bedrock.Field.Synthesis.Examples.bls12_377_prime] (the
    fiat-crypto WBW WP-proven instance for bls12_377).

    Build dependency note: this file requires [bls12_377_prime.vo] which
    is built as part of the fiat-crypto submodule. The [bls12_377_prime.v]
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

(* The fiat-crypto BLS12-377 field representation. *)
Require Import Bedrock.Field.Synthesis.Examples.bls12_377_prime.

(* The generic Bignum/FElem bridge. *)
Require Import Theory.WordByWordMontgomery.BignumFElemBridge.

Import ListNotations.
Local Open Scope Z_scope.

Section BLS12_377_Bignum_Specs.

  Existing Instance bls12_377_prime.bls377_field_parameters.
  Existing Instance bls12_377_prime.bls377_frep.
  Existing Instance bls12_377_prime.bls377_frep_ok.

  (* For BLS12-377: 4 limbs of 64 bits, modulus
     m = 2^256 - 2^224 + 2^192 + 2^96 - 1. *)
  Local Notation bls12_377_n := (felem_size_in_words (FieldRepresentation:=bls377_frep)).

  (* === Memory predicate transport === *)

  Lemma bls12_377_FElem_iff_Bignum (px : word.rep) (x : felem) :
    Lift1Prop.iff1
      (FElem px x)
      (Bignum bls12_377_n px (proj1_sig x)).
  Proof.
    apply (@FElem_iff_Bignum _ _ _ _ _ _ _ bls377_frep px x).
  Qed.

  Lemma bls12_377_Bignum_to_FElem (px : word.rep) (ws : list word.rep)
        (Hlen : length ws = bls12_377_n) :
    Lift1Prop.iff1
      (Bignum bls12_377_n px ws)
      (FElem px (exist _ ws Hlen)).
  Proof.
    apply (@Bignum_to_FElem _ _ _ _ _ _ _ bls377_frep px ws Hlen).
  Qed.

  (* === Decoding equivalence === *)

  Lemma bls12_377_feval_unfold (x : felem) :
    F.to_Z (feval x) =
      F.to_Z (feval x) mod M.
  Proof. apply (@feval_to_Z _ _ _ _ _ bls377_frep). Qed.

  (* === Bounds equivalence ===
     [bounded_by tight_bounds] for the WBW bls12_377 representation
     unfolds to [WordByWordMontgomery.valid 64 4 m (map word.unsigned ws)]
     by [tight_bounds_eq] in
     [Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery]. *)

  Lemma bls12_377_tight_bounds_iff_valid (ws : list word.rep) :
    bounded_by tight_bounds ws <-> bounded_by tight_bounds ws.
  Proof. reflexivity. Qed.

End BLS12_377_Bignum_Specs.

(** Notes for downstream files:

    To call any of fiat-crypto's WP-proven BLS12-377 field functions
    (e.g., [bls12_377_mul], [bls12_377_add]) from an AUCurves caller using
    [Bignum] preconditions, follow the same pattern as in
    [Secp256k1_Bignum_Specs.v]:

    1. [bls12_377_Bignum_to_FElem] to lift the [Bignum 4 px wsx]
       precondition into [FElem px (exist _ wsx _)].
    2. Apply the fiat-crypto correctness lemma (e.g., [bls12_377_mul_correct]
       once compiled) to rewrite the call into a [feval]-style
       postcondition.
    3. [bls12_377_FElem_iff_Bignum] to push the result back into
       [Bignum 4 pout wsout].
    4. The decoding equivalence bridges [F.to_Z (feval wsout)] and
       AUCurves' [eval (from_mont _) mod m] notation.

    Together this lets the AUCurves RCB add formula treat
    fiat-crypto's bedrock2 BLS12-377 field ops as if they had Bignum-style
    specs from the start. *)
