(** Pallas: instantiate [BignumFElemBridge] with the Pallas field
    representation.

    Pallas analogue of [P256_Bignum_Specs.v] and [Secp256k1_Bignum_Specs.v].
    Uses the [pallas_frep] field representation from
    [Bedrock.Field.Synthesis.Examples.pallas_prime] (the fiat-crypto
    WBW WP-proven instance for Pallas).

    Pallas prime modulus:
      m = 2^254 + 45560315531506369815346746415080538113
        = 0x4000...00224698fc094cf91b992d30ed00000001 *)

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

(* The fiat-crypto Pallas field representation. *)
Require Import Bedrock.Field.Synthesis.Examples.pallas_prime.

(* The generic Bignum/FElem bridge. *)
Require Import Theory.WordByWordMontgomery.BignumFElemBridge.

Import ListNotations.
Local Open Scope Z_scope.

Section Pallas_Bignum_Specs.

  Existing Instance pallas_prime.pallas_field_parameters.
  Existing Instance pallas_prime.pallas_frep.
  Existing Instance pallas_prime.pallas_frep_ok.

  (* Pallas: 4 limbs of 64 bits, modulus as above. *)
  Local Notation pallas_n := (felem_size_in_words (FieldRepresentation:=pallas_frep)).

  (* === Memory predicate transport === *)

  Lemma pallas_FElem_iff_Bignum (px : word.rep) (x : felem) :
    Lift1Prop.iff1
      (FElem px x)
      (Bignum pallas_n px (proj1_sig x)).
  Proof.
    apply (@FElem_iff_Bignum _ _ _ _ _ _ _ pallas_frep px x).
  Qed.

  Lemma pallas_Bignum_to_FElem (px : word.rep) (ws : list word.rep)
        (Hlen : length ws = pallas_n) :
    Lift1Prop.iff1
      (Bignum pallas_n px ws)
      (FElem px (exist _ ws Hlen)).
  Proof.
    apply (@Bignum_to_FElem _ _ _ _ _ _ _ pallas_frep px ws Hlen).
  Qed.

  (* === Decoding equivalence === *)

  Lemma pallas_feval_unfold (x : felem) :
    F.to_Z (feval x) =
      F.to_Z (feval x) mod M.
  Proof. apply (@feval_to_Z _ _ _ _ _ pallas_frep). Qed.

  (* === Bounds equivalence ===
     [bounded_by tight_bounds] for the WBW Pallas representation
     unfolds to [WordByWordMontgomery.valid 64 4 m (map word.unsigned ws)]
     by [tight_bounds_eq] in
     [Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery]. *)

  Lemma pallas_tight_bounds_iff_valid (ws : list word.rep) :
    bounded_by tight_bounds ws <-> bounded_by tight_bounds ws.
  Proof. reflexivity. Qed.

End Pallas_Bignum_Specs.

(** Notes for downstream files:

    To call any of fiat-crypto's WP-proven Pallas field functions
    (e.g., [pallas_mul], [pallas_add]) from an AUCurves caller using
    [Bignum] preconditions, follow the same pattern as in
    [P256_Bignum_Specs.v] / [Secp256k1_Bignum_Specs.v]:

    1. [pallas_Bignum_to_FElem] to lift the [Bignum 4 px wsx]
       precondition into [FElem px (exist _ wsx _)].
    2. Apply the fiat-crypto correctness lemma (e.g., [pallas_mul_correct]
       once compiled) to rewrite the call into a [feval]-style
       postcondition.
    3. [pallas_FElem_iff_Bignum] to push the result back into
       [Bignum 4 pout wsout].
    4. The decoding equivalence bridges [F.to_Z (feval wsout)] and
       AUCurves' [eval (from_mont _) mod m] notation.

    Together this lets the AUCurves RCB add formula treat
    fiat-crypto's bedrock2 Pallas field ops as if they had Bignum-style
    specs from the start. *)
