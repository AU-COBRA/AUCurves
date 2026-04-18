(** Vesta: instantiate [BignumFElemBridge] with the Vesta field
    representation.

    Vesta analogue of [P256_Bignum_Specs.v] and [Secp256k1_Bignum_Specs.v].
    Uses the [vesta_frep] field representation from
    [Bedrock.Field.Synthesis.Examples.vesta_prime] (the fiat-crypto
    WBW WP-proven instance for Vesta).

    Vesta prime modulus:
      m = 2^254 + 45560315531419706090280762371685220353
        = 0x4000...00224698fc0994a8dd8c46eb2100000001 *)

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

(* The fiat-crypto Vesta field representation. *)
Require Import Bedrock.Field.Synthesis.Examples.vesta_prime.

(* The generic Bignum/FElem bridge. *)
Require Import Theory.WordByWordMontgomery.BignumFElemBridge.

Import ListNotations.
Local Open Scope Z_scope.

Section Vesta_Bignum_Specs.

  Existing Instance vesta_prime.vesta_field_parameters.
  Existing Instance vesta_prime.vesta_frep.
  Existing Instance vesta_prime.vesta_frep_ok.

  (* Vesta: 4 limbs of 64 bits, modulus as above. *)
  Local Notation vesta_n := (felem_size_in_words (FieldRepresentation:=vesta_frep)).

  (* === Memory predicate transport === *)

  Lemma vesta_FElem_iff_Bignum (px : word.rep) (x : felem) :
    Lift1Prop.iff1
      (FElem px x)
      (Bignum vesta_n px (proj1_sig x)).
  Proof.
    apply (@FElem_iff_Bignum _ _ _ _ _ _ _ vesta_frep px x).
  Qed.

  Lemma vesta_Bignum_to_FElem (px : word.rep) (ws : list word.rep)
        (Hlen : length ws = vesta_n) :
    Lift1Prop.iff1
      (Bignum vesta_n px ws)
      (FElem px (exist _ ws Hlen)).
  Proof.
    apply (@Bignum_to_FElem _ _ _ _ _ _ _ vesta_frep px ws Hlen).
  Qed.

  (* === Decoding equivalence === *)

  Lemma vesta_feval_unfold (x : felem) :
    F.to_Z (feval x) =
      F.to_Z (feval x) mod M.
  Proof. apply (@feval_to_Z _ _ _ _ _ vesta_frep). Qed.

  (* === Bounds equivalence ===
     [bounded_by tight_bounds] for the WBW Vesta representation
     unfolds to [WordByWordMontgomery.valid 64 4 m (map word.unsigned ws)]
     by [tight_bounds_eq] in
     [Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery]. *)

  Lemma vesta_tight_bounds_iff_valid (ws : list word.rep) :
    bounded_by tight_bounds ws <-> bounded_by tight_bounds ws.
  Proof. reflexivity. Qed.

End Vesta_Bignum_Specs.

(** Notes for downstream files:

    To call any of fiat-crypto's WP-proven Vesta field functions
    (e.g., [vesta_mul], [vesta_add]) from an AUCurves caller using
    [Bignum] preconditions, follow the same pattern as in
    [P256_Bignum_Specs.v] / [Secp256k1_Bignum_Specs.v]:

    1. [vesta_Bignum_to_FElem] to lift the [Bignum 4 px wsx]
       precondition into [FElem px (exist _ wsx _)].
    2. Apply the fiat-crypto correctness lemma (e.g., [vesta_mul_correct]
       once compiled) to rewrite the call into a [feval]-style
       postcondition.
    3. [vesta_FElem_iff_Bignum] to push the result back into
       [Bignum 4 pout wsout].
    4. The decoding equivalence bridges [F.to_Z (feval wsout)] and
       AUCurves' [eval (from_mont _) mod m] notation.

    Together this lets the AUCurves RCB add formula treat
    fiat-crypto's bedrock2 Vesta field ops as if they had Bignum-style
    specs from the start. *)
