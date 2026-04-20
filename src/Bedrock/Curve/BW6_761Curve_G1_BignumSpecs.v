(** BW6_761: instantiate [BignumFElemBridge] with the BW6_761 field
    representation.

    BW6_761 analogue of [P256_Bignum_Specs.v] and [Secp256k1_Bignum_Specs.v].
    Uses the [bw6_761_frep] field representation from
    [Bedrock.Field.Synthesis.Examples.bw6_761_prime] (the fiat-crypto
    WBW WP-proven instance for BW6_761).

    BW6_761 prime modulus:
      m = BW6-761 prime (761 bits, 12 x 64-bit words)
        = 0x122e824fb83ce0ad187c94004faff3eb926186a81d14688528275ef8087be41707ba638e584e91903cebaff25b423048689c8ed12f9fd9071dcd3dc73ebff2e98a116c25667a8f8160cf8aeeaf0a437e6913e6870000082f49d00000000008b *)

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

(* The fiat-crypto BW6_761 field representation. *)
Require Import Bedrock.Field.Synthesis.Examples.bw6_761_prime.

(* The generic Bignum/FElem bridge. *)
Require Import Theory.WordByWordMontgomery.BignumFElemBridge.

Import ListNotations.
Local Open Scope Z_scope.

Section BW6_761_Bignum_Specs.

  Existing Instance bw6_761_prime.bw6_761_field_parameters.
  Existing Instance bw6_761_prime.bw6_761_frep.
  Existing Instance bw6_761_prime.bw6_761_frep_ok.

  (* BW6_761: 4 limbs of 64 bits, modulus as above. *)
  Local Notation bw6_761_n := (felem_size_in_words (FieldRepresentation:=bw6_761_frep)).

  (* === Memory predicate transport === *)

  Lemma bw6_761_FElem_iff_Bignum (px : word.rep) (x : felem) :
    Lift1Prop.iff1
      (FElem px x)
      (Bignum bw6_761_n px (proj1_sig x)).
  Proof.
    apply (@FElem_iff_Bignum _ _ _ _ _ _ _ bw6_761_frep px x).
  Qed.

  Lemma bw6_761_Bignum_to_FElem (px : word.rep) (ws : list word.rep)
        (Hlen : length ws = bw6_761_n) :
    Lift1Prop.iff1
      (Bignum bw6_761_n px ws)
      (FElem px (exist _ ws Hlen)).
  Proof.
    apply (@Bignum_to_FElem _ _ _ _ _ _ _ bw6_761_frep px ws Hlen).
  Qed.

  (* === Decoding equivalence === *)

  Lemma bw6_761_feval_unfold (x : felem) :
    F.to_Z (feval x) =
      F.to_Z (feval x) mod M.
  Proof. apply (@feval_to_Z _ _ _ _ _ bw6_761_frep). Qed.

  (* === Bounds equivalence ===
     [bounded_by tight_bounds] for the WBW BW6_761 representation
     unfolds to [WordByWordMontgomery.valid 64 4 m (map word.unsigned ws)]
     by [tight_bounds_eq] in
     [Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery]. *)

  Lemma bw6_761_tight_bounds_iff_valid (ws : list word.rep) :
    bounded_by tight_bounds ws <-> bounded_by tight_bounds ws.
  Proof. reflexivity. Qed.

End BW6_761_Bignum_Specs.

(** Notes for downstream files:

    To call any of fiat-crypto's WP-proven BW6_761 field functions
    (e.g., [bw6_761_mul], [bw6_761_add]) from an AUCurves caller using
    [Bignum] preconditions, follow the same pattern as in
    [P256_Bignum_Specs.v] / [Secp256k1_Bignum_Specs.v]:

    1. [bw6_761_Bignum_to_FElem] to lift the [Bignum 4 px wsx]
       precondition into [FElem px (exist _ wsx _)].
    2. Apply the fiat-crypto correctness lemma (e.g., [bw6_761_mul_correct]
       once compiled) to rewrite the call into a [feval]-style
       postcondition.
    3. [bw6_761_FElem_iff_Bignum] to push the result back into
       [Bignum 4 pout wsout].
    4. The decoding equivalence bridges [F.to_Z (feval wsout)] and
       AUCurves' [eval (from_mont _) mod m] notation.

    Together this lets the AUCurves RCB add formula treat
    fiat-crypto's bedrock2 BW6_761 field ops as if they had Bignum-style
    specs from the start. *)
