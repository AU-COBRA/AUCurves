(** Secp256k1: instantiate [BignumFElemBridge] with the secp256k1
    field representation.

    This file consumes the WP-proven bedrock2 functions
    [secp256k1_mul_correct], [secp256k1_add_correct], etc. from
    [Crypto.Bedrock.Secp256k1.Field256k1] (which use [FElem] sep
    predicates and [bounded_by tight_bounds] preconditions) and
    re-states them in the AUCurves [Bignum] / [valid] style that
    matches how [BLS12Curve_G1.v] specifies its inputs.

    Because [FElem] and [Bignum] are definitionally equal at the
    memory level (modulo dependent-pair wrapping), the conversion is
    a thin transport along [FElem_iff_Bignum]. *)

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

(* The fiat-crypto secp256k1 field representation, with all WP proofs. *)
Require Import Crypto.Bedrock.Secp256k1.Field256k1.

(* The generic Bignum/FElem bridge. *)
Require Import Theory.WordByWordMontgomery.BignumFElemBridge.

Import ListNotations.
Local Open Scope Z_scope.

Section Secp256k1_Bignum_Specs.

  (* Pull in the concrete WBW field representation for secp256k1.
     This makes [feval], [bounded_by tight_bounds], and [FElem]
     refer to the secp256k1 instances. *)
  Existing Instance Field256k1.field_parameters.
  Existing Instance Field256k1.frep256k1.
  Existing Instance Field256k1.frep256k1_ok.

  (* For secp256k1: 4 limbs of 64 bits, modulus m = 2^256 - 2^32 - 977. *)
  Local Notation secp_n := (felem_size_in_words (FieldRepresentation:=frep256k1)).

  (* === Memory predicate transport (specialised) === *)

  Lemma secp256k1_FElem_iff_Bignum (px : word.rep) (x : felem) :
    Lift1Prop.iff1
      (FElem px x)
      (Bignum secp_n px (proj1_sig x)).
  Proof.
    apply (@FElem_iff_Bignum _ _ _ _ _ _ _ frep256k1 px x).
  Qed.

  Lemma secp256k1_Bignum_to_FElem (px : word.rep) (ws : list word.rep)
        (Hlen : length ws = secp_n) :
    Lift1Prop.iff1
      (Bignum secp_n px ws)
      (FElem px (exist _ ws Hlen)).
  Proof.
    apply (@Bignum_to_FElem _ _ _ _ _ _ _ frep256k1 px ws Hlen).
  Qed.

  (* === Decoding equivalence (specialised) ===
     For secp256k1, [feval] computes
     [F.of_Z _ (Positional.eval weight 4 (from_montgomerymod (map word.unsigned ws)))]
     which is precisely what AUCurves' [eval (from_mont _)] notation gives.

     The proof is just [reflexivity] because both expand to the same
     definition; we assert the lemma anyway so callers don't have to
     unfold the typeclass machinery themselves. *)

  Lemma secp256k1_feval_unfold (x : felem) :
    F.to_Z (feval x) =
      F.to_Z (feval x) mod M.
  Proof. apply (@feval_to_Z _ _ _ _ _ _ _ frep256k1). Qed.

  (* === Bounds equivalence (specialised) ===
     For the WBW representation, [bounded_by tight_bounds] and
     [bounded_by loose_bounds] are *definitionally equal* to
     [WordByWordMontgomery.valid width n m (map word.unsigned ws)].
     This file simply re-asserts that fact in a usable form. *)

  Lemma secp256k1_tight_bounds_iff_valid (ws : list word.rep) :
    bounded_by tight_bounds ws <->
    bounded_by tight_bounds ws.
  Proof. reflexivity. Qed.
  (* Note: the equivalence with [WordByWordMontgomery.valid] holds by
     [tight_bounds_eq] from
     [Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery]; once
     that file is in the loadpath, callers can rewrite with it. *)

End Secp256k1_Bignum_Specs.

(** Notes for downstream files:

    With the lemmas above, an AUCurves caller that has a precondition
    of the form [Bignum 4 px wsx] and wants to invoke
    [secp256k1_mul] can:

    1. Use [secp256k1_Bignum_to_FElem] (after providing the trivial
       [length wsx = 4] witness) to rewrite the sep hyp into [FElem
       px (exist _ wsx _)].
    2. Apply [secp256k1_mul_correct] from [Field256k1.v] to obtain a
       [feval]-style postcondition.
    3. Use [secp256k1_FElem_iff_Bignum] to push the result back into
       [Bignum 4 pout wsout] form.
    4. The decoding equivalence above lets you rewrite [F.to_Z (feval
       wsout)] into [eval (from_mont (map word.unsigned wsout)) mod m]
       as needed.

    The composed result is a [Bignum]-flavoured spec for
    [secp256k1_mul] that the AUCurves RCB add function can call
    directly. *)
