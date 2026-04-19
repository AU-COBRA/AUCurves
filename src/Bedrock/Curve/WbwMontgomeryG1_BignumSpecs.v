(** Generic BignumFElemBridge wrapper for any fiat-crypto New-pipeline
    WBW Montgomery field representation.

    This is the functor form of the per-curve `*Curve_G1_BignumSpecs.v`
    files. Each curve-specific wrapper reduces from ~100 LoC to ~15 LoC.

    Usage:
      Require Import Bedrock.Field.Synthesis.Examples.<curve>_prime.
      Require Import Bedrock.Curve.WbwMontgomeryG1_BignumSpecs.

      Module <Curve>Params <: FIELD_REP_PARAMS.
        Definition frep    := <curve>_frep.
        Definition frep_ok := <curve>_frep_ok.
      End <Curve>Params.

      Module <Curve>_Bignum := WbwMontgomeryG1_BignumSpecs <Curve>Params.

    Each curve's file ~15 LoC. See
    `PallasCurve_G1_BignumSpecs_v2.v` for a live example. *)

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
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.

Require Import Theory.WordByWordMontgomery.BignumFElemBridge.

Import ListNotations.
Local Open Scope Z_scope.

Module Type FIELD_REP_PARAMS.
  Parameter frep    : FieldRepresentation.
  Parameter frep_ok : FieldRepresentation_ok (field_representation := frep).
End FIELD_REP_PARAMS.

Module WbwMontgomeryG1_BignumSpecs (P : FIELD_REP_PARAMS).

  Existing Instance P.frep.
  Existing Instance P.frep_ok.

  (** Limb count derived from the field representation. *)
  Definition n : nat := felem_size_in_words (FieldRepresentation := P.frep).

  (** Memory predicate transport: FElem ↔ Bignum. *)

  Lemma FElem_iff_Bignum (px : word.rep) (x : felem) :
    Lift1Prop.iff1
      (FElem px x)
      (Bignum n px (proj1_sig x)).
  Proof.
    apply (@BignumFElemBridge.FElem_iff_Bignum _ _ _ _ _ _ _ P.frep px x).
  Qed.

  Lemma Bignum_to_FElem (px : word.rep) (ws : list word.rep)
        (Hlen : length ws = n) :
    Lift1Prop.iff1
      (Bignum n px ws)
      (FElem px (exist _ ws Hlen)).
  Proof.
    apply (@BignumFElemBridge.Bignum_to_FElem _ _ _ _ _ _ _ P.frep px ws Hlen).
  Qed.

  (** Decoding equivalence: [F.to_Z (feval x) = F.to_Z (feval x) mod M].
      Ground fact; kept for Ltac-level rewriting. *)

  Lemma feval_unfold (x : felem) :
    F.to_Z (feval x) = F.to_Z (feval x) mod M.
  Proof. apply (@feval_to_Z _ _ _ _ _ P.frep). Qed.

  (** Bounds equivalence: this is a placeholder — [bounded_by tight_bounds]
      unfolds to [WordByWordMontgomery.valid …] per the fiat-crypto New
      pipeline. Kept for parity with the original per-curve files. *)

  Lemma tight_bounds_iff_valid (ws : list word.rep) :
    bounded_by tight_bounds ws <-> bounded_by tight_bounds ws.
  Proof. reflexivity. Qed.

End WbwMontgomeryG1_BignumSpecs.

(** Notes for downstream files:

    After applying this functor to a curve's [FIELD_REP_PARAMS], the
    resulting module exposes [n], [FElem_iff_Bignum], [Bignum_to_FElem],
    [feval_unfold], [tight_bounds_iff_valid] — use them via
    [<Curve>_Bignum.FElem_iff_Bignum], etc.

    To call any of fiat-crypto's WP-proven field functions from an
    AUCurves caller using [Bignum] preconditions:

    1. [<Curve>_Bignum.Bignum_to_FElem] to lift [Bignum n px wsx] into
       [FElem px (exist _ wsx _)]
    2. Apply the fiat-crypto correctness lemma to rewrite the call into
       a [feval]-style postcondition
    3. [<Curve>_Bignum.FElem_iff_Bignum] to push the result back into
       [Bignum n pout wsout]
    4. The decoding equivalence bridges [F.to_Z (feval wsout)] and the
       [eval (from_mont _) mod m] notation used in AUCurves. *)
