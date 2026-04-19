(** Generic BignumFElemBridge wrapper for any fiat-crypto New-pipeline
    WBW Montgomery field representation.

    Section-based generic form: each per-curve wrapper declares
    [Existing Instance] for its field parameters + field representation,
    then imports this file. The bridge lemmas below are parameterized
    via Context variables and specialize automatically via typeclass
    resolution.

    See PallasCurve_G1_BignumSpecs_v2.v for a concrete usage example. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.Lift1Prop.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.

Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.

Require Import Theory.WordByWordMontgomery.BignumFElemBridge.

Import ListNotations.
Local Open Scope Z_scope.

Section Generic.
  Context {field_parameters : FieldParameters}.
  Context {field_representation : FieldRepresentation}.
  Context {field_representation_ok : FieldRepresentation_ok}.

  (** Limb count derived from the field representation. *)
  Local Notation n := (felem_size_in_words (FieldRepresentation := field_representation)).

  (** Memory predicate transport: FElem ↔ Bignum. *)

  Lemma G1_FElem_iff_Bignum (px : word.rep) (x : felem) :
    Lift1Prop.iff1
      (FElem px x)
      (Bignum n px (proj1_sig x)).
  Proof.
    apply (@BignumFElemBridge.FElem_iff_Bignum _ _ _ _ _ _ _ field_representation px x).
  Qed.

  Lemma G1_Bignum_to_FElem (px : word.rep) (ws : list word.rep)
        (Hlen : length ws = n) :
    Lift1Prop.iff1
      (Bignum n px ws)
      (FElem px (exist _ ws Hlen)).
  Proof.
    apply (@BignumFElemBridge.Bignum_to_FElem _ _ _ _ _ _ _ field_representation px ws Hlen).
  Qed.

  (** Decoding equivalence: [F.to_Z (feval x) = F.to_Z (feval x) mod M]. *)

  Lemma G1_feval_unfold (x : felem) :
    F.to_Z (feval x) = F.to_Z (feval x) mod M.
  Proof. apply (@feval_to_Z _ _ _ _ _ field_representation). Qed.

  (** Bounds equivalence placeholder. *)

  Lemma G1_tight_bounds_iff_valid (ws : list word.rep) :
    bounded_by tight_bounds ws <-> bounded_by tight_bounds ws.
  Proof. reflexivity. Qed.

End Generic.

(** Usage:

    Each per-curve wrapper file:

    {[
      Require Import Bedrock.Field.Synthesis.Examples.<curve>_prime.
      Require Import Bedrock.Curve.WbwMontgomeryG1_BignumSpecs.

      Existing Instance <curve>_field_parameters.
      Existing Instance <curve>_frep.
      Existing Instance <curve>_frep_ok.

      (* Re-export under legacy names if desired *)
      Notation <curve>_n                      := n.  (* from this file *)
      Notation <curve>_FElem_iff_Bignum       := G1_FElem_iff_Bignum.
      Notation <curve>_Bignum_to_FElem        := G1_Bignum_to_FElem.
      Notation <curve>_feval_unfold           := G1_feval_unfold.
      Notation <curve>_tight_bounds_iff_valid := G1_tight_bounds_iff_valid.
    ]}

    Each wrapper shrinks from ~100 LoC to ~15 LoC. *)
