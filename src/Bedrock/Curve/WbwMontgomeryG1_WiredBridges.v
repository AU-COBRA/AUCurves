(** Shared F ↔ Z/modular-arithmetic bridge lemmas used by the
    per-curve G1 WiredSpecs transport proofs.

    Extracts the 6 [feval_*_bridge] lemmas that appear identically in:
      - P256_Wired_Specs.v
      - Pallas/Vesta/BLS12/BLS12_377/BN256/BN446 Curve_G1_WiredSpecs.v

    Each per-curve file saves ~90 LoC by importing these instead of
    duplicating the boilerplate. Works for any fiat-crypto New-pipeline
    field representation — the lemmas are purely about the
    [feval ~ F.of_Z M_pos (eval (from_mont _))] bridge and Z modular
    arithmetic. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Bitwidth64.

Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.

Import ListNotations.
Local Open Scope Z_scope.

Section Bridges.
  Context {field_parameters : FieldParameters}.
  Context {field_representation : FieldRepresentation}.

  (** Canonical setup at bw=64, n from the field representation. *)
  Local Notation bw := 64%Z.
  Local Notation n  := (felem_size_in_words (FieldRepresentation := field_representation)).
  Local Notation m  := (Z.pos M_pos).
  Local Notation m' := (@Field.m' bw field_parameters).

  Local Notation eval     := (@WordByWordMontgomery.WordByWordMontgomery.eval bw n).
  Local Notation from_mont := (@WordByWordMontgomery.from_montgomerymod bw n m m').
  Local Notation toZ       := (List.map Interface.word.unsigned).

  (** Core decoding identity: [F.to_Z (feval ws) = eval (from_mont ws) mod m].

      The [field_representation] on WBW makes [feval ws := F.of_Z M_pos (eval (from_mont (toZ ws)))].
      This lemma unpacks the [F.to_Z ∘ F.of_Z] to the [mod m] form used in
      Bignum-style specs. *)
  Lemma feval_toZ (ws : list word.rep) :
    F.to_Z (feval ws) = eval (from_mont (toZ ws)) mod m.
  Proof.
    change (feval ws) with (F.of_Z M_pos (eval (from_mont (toZ ws)))).
    rewrite F.to_Z_of_Z. unfold M. reflexivity.
  Qed.

  (** ** Bridge lemmas: from [feval out = F.op …] to the Bignum
      [eval/from_mont mod m] form. Each handles the mod arithmetic so
      per-curve transport proofs stay clean. *)

  Lemma feval_mul_bridge (wout wx wy : list word.rep) :
    feval wout = F.mul (feval wx) (feval wy) ->
    eval (from_mont (toZ wout)) mod m =
    ((eval (from_mont (toZ wx))) mod m *
     (eval (from_mont (toZ wy))) mod m) mod m.
  Proof.
    intros H. apply (f_equal F.to_Z) in H.
    rewrite F.to_Z_mul in H. rewrite !feval_toZ in H.
    change (Z.pos M_pos) with m in H.
    rewrite Z.mul_mod_idemp_r in H by discriminate.
    rewrite Zmod_mod. exact H.
  Qed.

  Lemma feval_add_bridge (wout wx wy : list word.rep) :
    feval wout = F.add (feval wx) (feval wy) ->
    eval (from_mont (toZ wout)) mod m =
    ((eval (from_mont (toZ wx))) mod m +
     (eval (from_mont (toZ wy))) mod m) mod m.
  Proof.
    intros H. apply (f_equal F.to_Z) in H.
    rewrite F.to_Z_add in H. rewrite !feval_toZ in H.
    change (Z.pos M_pos) with m in H. exact H.
  Qed.

  Lemma feval_sub_bridge (wout wx wy : list word.rep) :
    feval wout = F.sub (feval wx) (feval wy) ->
    eval (from_mont (toZ wout)) mod m =
    ((eval (from_mont (toZ wx))) mod m -
     (eval (from_mont (toZ wy))) mod m) mod m.
  Proof.
    intros H. apply (f_equal F.to_Z) in H.
    cbv [F.sub] in H.
    rewrite F.to_Z_add, F.to_Z_opp in H. rewrite !feval_toZ in H.
    change (Z.pos M_pos) with m in H.
    rewrite Zdiv.Zplus_mod_idemp_r in H. exact H.
  Qed.

  Lemma feval_square_bridge (wout wx : list word.rep) :
    feval wout = F.pow (feval wx) 2 ->
    eval (from_mont (toZ wout)) mod m =
    ((eval (from_mont (toZ wx))) mod m *
     (eval (from_mont (toZ wx))) mod m) mod m.
  Proof.
    intros H. apply (f_equal F.to_Z) in H.
    rewrite F.to_Z_pow in H. simpl Z.of_N in H.
    rewrite Z.pow_2_r in H. rewrite !feval_toZ in H.
    change (Z.pos M_pos) with m in H.
    rewrite Z.mul_mod_idemp_r in H by discriminate.
    rewrite Zmod_mod. exact H.
  Qed.

  Lemma Z_opp_mod (a q : Z) : (- (a mod q)) mod q = (- a) mod q.
  Proof.
    replace (- (a mod q)) with (0 - (a mod q)) by lia.
    replace (- a) with (0 - a) by lia.
    apply Zminus_mod_idemp_r.
  Qed.

  Lemma feval_opp_bridge (wout wx : list word.rep) :
    feval wout = F.opp (feval wx) ->
    eval (from_mont (toZ wout)) mod m =
    (- (eval (from_mont (toZ wx))) mod m) mod m.
  Proof.
    intros H. apply (f_equal F.to_Z) in H.
    rewrite F.to_Z_opp in H. rewrite !feval_toZ in H.
    change (Z.pos M_pos) with m in H.
    rewrite Z_opp_mod in H. rewrite Zmod_mod. exact H.
  Qed.

End Bridges.

(** * Usage

    In a per-curve WiredSpecs file, after the [Existing Instance <curve>_field_parameters.]
    and [Existing Instance <curve>_frep.] declarations:

    {[
      Require Import Bedrock.Curve.WbwMontgomeryG1_WiredBridges.
      (* now [feval_mul_bridge], [feval_add_bridge], etc. are in scope
         instantiated for this curve's parameters *)

      Lemma <curve>_mul_bignum_correct : …
      Proof.
        …
        - apply (feval_mul_bridge _ _ _ Hfeval_out).
      Qed.
    ]}

    Net savings per curve: ~90 LoC (the 6 bridge lemmas including [feval_toZ]
    and [Z_opp_mod]). Across 7 curves: ~630 LoC. *)
