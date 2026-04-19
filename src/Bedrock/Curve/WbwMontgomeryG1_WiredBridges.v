(** Shared F ↔ Z/modular-arithmetic bridge lemmas for per-curve G1
    WiredSpecs transport proofs.

    The 6 bridges ([feval_toZ], [feval_{mul,add,sub,square,opp}_bridge])
    appear identically in every per-curve `*Curve_G1_WiredSpecs.v`.
    Extracting them saves ~90 LoC × each curve that adopts this file.

    **Design note:** the bridges rely on `feval ws` reducing to
    `F.of_Z M_pos (eval (from_mont (toZ ws)))`. Over a fully abstract
    `FieldRepresentation` Context variable, that definitional equality
    is not available. Instead we take the WBW-specific representation
    via `WordByWordMontgomery.field_representation m` and use it as a
    `Local Instance`. Downstream curves define their `<curve>_frep` as
    `:= field_representation m`, so typeclass resolution finds the same
    instance up to definitional equality. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.

Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.

Import ListNotations.
Local Open Scope Z_scope.

Section Bridges.
  Context {field_parameters : FieldParameters}.
  Context {field_representation : FieldRepresentation}.

  Local Notation bw := 64%Z.
  Local Notation n  := (felem_size_in_words (FieldRepresentation := field_representation)).
  Local Notation m  := (Z.pos M_pos).
  Local Notation m' := (@Field.m' bw field_parameters).
  Local Notation eval     := (@WordByWordMontgomery.WordByWordMontgomery.eval bw n).
  Local Notation from_mont := (@WordByWordMontgomery.from_montgomerymod bw n m m').
  Local Notation toZ       := (List.map Interface.word.unsigned).

  (** Per-curve files provide this as
      [reflexivity] because their [<curve>_frep := field_representation m]
      makes [feval] unfold to the RHS definitionally. *)
  Variable feval_wbw_def :
    forall (ws : list word.rep),
      feval ws = F.of_Z M_pos (eval (from_mont (toZ ws))).

  (** Core decoding identity. *)
  Lemma feval_toZ (ws : list word.rep) :
    F.to_Z (feval ws) = eval (from_mont (toZ ws)) mod m.
  Proof.
    rewrite feval_wbw_def.
    rewrite F.to_Z_of_Z. unfold M. reflexivity.
  Qed.

  (** ** Bridge lemmas *)

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

(** Usage:

    In a per-curve WiredSpecs file, after declaring [Existing Instance
    <curve>_field_parameters] + [Existing Instance <curve>_frep]:

    {[
      Lemma curve_feval_def :
        forall ws, feval ws =
          F.of_Z M_pos (eval (from_mont (List.map word.unsigned ws))).
      Proof. reflexivity. Qed.

      (* Bridges specialize automatically via typeclass resolution + hypothesis *)
      Local Definition feval_mul_bridge' := feval_mul_bridge curve_feval_def.
      (* …etc *)
    ]}

    Saves ~90 LoC per curve (the 6 bridges + Z_opp_mod + feval_toZ). *)
