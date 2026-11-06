(** * The BLS12-381 G2 curve constant 3b' = 3 * 4 (1 + u) = (12, 12) in Fp2.

    A bedrock2 loader ["bls12_Fp2_three_b"] storing the 12 Montgomery words
    of (12, 12) (both halves are the G1 constant [bls12_three_b.three_b_mont]),
    proved against [CurveAddAF.spec_of_af_three_b] at the Fp2 instance
    [bls12_Fp2].  This replaces, for the G2 group law, the unproved
    placeholder [bls12_three_b_Fp2.bls12_three_b_G2] (whose spec is
    [fun _ => True]). *)

Require Import Rupicola.Lib.Api.
From Stdlib Require Import ZArith Lia List.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Crypto.Bedrock.Specs.Field.
Require Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Bedrock.Field.FieldExtensions.Compilation2_Fp2.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_Fp2.
Require Bedrock.Field.Synthesis.Examples.bls12_three_b.
Require Import Bedrock.Group.CurveAdd.CurveAddAF.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Section G2ThreeB.
  Existing Instances Bitwidth64.BW64
    Defaults64.default_parameters Defaults64.default_parameters_ok
    bls12_prime_parameters bls12_field_representation
    bls12_Fp2_field_parameters bls12_Fp2_field_representation.
  Existing Instance prime_field_parameters.

  Local Notation Fp := (F PrimeField.M_pos).
  Local Notation Fp2 := (Fp * Fp)%type.
  Local Notation AFElem := Compilation2_Fp2.AFElem.

  Definition tbm (i : nat) : Z := nth i bls12_three_b.three_b_mont 0.

  Definition st (off : Z) (i : nat) : Syntax.cmd :=
    cmd.store access_size.word
      (if Z.eqb off 0 then expr.var "out"
       else expr.op bopname.add (expr.var "out") (expr.literal off))
      (expr.literal (tbm i)).

  (** out[0..5] := Montgomery 12; out[6..11] := Montgomery 12. *)
  Definition g2_three_b_body : Syntax.func :=
    (["out"], [],
     cmd.seq (st 0 0) (cmd.seq (st 8 1) (cmd.seq (st 16 2) (cmd.seq (st 24 3)
     (cmd.seq (st 32 4) (cmd.seq (st 40 5)
     (cmd.seq (st 48 0) (cmd.seq (st 56 1) (cmd.seq (st 64 2) (cmd.seq (st 72 3)
     (cmd.seq (st 80 4) (st 88 5)))))))))))).

  Definition g2_tb : Fp2 := (F.of_Z _ 12, F.of_Z _ 12).

  Lemma feval_tb :
    AbstractField.feval (bls12_three_b.three_b_words) = F.of_Z PrimeField.M_pos 12.
  Proof. exact bls12_three_b.feval_three_b_words. Qed.

  Local Infix "+w" := word.add (at level 50).

  Lemma AFElem_intro (p : word) (ws : list word) (v : Fp2) bnd (R : mem -> Prop) m :
    AbstractField.feval (F:=Fp2) ws = v -> AbstractField.bounded_by (F:=Fp2) bnd ws ->
    (AbstractField.FElem (F:=Fp2) p ws * R)%sep m -> (AFElem (Some bnd) p v * R)%sep m.
  Proof.
    intros Hv Hb Hm. unfold AFElem.
    eapply Proper_sep_impl1; [ | reflexivity | exact Hm ].
    intros m' Hm'. exists ws. apply sep_emp_l. split; [ split; assumption | exact Hm' ].
  Qed.

  Lemma tw_len : length bls12_three_b.three_b_words = AbstractField.felem_size_in_words.
  Proof. reflexivity. Qed.

  Lemma tw_bounded :
    AbstractField.bounded_by AbstractField.loose_bounds bls12_three_b.three_b_words.
  Proof.
    cbv [AbstractField.bounded_by AbstractField.loose_bounds bls12_field_representation
         Field.bounded_by bls12_frep Signature.field_representation
         Representation.frep Field.loose_bounds bls12_three_b.three_b_words
         Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.field_representation].
    rewrite (bls12_three_b.unsigned_of_Z_valid _ bls12_three_b.three_b_mont_valid).
    exact bls12_three_b.three_b_mont_valid.
  Qed.

  Ltac subst_words :=
    repeat match goal with
           | x := word.of_Z _ |- _ => subst x
           | x := word.add _ _ |- _ => subst x
           end.

  Lemma g2_three_b_ok (functions : Semantics.env) :
    map.get functions "bls12_Fp2_three_b" = Some g2_three_b_body ->
    spec_of_af_three_b g2_tb "bls12_Fp2_three_b" functions.
  Proof.
    intros Henv. cbv [spec_of_af_three_b].
    intros pout outold Rout tr m Hm.
    eapply WeakestPreconditionProperties.start_func; [ exact Henv | ].
    cbv match beta delta [WeakestPrecondition.func g2_three_b_body].
    unfold AFElem in Hm. sepsimpl.
    cbv [AbstractField.FElem bls12_Fp2_field_representation Fp2_field_representation
         Bignum.Bignum] in *.
    sepsimpl.
    match goal with H : length ?ws = _ |- _ => rename ws into ws0; rename H into Hlen end.
    cbn in Hlen.
    do 12 (destruct ws0 as [|? ws0]; [ cbn in Hlen; lia | ]).
    destruct ws0; [ | cbn in Hlen; lia ].
    cbn [array] in *.
    change (Memory.bytes_per_word 64) with 8 in *.
    repeat match goal with
           | H : context [ (?p +w word.of_Z ?a) +w word.of_Z ?c ] |- _ =>
             replace ((p +w word.of_Z a) +w word.of_Z c) with (p +w word.of_Z (a + c)) in H
               by (rewrite word.ring_morph_add; ring);
             cbn [Z.add Pos.add Pos.succ] in H
           end.
    cbv [st tbm Z.eqb Pos.eqb].
    repeat straightline.
    apply (AFElem_intro pout (bls12_three_b.three_b_words ++ bls12_three_b.three_b_words)).
    { cbv [g2_tb AbstractField.feval bls12_Fp2_field_representation Fp2_field_representation
           fst_felem snd_felem].
      rewrite firstn_app' by exact tw_len. rewrite skipn_app by exact tw_len.
      exact (f_equal2 pair feval_tb feval_tb). }
    { cbv [AbstractField.bounded_by bls12_Fp2_field_representation Fp2_field_representation
           fst_felem snd_felem AbstractField.loose_bounds].
      rewrite firstn_app' by exact tw_len. rewrite skipn_app by exact tw_len.
      split; exact tw_bounded. }
    cbv [AbstractField.FElem bls12_Fp2_field_representation Fp2_field_representation
         Bignum.Bignum].
    apply sep_assoc. apply sep_emp_l. split.
    { rewrite List.length_app, tw_len. reflexivity. }
    cbv [bls12_three_b.three_b_words bls12_three_b.three_b_mont List.app List.map].
    cbn [array].
    change (Memory.bytes_per_word 64) with 8.
    repeat match goal with
           | |- context [ (?p +w word.of_Z ?a) +w word.of_Z ?c ] =>
             replace ((p +w word.of_Z a) +w word.of_Z c) with (p +w word.of_Z (a + c))
               by (rewrite word.ring_morph_add; ring);
             cbn [Z.add Pos.add Pos.succ]
           end.
    subst_words.
    cbv [bls12_three_b.three_b_mont nth] in *.
    ecancel_assumption.
  Qed.

End G2ThreeB.
