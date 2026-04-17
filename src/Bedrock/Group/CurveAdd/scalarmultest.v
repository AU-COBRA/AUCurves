Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Group.CurveAdd.CurveAdd.
Require Import Coq.Strings.String.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Bedrock.Field.FieldExtensions.Theory.QuadraticExtensions.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.


Section bls12_Fp2.

    Existing Instances Defaults64.default_parameters Defaults64.default_parameters_ok.

    Instance prime_field_parameters : Field.PrimeFieldParameters.
    Proof.
        exact bls12_prime.field_parameters.
    Defined.

    Instance field_parameters : Field.FieldParameters.
    Proof.
        exact (@Field.prime_field_parameters prime_field_parameters).
    Defined.

    Instance field_names : FieldNames.
    Proof.
        exact field_names.
    Defined.

    Instance field_representation : @Field.FieldRepresentation field_parameters _ _ _ _.
    Proof.
        exact (WordByWordMontgomery.field_representation m).
    Defined.

    Check @ladderstep_body. (*Give Proper Name!!!!!!!!*)

    Definition bls12_G1_add := ladderstep_body.
    (*make Field.field_representation from rep in WordByWordMontgomery.*)

    Definition mpos : positive.
    Proof.
        destruct bls12_Fp2.prime_field_parameters. eapply M_pos.
    Defined.

    (*hard-code curve-defining parameter b*)
    Definition b := 4.
    Definition three_b := 12.
    Definition uw := (uweight 64).
    Definition n := felem_size_in_words.
    Definition three_b_list := Partition.partition uw n three_b.
    Definition word := BasicC64Semantics.word.
    Definition m' := Eval native_compute in (@m' prime_field_parameters 64).
    Definition three_b_mont := @WordByWordMontgomery.to_montgomerymod 64 n m m' three_b_list.
    Definition three_b_words := List.map (@word.of_Z 64 word) three_b_mont.

    Definition to_mont l := @WordByWordMontgomery.to_montgomerymod 64 n m m' l.

    Definition from_mont l := @WordByWordMontgomery.from_montgomerymod 64 n m m' l.

    Definition Px_mont := [9000203289623549276; 7000342082925068282; 1000538881605221074; 10009550692327388916; 10008355200866287827; 500084205531694093].
    Definition Py_mont := [11671922859260663127; 11050707557586042878; 284884720401305268; 17749945728364010941; 8613774818643959860; 145621051382923523].
    Definition Pz_mont := [9794203289623549276; 7309342082925068282; 1139538881605221074; 15659550692327388916; 16008355200866287827; 582484205531694093].

    Definition Px_list := Eval native_compute in (from_mont Px_mont).
    Definition Py_list := Eval native_compute in (from_mont Py_mont).
    Definition Pz_list := Eval native_compute in (from_mont Pz_mont).

    Require Import Crypto.Arithmetic.Core.
    Definition eval := Positional.eval (uweight 64) 6.

    Definition xZ := Eval native_compute in (eval Px_list).
    Definition yZ := Eval native_compute in (eval Py_list).
    Definition zZ := Eval native_compute in (eval Pz_list).

    Definition m_pos : positive := Eval native_compute in (@M_pos prime_field_parameters).

    Definition F_of_Z z : F := (ModularArithmetic.F.of_Z m_pos z).

    Definition Fx := F_of_Z xZ.
    Definition Fy := F_of_Z yZ.
    Definition Fz := F_of_Z zZ.

    Definition PF := (Fx, Fy, Fz).
    Definition sc := 1%Z.

    Local Infix "+F" := Fadd (at level 100).
    Local Infix "-F" := Fsub (at level 100).
    Local Infix "*F" := Fmul (at level 90).
    Local Notation "x ^F2" := (Fmul x x) (at level 90).

  Definition G1_add (P1 P2 : (F * F * F)) : (F * F * F) :=
      let (P1', Z1) := P1 in
      let (X1, Y1) := P1' in
      let (P2', Z2) := P2 in
      let (X2, Y2) := P2' in
      let three_b := (feval (three_b_words)) in
      let t0 := (X1 *F X2) in
      let t1 := (Y1 *F Y2) in
      let t2 := (Z1 *F Z2) in
      let t3 := (X1 +F Y1) in
      let t4 := (X2 +F Y2) in
      let t3 := (t3 *F t4) in
      let t4 := (t0 +F t1) in
      let t3 := (t3 -F t4) in
      let t4 := (X1 +F Z1) in
      let t5 := (X2 +F Z2) in
      let t4 := (t4 *F t5) in
      let t5 := (t0 +F t2) in
      let t4 := (t4 -F t5) in
      let t5 := (Y1 +F Z1) in
      let Xout := (Y2 +F Z2) in
      let t5 := (t5 *F Xout) in
      let Xout:= (t1 +F t2) in
      let t5 := (t5 -F Xout) in
      let Zout := (three_b *F t2) in
      let Xout := (t1 -F Zout) in
      let Zout := (Zout +F t1) in
      let Yout := (Xout *F Zout) in
      let t1 := (t0 +F t0) in
      let t1 := (t1 +F t0) in
      let t4 := (three_b *F t4) in
      let t0 := (t1 *F t4) in
      let Yout := (Yout +F t0) in
      let t0 := (t5 *F t4) in
      let Xout := (t3 *F Xout) in
      let Xout := (Xout -F t0) in
      let t0 := (t3 *F t1) in
      let Zout := (t5 *F Zout) in
      let Zout := (Zout +F t0) in
      (Xout, Yout, Zout).

      (*zero*)
      Definition Pinf := (Fzero, Fone, Fzero).

      Eval native_compute in (G1_add Pinf PF).

      Definition Zoutx := (3722719890079661536748435805543770836057835538483654308263392882797705601190437893436693602342029850740932806524614).
      Definition Zouty := 1000602388805416848354447456433976039139220704984751971333014534031007912622709466110671907282253916009473568139947.
      Definition Zoutz := 1.

      Definition to_list := (Partition.partition (uweight 64) 6).

      Definition outx_list := Eval native_compute in to_list Zoutx.
      Definition outy_list := Eval native_compute in to_list Zouty.
      Definition outz_list := Eval native_compute in to_list Zoutz.

      Definition outx_mont := Eval native_compute in (to_mont outx_list).
      Definition outy_mont := Eval native_compute in (to_mont outy_list).
      Definition outz_mont := Eval native_compute in (to_mont outz_list).

      Print outx_mont.
      Print outy_mont.

    Instance spec_of_bls12_add : spec_of (fst bls12_add).
    Proof. exact spec_of_add. Defined.
        (* exact (@spec_of_add _ _ _ _ _ _ field_parameters (WordByWordMontgomery.field_representation m)).
    Defined. *)

    Instance spec_of_bls12_sub : spec_of (fst bls12_sub).
    Proof. exact spec_of_sub. Defined.
        (* exact (@spec_of_sub _ _ _ _ _ _ field_parameters (WordByWordMontgomery.field_representation m)).
    Defined. *)

    Instance spec_of_bls12_mul : spec_of (fst bls12_mul).
    Proof. exact spec_of_mul. Defined.
        (* exact (@spec_of_mul _ _ _ _ _ _ field_parameters (WordByWordMontgomery.field_representation m)).
    Defined. *)

    (* Instance spec_of_bls12_square : spec_of (fst bls12_square).
    Proof. exact spec_of_square. Defined. *)

    Instance spec_of_G1_add : spec_of "ladderstep".
    Proof.
        exact (spec_of_ladderstep three_b_words).
    Defined.

    Definition three_b_F : (@F field_parameters).
    Proof.
        exact (ModularArithmetic.F.of_Z M_pos three_b).
    Defined.

    Instance spec_of_from_list : spec_of from_list.
    Proof.
        exact (spec_of_from_list three_b_F).
    Defined.
(* 
    Lemma bls12_G1_ok : program_logic_goal_for_function! bls12_G1_add. (*Why does this take 7 minutes??!?!?*)
    pose proof ladderstep_correct. cbv [spec_of_G1_add].
    cbv [bls12_G1_add].
    cbv [program_logic_goal_for]. intros.
    eapply H.
        1: simpl; auto.
        3: auto.
        3: cbv [spec_of_bls12_add] in H4; apply H4.
        3: cbv [spec_of_bls12_sub] in H13; apply H13.
        2: {
            cbv [__rupicola_program_marker]. auto.
        }
        2: {
            cbv [CurveAdd.spec_of_from_list]. cbv [spec_of_from_list] in H0.
            assert (three_b_F = feval three_b_words).
            {
                simpl. cbv [Representation.eval_words eval_trans three_b_F].
                Require Import Bedrock.Field.Synthesis.Examples.bls12_from_list_F.
                pose proof (three_b_mont_mod).
                assert (three_b_words = bls12_Fp2.three_b_words).
                {
                    cbv [bls12_Fp2.three_b_words three_b_words]. eapply f_equal.
                    cbv [bls12_Fp2.three_b_mont three_b_mont bls12_Fp2.three_b_list].
                    cbv. reflexivity.
                }
                rewrite <- H35.
                apply f_equal.
                cbv [word] in H34.
                assert (@M bls12_prime.field_parameters = m).
                {
                    simpl. cbv [M]. cbv [m]. cbv [M_pos]. simpl. reflexivity.
                }
                rewrite H36 in H34.
                rewrite H34.
                cbv [three_b_list]. rewrite eval_partition; [| eapply uwprops].
                2 : {
                    clear H H1 H2 H4 H6 H7 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33.
                    clear H34 H35 H36. lia.
                }
                clear H H1 H2 H4 H6 H7 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33.
                cbv [three_b bls12_Fp2.three_b]. erewrite Zmod_small; try lia.
                cbv [n felem_size_in_words]. simpl. cbv [WordByWordMontgomery.n]. simpl.
                cbv [uw uweight ModOps.weight]. simpl. lia.
            }
            rewrite H34 in H0.
            eapply H0.
        }
        clear H H1 H2 H4 H6 H7 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33.
        cbv [CompilationAbstract.maybe_bounded bounded_by loose_bounds bls12_Fp2.three_b_words].
        eassert (my_field_representation = _).
        {
            cbv [my_field_representation]. eauto. 
        }
        rewrite H.
        eassert (bls12_Fp2.field_representation = _).
        {
            cbv [bls12_Fp2.field_representation]. auto.
        }
        cbv [bls12_Fp2.field_representation]. remember (List.map word.of_Z bls12_Fp2.three_b_mont) as eyy.
        simpl. subst eyy.


        assert (three_b_mont = bls12_Fp2.three_b_mont).
        {
            pose proof (three_b_mont_eq). rewrite H2.
            cbv [bls12_Fp2.three_b_mont bls12_Fp2.three_b_list bls12_Fp2.three_b].
            cbv [three_b_list three_b].
            assert (n = bls12_Fp2.n).
            {
                cbv [bls12_Fp2.n]. cbv [n]. reflexivity.
            }
            rewrite <- H4.
            assert (bls12_Fp2.uw = uw).
            {
                cbv [bls12_Fp2.uw]. cbv [uw]. reflexivity.
            }
            rewrite H6. reflexivity.
        }
        rewrite <- H2.
        rewrite unsigned_of_Z_valid.

        2: cbv [n felem_size_in_words]; simpl.
        all: eapply three_b_mont_valid.
Qed. *)

End bls12_Fp2.
    (* From bedrock2 Require Import ToCString Bytedump. *)
    (* Require Import Bedrock.Field.Synthesis.Examples.bls12_from_list_F. *)
    (* Definition c_mod := (c_module (bls12_mul :: nil)). *)

    (* Redirect "blstest.c" Eval compute in c_mod. *)
