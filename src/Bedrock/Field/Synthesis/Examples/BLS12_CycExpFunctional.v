(** * BLS12-381 cyclotomic exponentiation: functional WP proofs

    Functional versions of the lemmas of BLS12_CycExp.v (which state bounds and
    frame only).  The callee specs are the same hypotheses
    (AbstractField.binop_spec / unop_spec carry the feval equalities, which the
    bounds-only proofs drop).

      fp12_set_one_functional_wp  feval of the 12 from_word results = Pairing.fp12_one
      cyc_sqr_functional_wp       feval out = cyc_sqr_model (feval in)    (CycExpModel.v)
      cyc_exp_neg_functional_ok   post: cyclotomic (feval base) ->
                                        feval out = conj (pw (feval base) e)
      bls12_Fp12_cyc_exp_x_neg_functional_ok / _c_neg_:
                                  feval out = Pairing.fp12_pow_bls_x_signed / _c_signed (feval base)
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Bedrock.Field.Synthesis.Examples.BN_StraightlineFast.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime_certif.
Require Import Bedrock.Field.Synthesis.Examples.bls12_felem_copy.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.PairingFieldOps.
Require Import Bedrock.Field.FieldExtensions.WPTactics.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_Pairing.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingHelpers.
Require Import bedrock2.Loops.
Require Import bedrock2.SepCalls.
Require Import coqutil.Z.Lia.
Require Import bedrock2.SepAutoArray.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_CurveInstances.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingHelpers.


Require Import Bedrock.Field.Synthesis.Examples.BLS12_CycExp.
Require Import Theory.BLS12Pairing.Fp12Ring.
Require Import Theory.BLS12Pairing.Cyclotomic.
Require Import Theory.BLS12Pairing.CycExpModel.
Require Theory.BLS12Pairing.Pairing.
Require Theory.BLS12Pairing.Fp6.
Require Theory.BLS12Pairing.Fp12.
Require Bedrock.Field.Synthesis.Examples.BLS12_Fp6Feval.
Require Bedrock.Field.Synthesis.Examples.BLS12_PairingFevalInst.
Module P := Theory.BLS12Pairing.Pairing.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** Callee facts are wrapped in [hidden] so that [eassumption] does not try them (performance). *)
Record hidden (P : Prop) : Prop := hide { unhide : P }.

Section BLS12_CycExpFunctional.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    Existing Instance BLS12_CycExp.bls12_pf_params.
    Existing Instance BLS12_CycExp.bls12_pf_params_ok.
    Existing Instance prime_field_parameters.
    Existing Instance BLS12_CycExp.bls12_Fp_rep.
    Existing Instance BLS12_CycExp.bls12_Fp_rep_ok.

    Local Notation Fp := (F PrimeField.M_pos).
    Local Notation Fp2 := ((Fp * Fp)%type).
    Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
    Local Notation Fp12 := ((Fp6 * Fp6)%type).

    Let fp2_prefix := "bls12_Fp2_".
    Let fp6_prefix := "bls12_Fp6_".
    Let fp12_prefix := "bls12_Fp12_".
    Let bls12_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-1).
    Let bls12_xi_re : F PrimeField.M_pos := @F.one PrimeField.M_pos.
    Let bls12_xi_im : F PrimeField.M_pos := @F.one PrimeField.M_pos.

    Existing Instance BLS12_CycExp.bls12_Fp2_params'.
    Existing Instance BLS12_CycExp.bls12_Fp2_rep'.
    Existing Instance BLS12_CycExp.bls12_Fp6_params'.
    Existing Instance BLS12_CycExp.bls12_Fp6_rep'.
    Existing Instance BLS12_CycExp.bls12_Fp12_params'.
    Existing Instance BLS12_CycExp.bls12_Fp12_rep'.

    Local Notation bls12_Fp_rep := BLS12_CycExp.bls12_Fp_rep.
    Local Notation bls12_pf_params := BLS12_CycExp.bls12_pf_params.
    Local Notation bls12_Fp2_params' := BLS12_CycExp.bls12_Fp2_params'.
    Local Notation bls12_Fp2_rep' := BLS12_CycExp.bls12_Fp2_rep'.
    Local Notation bls12_Fp6_params' := BLS12_CycExp.bls12_Fp6_params'.
    Local Notation bls12_Fp6_rep' := BLS12_CycExp.bls12_Fp6_rep'.
    Local Notation bls12_Fp12_params' := BLS12_CycExp.bls12_Fp12_params'.
    Local Notation bls12_Fp12_rep' := BLS12_CycExp.bls12_Fp12_rep'.

    Local Notation FElem_Fp := (@AbstractField.FElem _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation FElem_Fp2 := (@AbstractField.FElem _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation FElem_Fp6 := (@AbstractField.FElem _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep').
    Local Notation FElem_Fp12 := (@AbstractField.FElem _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp_bounded := (@AbstractField.bounded_by _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp_tight := (@AbstractField.tight_bounds _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp2_bounded := (@AbstractField.bounded_by _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp2_tight := (@AbstractField.tight_bounds _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp6_bounded := (@AbstractField.bounded_by _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep').
    Local Notation Fp12_bounded := (@AbstractField.bounded_by _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp12_tight := (@AbstractField.tight_bounds _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp12_loose := (@AbstractField.loose_bounds _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp_felem := (@AbstractField.felem _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp2_felem := (@AbstractField.felem _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp6_felem := (@AbstractField.felem _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep').
    Local Notation Fp12_felem := (@AbstractField.felem _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp_feval := (@AbstractField.feval _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp2_feval := (@AbstractField.feval _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp6_feval := (@AbstractField.feval _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep').
    Local Notation Fp12_feval := (@AbstractField.feval _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').

    Local Typeclasses Opaque bls12_Fp12_params'.
    Local Typeclasses Opaque bls12_Fp6_params'.
    Local Typeclasses Opaque bls12_Fp2_params'.

    Local Instance bls12_Fp12_rep_ok'' :
      @AbstractField.FieldRepresentation_ok _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep' :=
      BLS12_CycExp.bls12_Fp12_rep_ok'.
    Local Instance bls12_Fp6_rep_ok'' :
      @AbstractField.FieldRepresentation_ok _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep' :=
      BLS12_CycExp.bls12_Fp6_rep_ok'.
    Local Instance bls12_Fp2_rep_ok'' :
      @AbstractField.FieldRepresentation_ok _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep' :=
      BLS12_CycExp.bls12_Fp2_rep_ok'.

    Local Notation Fp_fsw := (@AbstractField.felem_size_in_words _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp2_fsw := (@AbstractField.felem_size_in_words _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp6_fsw := (@AbstractField.felem_size_in_words _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep').
    Local Notation fp_felem_offset :=
      (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bls12_Fp_rep)).
    Local Notation fp6_felem_offset :=
      (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep')).
    Local Notation fst_felem := (@QuadraticFieldExtensionsSpecs.fst_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).
    Local Notation snd_felem := (@QuadraticFieldExtensionsSpecs.snd_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).
    Local Notation c0_felem := (@CubicFieldExtensionsSpecs.c0_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).
    Local Notation c1_felem := (@CubicFieldExtensionsSpecs.c1_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).
    Local Notation c2_felem := (@CubicFieldExtensionsSpecs.c2_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).
    Local Notation d0_felem := (@DodecicFieldExtensionsSpecs.d0_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).
    Local Notation d1_felem := (@DodecicFieldExtensionsSpecs.d1_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).
    Local Notation fp6_c1_off :=
      (@CubicFieldExtensions.fp6_c1_offset _ _ _ _ bls12_pf_params bls12_beta bls12_Fp_rep fp2_prefix).
    Local Notation fp6_c2_off :=
      (@CubicFieldExtensions.fp6_c2_offset _ _ _ _ bls12_pf_params bls12_beta bls12_Fp_rep fp2_prefix).

    (* ================================================================ *)
    (* Pure feval lemmas                                                *)
    (* ================================================================ *)

    Local Opaque BLS12_CycExp.bls12_Fp_rep.

    Lemma Fp2_feval_app' (a b : Fp_felem) :
      List.length a = Fp_fsw -> Fp2_feval (a ++ b) = (Fp_feval a, Fp_feval b).
    Proof.
      intros Ha.
      change (Fp2_feval (a ++ b)) with
        (Fp_feval (firstn Fp_fsw (a ++ b)), Fp_feval (skipn Fp_fsw (a ++ b))).
      rewrite (QuadraticFieldExtensions.firstn_app' _ _ _ Ha).
      rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Ha).
      reflexivity.
    Qed.

    Lemma Fp6_feval_app3' (a b c : Fp2_felem) :
      List.length a = Fp2_fsw -> List.length b = Fp2_fsw ->
      Fp6_feval (a ++ b ++ c) = ((Fp2_feval a, Fp2_feval b), Fp2_feval c).
    Proof.
      intros Ha Hb.
      change (Fp6_feval (a ++ b ++ c)) with
        ((Fp2_feval (firstn Fp2_fsw (a ++ b ++ c)),
          Fp2_feval (firstn Fp2_fsw (skipn Fp2_fsw (a ++ b ++ c)))),
         Fp2_feval (skipn (2 * Fp2_fsw) (a ++ b ++ c))).
      assert (Hab : List.length (a ++ b) = (2 * Fp2_fsw)%nat).
      { rewrite length_app, Ha, Hb. lia. }
      rewrite (QuadraticFieldExtensions.firstn_app' _ _ _ Ha).
      rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Ha).
      rewrite (QuadraticFieldExtensions.firstn_app' _ _ _ Hb).
      rewrite (app_assoc a b c).
      rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Hab).
      reflexivity.
    Qed.

    Lemma Fp12_feval_app' (a b : Fp6_felem) :
      List.length a = Fp6_fsw -> Fp12_feval (a ++ b) = (Fp6_feval a, Fp6_feval b).
    Proof.
      intros Ha.
      change (Fp12_feval (a ++ b)) with
        (Fp6_feval (firstn Fp6_fsw (a ++ b)), Fp6_feval (skipn Fp6_fsw (a ++ b))).
      rewrite (QuadraticFieldExtensions.firstn_app' _ _ _ Ha).
      rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Ha).
      reflexivity.
    Qed.

    Lemma Fp12_feval_split (x : Fp12_felem) :
      Fp12_feval x = (Fp6_feval (d0_felem x), Fp6_feval (d1_felem x)).
    Proof. reflexivity. Qed.

    Lemma Fp6_feval_split (x : Fp6_felem) :
      Fp6_feval x = ((Fp_feval (fst_felem (c0_felem x)), Fp_feval (snd_felem (c0_felem x))),
                     Fp2_feval (c1_felem x), Fp2_feval (c2_felem x)).
    Proof. reflexivity. Qed.

    Local Notation word_feval z := (F.of_Z PrimeField.M_pos (@word.unsigned 64 word (word.of_Z z))).

    Lemma Fp12_feval_set_one (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : Fp_felem) :
      List.length w1 = Fp_fsw -> List.length w2 = Fp_fsw -> List.length w3 = Fp_fsw ->
      List.length w4 = Fp_fsw -> List.length w5 = Fp_fsw -> List.length w6 = Fp_fsw ->
      List.length w7 = Fp_fsw -> List.length w8 = Fp_fsw -> List.length w9 = Fp_fsw ->
      List.length w10 = Fp_fsw -> List.length w11 = Fp_fsw ->
      Fp_feval w1 = word_feval 1 -> Fp_feval w2 = word_feval 0 -> Fp_feval w3 = word_feval 0 ->
      Fp_feval w4 = word_feval 0 -> Fp_feval w5 = word_feval 0 -> Fp_feval w6 = word_feval 0 ->
      Fp_feval w7 = word_feval 0 -> Fp_feval w8 = word_feval 0 -> Fp_feval w9 = word_feval 0 ->
      Fp_feval w10 = word_feval 0 -> Fp_feval w11 = word_feval 0 -> Fp_feval w12 = word_feval 0 ->
      Fp12_feval (((w1 ++ w2) ++ (w3 ++ w4) ++ (w5 ++ w6)) ++ ((w7 ++ w8) ++ (w9 ++ w10) ++ (w11 ++ w12)))
      = P.fp12_one PrimeField.M_pos.
    Proof.
      intros L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12.
      assert (L12' : List.length (w1 ++ w2) = Fp2_fsw).
      { rewrite length_app, L1, L2. change Fp2_fsw with (2 * Fp_fsw)%nat. lia. }
      assert (L34' : List.length (w3 ++ w4) = Fp2_fsw).
      { rewrite length_app, L3, L4. change Fp2_fsw with (2 * Fp_fsw)%nat. lia. }
      assert (L78' : List.length (w7 ++ w8) = Fp2_fsw).
      { rewrite length_app, L7, L8. change Fp2_fsw with (2 * Fp_fsw)%nat. lia. }
      assert (L910' : List.length (w9 ++ w10) = Fp2_fsw).
      { rewrite length_app, L9, L10. change Fp2_fsw with (2 * Fp_fsw)%nat. lia. }
      assert (L6' : List.length ((w1 ++ w2) ++ (w3 ++ w4) ++ (w5 ++ w6)) = Fp6_fsw).
      { rewrite !length_app, L1, L2, L3, L4, L5, L6.
        change Fp6_fsw with (3 * Fp2_fsw)%nat. change Fp2_fsw with (2 * Fp_fsw)%nat. lia. }
      rewrite (Fp12_feval_app' ((w1 ++ w2) ++ (w3 ++ w4) ++ (w5 ++ w6))
                 ((w7 ++ w8) ++ (w9 ++ w10) ++ (w11 ++ w12)) L6').
      rewrite (Fp6_feval_app3' (w1 ++ w2) (w3 ++ w4) (w5 ++ w6) L12' L34').
      rewrite (Fp6_feval_app3' (w7 ++ w8) (w9 ++ w10) (w11 ++ w12) L78' L910').
      rewrite (Fp2_feval_app' w1 w2 L1), (Fp2_feval_app' w3 w4 L3), (Fp2_feval_app' w5 w6 L5),
        (Fp2_feval_app' w7 w8 L7), (Fp2_feval_app' w9 w10 L9), (Fp2_feval_app' w11 w12 L11).
      rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12.
      reflexivity.
    Qed.

    (* Models of the callees in Pairing.v terms *)
    Lemma F6mul_eq (o a b : Fp6) :
      o = @AbstractField.Fmul _ bls12_Fp6_params' a b -> o = P.fp6_mul PrimeField.M_pos a b.
    Proof. intros ->. exact (BLS12_Fp6Feval.fp6_mul_eq PrimeField.M_pos a b). Qed.

    Lemma F6add_eq (o a b : Fp6) :
      o = @AbstractField.Fadd _ bls12_Fp6_params' a b -> o = P.fp6_add PrimeField.M_pos a b.
    Proof. intros ->. exact (BLS12_Fp6Feval.fp6_add_eq PrimeField.M_pos a b). Qed.

    Lemma F6mulv_eq (o a : Fp6) :
      o = @AbstractField.un_model _ _ _ _ _ bls12_Fp6_params' bls12_Fp6_rep' _
            (@DodecicFieldExtensions.un_Fp6_mul_by_v _ _ _ _
               bls12_pf_params bls12_Fp_rep bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix) a ->
      o = P.fp6_mul_by_v PrimeField.M_pos a.
    Proof.
      intros ->. rewrite <- (BLS12_Fp6Feval.fp6_mul_by_v_eq PrimeField.M_pos a).
      destruct a as [[a0 a1] a2]. reflexivity.
    Qed.

    Lemma F12mul_eq (o a b : Fp12) :
      o = @AbstractField.Fmul _ bls12_Fp12_params' a b -> o = P.fp12_mul PrimeField.M_pos a b.
    Proof. intros ->. exact (BLS12_PairingFevalInst.fp12_mul_eq_closed PrimeField.M_pos a b). Qed.

    Lemma F12conj_eq (o a : Fp12) :
      o = @AbstractField.un_model _ _ _ _ _ bls12_Fp12_params' bls12_Fp12_rep' _
            (@DodecicFieldExtensions.un_Fp12_conjugate _ _ _ _
               bls12_pf_params bls12_Fp_rep bls12_beta bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix) a ->
      o = P.fp12_conjugate PrimeField.M_pos a.
    Proof. intros ->. destruct a as [a0 a1]. reflexivity. Qed.

    Lemma Fpadd_eq (o a b : Fp) :
      o = @AbstractField.Fadd _ (@prime_field_parameters bls12_pf_params) a b -> o = F.add a b.
    Proof. intros ->. reflexivity. Qed.

    Add Ring Fp_ring_cyc : (@Fp_ring_theory PrimeField.M_pos).

    (** The six calls of cyc_sqr_body compose to [cyc_sqr_model]. *)
    Lemma cyc_sqr_chain (r : Fp12_felem) (y1 y2 y3 y4 y6 : Fp6_felem) (z one : Fp_felem) :
      List.length z = Fp_fsw ->
      List.length (z ++ snd_felem (c0_felem y4)) = Fp2_fsw ->
      List.length (c1_felem y4) = Fp2_fsw ->
      List.length ((z ++ snd_felem (c0_felem y4)) ++ c1_felem y4 ++ c2_felem y4) = Fp6_fsw ->
      Fp6_feval y1 = P.fp6_mul PrimeField.M_pos (Fp6_feval (d1_felem r)) (Fp6_feval (d1_felem r)) ->
      Fp6_feval y2 = P.fp6_mul PrimeField.M_pos (Fp6_feval (d0_felem r)) (Fp6_feval (d1_felem r)) ->
      Fp6_feval y3 = P.fp6_mul_by_v PrimeField.M_pos (Fp6_feval y1) ->
      Fp6_feval y4 = P.fp6_add PrimeField.M_pos (Fp6_feval y3) (Fp6_feval y3) ->
      Fp_feval z = F.add (Fp_feval (fst_felem (c0_felem y4))) (Fp_feval one) ->
      Fp_feval one = F.one ->
      Fp6_feval y6 = P.fp6_add PrimeField.M_pos (Fp6_feval y2) (Fp6_feval y2) ->
      Fp12_feval (((z ++ snd_felem (c0_felem y4)) ++ c1_felem y4 ++ c2_felem y4) ++ y6) =
      cyc_sqr_model (Fp12_feval r).
    Proof.
      intros Lz L0 L1 Lc E1 E2 E3 E4 E5 Eone E6.
      rewrite (Fp12_feval_app' _ _ Lc), (Fp6_feval_app3' _ _ _ L0 L1), (Fp2_feval_app' _ _ Lz).
      rewrite Fp12_feval_split.
      cbv [cyc_sqr_model]; cbn [fst snd].
      rewrite <- E1, <- E3, <- E4, <- E2, <- E6.
      rewrite E5, Eone, (Fp6_feval_split y4).
      generalize (Fp_feval (fst_felem (c0_felem y4))) (Fp_feval (snd_felem (c0_felem y4)))
        (Fp2_feval (c1_felem y4)) (Fp2_feval (c2_felem y4)) (Fp6_feval y6).
      intros a b [c0 c1] [d0 d1] y.
      cbv [P.fp6_add P.fp6_one P.fp6_build P.fp6_c0 P.fp6_c1 P.fp6_c2 P.fp2_add P.fp2_one P.fp2_zero fst snd].
      repeat f_equal; ring.
    Qed.

    Local Transparent BLS12_CycExp.bls12_Fp_rep.

    (* ================================================================ *)
    (* fp12_set_one, functional                                         *)
    (* ================================================================ *)

    Local Ltac snd_from_word_ecancel H :=
      let H' := fresh "H" in
      pose proof H as H';
      ecancel_assumption_impl.

    Local Ltac fw_pair HFfromword a x :=
      repeat straightline;
      let Hs := fresh "Hs" in
      eassert (Hs : (FElem_Fp2 a x ⋆ _) _) by ecancel_assumption;
      apply BLS12_PairingHelpers.FElem_Fp2_split_in_sep in Hs;
      eexists; split; [eval_dexprs_fast |];
      eapply Semantics.weaken_call;
      [ eapply (HFfromword _ _ (fst_felem x)); exact Hs | ];
      let fwa := fresh "fw" in let Hba := fresh "Hb_fw" in let Hsa := fresh "Hsep_fw" in
      let Hfa := fresh "Hfe_fw" in
      intros ? ? ? [? [? [fwa [Hfa [Hba Hsa]]]]];
      apply hide in Hfa;
      subst; cbv [map.putmany_of_list_zip]; eexists; split; [ exact eq_refl | ];
      repeat straightline;
      eexists; split; [eval_dexprs_fast |];
      eapply Semantics.weaken_call;
      [ eapply (HFfromword _ _ (snd_felem x)); snd_from_word_ecancel Hsa | ];
      let fwb := fresh "fw" in let Hbb := fresh "Hb_fw" in let Hsb := fresh "Hsep_fw" in
      let Hfb := fresh "Hfe_fw" in
      intros ? ? ? [? [? [fwb [Hfb [Hbb Hsb]]]]];
      apply hide in Hfb;
      subst; cbv [map.putmany_of_list_zip]; eexists; split; [ exact eq_refl | ].

    Local Ltac fp_len x :=
        match goal with H : (_ ⋆ _) ?mf |- _ =>
          let Ht := fresh in
          eassert (Ht : (FElem_Fp _ x ⋆ _) mf) by ecancel_assumption;
          let Hfe := fresh in
          destruct Ht as [? [? [_ [Hfe _]]]];
          exact (BLS12_CycExp.Fp_FElem_length _ _ _ Hfe)
        end.

    Lemma fp12_set_one_functional_wp :
      forall functions (HFfromword : BLS12_CycExp.spec_of_Fp_from_word functions)
        (a : word) (old : Fp12_felem) (R : mem -> Prop) tr (m : mem) (l : locals)
        (post : Semantics.trace -> mem -> locals -> Prop),
        map.get l "result" = Some a ->
        (FElem_Fp12 a old ⋆ R) m ->
        (forall m' (one : Fp12_felem),
           Fp12_bounded Fp12_tight one ->
           Fp12_feval one = P.fp12_one PrimeField.M_pos ->
           (FElem_Fp12 a one ⋆ R) m' -> post tr m' l) ->
        WeakestPrecondition.cmd functions (BLS12_Pairing.fp12_set_one "result") tr m l post.
    Proof.
      intros functions HFfromword a old R tr m l post Hget Hsep Hpost.
      apply BLS12_CycExp.FElem_Fp12_split6 in Hsep.
      unfold BLS12_Pairing.fp12_set_one, BLS12_Pairing.cmd_seq_list.
      unfold BLS12_Pairing.expr_fp12_c0, BLS12_Pairing.expr_fp12_c1,
             BLS12_Pairing.expr_fp6_c0, BLS12_Pairing.expr_fp6_c1,
             BLS12_Pairing.expr_fp6_c2, BLS12_Pairing.expr_fp_snd.
      fw_pair HFfromword a (c0_felem (d0_felem old)).
      fw_pair HFfromword (word.add a fp6_c1_off) (c1_felem (d0_felem old)).
      fw_pair HFfromword (word.add a fp6_c2_off) (c2_felem (d0_felem old)).
      fw_pair HFfromword (word.add a (word.of_Z fp6_felem_offset)) (c0_felem (d1_felem old)).
      fw_pair HFfromword (word.add (word.add a (word.of_Z fp6_felem_offset)) fp6_c1_off) (c1_felem (d1_felem old)).
      fw_pair HFfromword (word.add (word.add a (word.of_Z fp6_felem_offset)) fp6_c2_off) (c2_felem (d1_felem old)).
      match goal with H : (_ ⋆ _) ?mf |- _ => set (m_fw := mf) in * end.
      assert (L0 : length fw = Fp_fsw) by fp_len fw.
      assert (L1 : length fw0 = Fp_fsw) by fp_len fw0.
      assert (L2 : length fw1 = Fp_fsw) by fp_len fw1.
      assert (L3 : length fw2 = Fp_fsw) by fp_len fw2.
      assert (L4 : length fw3 = Fp_fsw) by fp_len fw3.
      assert (L5 : length fw4 = Fp_fsw) by fp_len fw4.
      assert (L6 : length fw5 = Fp_fsw) by fp_len fw5.
      assert (L7 : length fw6 = Fp_fsw) by fp_len fw6.
      assert (L8 : length fw7 = Fp_fsw) by fp_len fw7.
      assert (L9 : length fw8 = Fp_fsw) by fp_len fw8.
      assert (L10 : length fw9 = Fp_fsw) by fp_len fw9.
      assert (L11 : length fw10 = Fp_fsw) by fp_len fw10.
      eapply (Hpost _ (((fw ++ fw0) ++ (fw1 ++ fw2) ++ (fw3 ++ fw4)) ++
                       ((fw5 ++ fw6) ++ (fw7 ++ fw8) ++ (fw9 ++ fw10)))).
      { apply BLS12_CycExp.Fp12_bounded_join6;
          [ rewrite length_app, L0, L1; reflexivity
          | rewrite length_app, L2, L3; reflexivity
          | rewrite length_app, L4, L5; reflexivity
          | rewrite length_app, L6, L7; reflexivity
          | rewrite length_app, L8, L9; reflexivity
          | rewrite length_app, L10, L11; reflexivity
          | apply BLS12_CycExp.Fp2_bounded_join; assumption
          | apply BLS12_CycExp.Fp2_bounded_join; assumption
          | apply BLS12_CycExp.Fp2_bounded_join; assumption
          | apply BLS12_CycExp.Fp2_bounded_join; assumption
          | apply BLS12_CycExp.Fp2_bounded_join; assumption
          | apply BLS12_CycExp.Fp2_bounded_join; assumption ]. }
      { repeat match goal with H : hidden _ |- _ => apply unhide in H end.
        apply Fp12_feval_set_one; assumption. }
      eapply BLS12_CycExp.FElem_Fp12_join12; try eassumption.
      ecancel_assumption_impl.
    Qed.

    (* ================================================================ *)
    (* One cyclotomic squaring, functional                              *)
    (* ================================================================ *)

    Local Ltac felem_len P :=
      match goal with
      | |- Datatypes.length ?x = _ =>
        let Ht := fresh in
        eassert (Ht : (P _ x ⋆ _) _) by ecancel_assumption;
        let Hfe := fresh in
        destruct Ht as [? [? [_ [Hfe _]]]];
        let Hl := fresh in
        destruct Hfe as [? [? [_ [[_ Hl] _]]]];
        exact Hl
      end.

    Lemma cyc_sqr_functional_wp :
      forall functions
        (HFp6mul : BLS12_CycExp.spec_of_Fp6_mul functions)
        (HFp6add : BLS12_CycExp.spec_of_Fp6_add functions)
        (HFp6mulv : BLS12_CycExp.spec_of_Fp6_mul_by_v functions)
        (HFpadd : BLS12_CycExp.spec_of_Fp_add functions)
        (a_r a_t0 a_t1 a_one : word) (r : Fp12_felem) (x0 x1 : Fp6_felem) (one : Fp_felem)
        (R : mem -> Prop) tr (m : mem) (l : locals)
        (post : Semantics.trace -> mem -> locals -> Prop),
        map.get l "result" = Some a_r ->
        map.get l "cyc_t0" = Some a_t0 ->
        map.get l "cyc_t1" = Some a_t1 ->
        map.get l "cyc_one" = Some a_one ->
        Fp12_bounded Fp12_tight r ->
        Fp_bounded Fp_tight one ->
        Fp_feval one = F.one ->
        (FElem_Fp12 a_r r ⋆ (FElem_Fp6 a_t0 x0 ⋆ (FElem_Fp6 a_t1 x1 ⋆ (FElem_Fp a_one one ⋆ R)))) m ->
        (forall m' (r' : Fp12_felem) (x0' x1' : Fp6_felem),
           Fp12_bounded Fp12_tight r' ->
           Fp12_feval r' = cyc_sqr_model (Fp12_feval r) ->
           (FElem_Fp12 a_r r' ⋆ (FElem_Fp6 a_t0 x0' ⋆ (FElem_Fp6 a_t1 x1' ⋆ (FElem_Fp a_one one ⋆ R)))) m' ->
           post tr m' l) ->
        WeakestPrecondition.cmd functions (BLS12_Pairing.cyc_sqr_body "result" "result") tr m l post.
    Proof.
      intros functions HFp6mul HFp6add HFp6mulv HFpadd a_r a_t0 a_t1 a_one r x0 x1 one R tr m l post
        Hgr Hgt0 Hgt1 Hgone Hbr Hbone Hone Hsep Hpost.
      apply hide in Hone.
      unfold BLS12_Pairing.cyc_sqr_body, BLS12_Pairing.cmd_seq_list.
      change Fp12_bounded with
        (fun (b : @AbstractField.bounds _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep') (felem : list word) =>
           Fp6_bounded b (d0_felem felem) /\ Fp6_bounded b (d1_felem felem)) in Hbr.
      cbv beta in Hbr. destruct Hbr as [Hbr0 Hbr1].
      destruct Hsep as [m_r [m_rest [[Heq Hd] [Hfe Hrest]]]].
      pose proof (DodecicFieldExtensions.Fp12_raw_FElem_split bls12_beta bls12_xi_re bls12_xi_im
        fp12_prefix fp6_prefix fp2_prefix a_r r m_r Hfe) as [m_d0 [m_d1 [[Heq12 Hd12] [Hf0 Hf1]]]].
      subst m m_r.
      assert (Hsep6 :
        (FElem_Fp6 a_r (d0_felem r) ⋆
         (FElem_Fp6 (word.add a_r (word.of_Z fp6_felem_offset)) (d1_felem r) ⋆
          (FElem_Fp6 a_t0 x0 ⋆ (FElem_Fp6 a_t1 x1 ⋆ (FElem_Fp a_one one ⋆ R)))))
          (map.putmany (map.putmany m_d0 m_d1) m_rest)).
      { rewrite <- map.putmany_assoc.
        pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd) as [Hd0r Hd1r].
        exists m_d0, (map.putmany m_d1 m_rest).
        split; [split; [reflexivity | apply map.disjoint_putmany_r; split; assumption] |].
        split; [exact Hf0 |].
        exists m_d1, m_rest. split; [split; [reflexivity | exact Hd1r] |].
        split; [exact Hf1 | exact Hrest]. }
      clear Hf0 Hf1 Hrest Hd Hd12.
      set (m0 := map.putmany (map.putmany m_d0 m_d1) m_rest) in *.

      (* Call 1: Fp6 mul(cyc_t0, c1, c1) *)
      repeat straightline.
      eexists; split; [eval_dexprs_fast |].
      eapply Semantics.weaken_call.
      1: { eapply HFp6mul.
           split; [exact Hbr1 |].
           split; [exact Hbr1 |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [y1 [Hfe1 [Hb_y1 Hsep1]]]]]. subst.
      apply F6mul_eq in Hfe1. apply hide in Hfe1.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 2: Fp6 mul(cyc_t1, c0, c1) *)
      repeat straightline.
      eexists; split; [eval_dexprs_fast |].
      eapply Semantics.weaken_call.
      1: { eapply HFp6mul.
           split; [exact Hbr0 |].
           split; [exact Hbr1 |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [y2 [Hfe2 [Hb_y2 Hsep2]]]]]. subst.
      apply F6mul_eq in Hfe2. apply hide in Hfe2.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 3: Fp6 mul_by_v(cyc_t0, cyc_t0) *)
      repeat straightline.
      eexists; split; [eval_dexprs_fast |].
      eapply Semantics.weaken_call.
      1: { eapply HFp6mulv.
           split; [exact Hb_y1 |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [y3 [Hfe3 [Hb_y3 Hsep3]]]]]. subst.
      apply F6mulv_eq in Hfe3. apply hide in Hfe3.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 4: Fp6 add(out_c0, cyc_t0, cyc_t0) *)
      repeat straightline.
      eexists; split; [eval_dexprs_fast |].
      eapply Semantics.weaken_call.
      1: { eapply HFp6add.
           split; [exact Hb_y3 |].
           split; [exact Hb_y3 |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [y4 [Hfe4 [Hb_y4 Hsep4]]]]]. subst.
      apply F6add_eq in Hfe4. apply hide in Hfe4.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 5: Fp add on the first Fp limb of out_c0 *)
      assert (Hb5 : Fp_bounded Fp_tight (fst_felem (c0_felem y4)) /\
                    Fp_bounded Fp_tight (snd_felem (c0_felem y4)) /\
                    Fp2_bounded Fp2_tight (c1_felem y4) /\ Fp2_bounded Fp2_tight (c2_felem y4)).
      { change Fp6_bounded with
          (fun (b : @AbstractField.bounds _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep') (felem : list word) =>
             Fp2_bounded b (c0_felem felem) /\ Fp2_bounded b (c1_felem felem) /\
             Fp2_bounded b (c2_felem felem)) in Hb_y4.
        cbv beta in Hb_y4. destruct Hb_y4 as [Hc0 [Hc1 Hc2]].
        change Fp2_bounded with
          (fun (b : @AbstractField.bounds _ _ _ _ _ _ bls12_Fp_rep) (ws : list word) =>
             Fp_bounded b (fst_felem ws) /\ Fp_bounded b (snd_felem ws)) in Hc0.
        cbv beta in Hc0. destruct Hc0 as [Hc0a Hc0b].
        split; [exact Hc0a |]. split; [exact Hc0b |]. split; [exact Hc1 | exact Hc2]. }
      destruct Hb5 as [Hb5a [Hb5b [Hb5c Hb5d]]].
      destruct Hsep4 as [m_y4 [m_r4 [Sy4 [Hfe4m Hr4]]]].
      pose proof (CubicFieldExtensions.Fp6_raw_FElem_split bls12_beta bls12_xi_re bls12_xi_im
        fp6_prefix fp2_prefix a_r y4 m_y4 Hfe4m) as Hy4s.
      pose proof (BLS12_CycExp.sep3_frame _ _ _ _ _ _ _ Sy4 Hy4s Hr4) as Hs5.
      clear Hy4s Hfe4m Hr4 Sy4.
      apply BLS12_PairingHelpers.FElem_Fp2_split_in_sep in Hs5.
      repeat straightline.
      eexists; split; [eval_dexprs_fast |].
      eapply Semantics.weaken_call.
      1: { eapply HFpadd.
           split; [exact Hb5a |].
           split; [exact Hbone |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [z [Hfe5 [Hb_z Hsep5]]]]]. subst.
      apply Fpadd_eq in Hfe5. apply hide in Hfe5.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
      assert (Lz : Datatypes.length z = Fp_fsw) by felem_len constr:(FElem_Fp).
      assert (Ls : Datatypes.length (snd_felem (c0_felem y4)) = Fp_fsw) by felem_len constr:(FElem_Fp).
      assert (L1 : Datatypes.length (c1_felem y4) = Fp2_fsw) by felem_len constr:(FElem_Fp2).
      assert (L2 : Datatypes.length (c2_felem y4) = Fp2_fsw) by felem_len constr:(FElem_Fp2).
      eassert (Hj : (FElem_Fp a_r z ⋆ (FElem_Fp (word.add a_r (word.of_Z fp_felem_offset))
                       (snd_felem (c0_felem y4)) ⋆ _)) _) by ecancel_assumption.
      apply BLS12_PairingHelpers.FElem_Fp_join_in_sep in Hj; [| exact Lz | exact Ls].
      eassert (Hk : ((FElem_Fp2 a_r (z ++ snd_felem (c0_felem y4)) ⋆
                      (FElem_Fp2 (word.add a_r fp6_c1_off) (c1_felem y4) ⋆
                       FElem_Fp2 (word.add a_r fp6_c2_off) (c2_felem y4))) ⋆ _) _)
        by ecancel_assumption.
      clear Hj Hsep5.
      assert (L0 : Datatypes.length (z ++ snd_felem (c0_felem y4)) = Fp2_fsw)
        by (rewrite length_app, Lz, Ls; reflexivity).
      destruct Hk as [mk [mr [Sk [Hk1 Hk2]]]].
      apply (@CubicFieldExtensions.Fp6_raw_FElem_join _ _ _ _ wordok mapok bls12_pf_params
          bls12_beta bls12_xi_re bls12_xi_im bls12_Fp_rep fp6_prefix fp2_prefix _ _ _ _ _
          L0 L1 L2) in Hk1.
      set (c0n := (z ++ snd_felem (c0_felem y4)) ++ c1_felem y4 ++ c2_felem y4) in *.
      assert (Hsep5' : (FElem_Fp6 a_r c0n ⋆ _) _) by (exists mk, mr; exact (conj Sk (conj Hk1 Hk2))).
      clear Hk1 Hk2 Sk.

      (* Call 6: Fp6 add(out_c1, cyc_t1, cyc_t1) *)
      repeat straightline.
      eexists; split; [eval_dexprs_fast |].
      eapply Semantics.weaken_call.
      1: { eapply HFp6add.
           split; [exact Hb_y2 |].
           split; [exact Hb_y2 |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [y6 [Hfe6 [Hb_y6 Hsep6']]]]]. subst.
      apply F6add_eq in Hfe6. apply hide in Hfe6.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      assert (Lc0n : Datatypes.length c0n = Fp6_fsw)
        by (subst c0n; rewrite !length_app, Lz, Ls, L1, L2; reflexivity).
      assert (Ly6 : Datatypes.length y6 = Fp6_fsw) by felem_len constr:(FElem_Fp6).
      eassert (H12 : ((FElem_Fp6 a_r c0n ⋆
                       FElem_Fp6 (word.add a_r (word.of_Z fp6_felem_offset)) y6) ⋆ _) _)
        by ecancel_assumption.
      destruct H12 as [m12 [mr12 [S12 [H12a H12b]]]].
      apply (@DodecicFieldExtensions.Fp12_raw_FElem_join _ _ _ _ wordok mapok bls12_pf_params
          bls12_Fp_rep bls12_beta bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix
          _ _ _ _ Lc0n Ly6) in H12a.
      eapply (Hpost _ (c0n ++ y6) y3 y2).
      { change Fp12_bounded with
          (fun (b : @AbstractField.bounds _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep')
               (felem : list word) =>
            Fp6_bounded b (d0_felem felem) /\ Fp6_bounded b (d1_felem felem)); cbv beta.
        rewrite (@DodecicFieldExtensions.d0_felem_app _ _ _ _ bls12_pf_params bls12_Fp_rep bls12_beta
          bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix _ _ Lc0n).
        rewrite (@DodecicFieldExtensions.d1_felem_app _ _ _ _ bls12_pf_params bls12_Fp_rep bls12_beta
          bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix _ _ Lc0n).
        split; [| exact Hb_y6].
        subst c0n.
        change Fp6_bounded with
          (fun (b : @AbstractField.bounds _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep')
               (felem : list word) =>
            Fp2_bounded b (c0_felem felem) /\ Fp2_bounded b (c1_felem felem) /\
            Fp2_bounded b (c2_felem felem)); cbv beta.
        rewrite (@CubicFieldExtensions.c0_felem_app _ _ _ _ bls12_pf_params bls12_beta bls12_Fp_rep fp2_prefix _ _ _ L0).
        rewrite (@CubicFieldExtensions.c1_felem_app _ _ _ _ bls12_pf_params bls12_beta bls12_Fp_rep fp2_prefix _ _ _ L0 L1).
        rewrite (@CubicFieldExtensions.c2_felem_app _ _ _ _ bls12_pf_params bls12_beta bls12_Fp_rep fp2_prefix _ _ _ L0 L1).
        split; [apply BLS12_CycExp.Fp2_bounded_join; [exact Lz | exact Hb_z | exact Hb5b] |].
        split; [exact Hb5c | exact Hb5d]. }
      { apply unhide in Hfe1, Hfe2, Hfe3, Hfe4, Hfe5, Hfe6, Hone.
        subst c0n.
        exact (cyc_sqr_chain r y1 y2 y3 y4 y6 z one Lz L0 L1 Lc0n Hfe1 Hfe2 Hfe3 Hfe4 Hfe5 Hone Hfe6). }
      eassert (Hfin : ((FElem_Fp12 a_r (c0n ++ y6)) ⋆ _) _) by (exists m12, mr12; exact (conj S12 (conj H12a H12b))).
      ecancel_assumption.
    Qed.

    (* ================================================================ *)
    (* The function, functional, for any exponent 0 <= e < 2^64         *)
    (* ================================================================ *)

    Definition spec_of_cyc_exp_neg_functional (name : string) (e : Z) : spec_of name :=
      fnspec! name (pout pbase : word)
        / (old_out base_val : Fp12_felem) Rr,
      { requires tr mem :=
          Fp12_bounded Fp12_tight base_val /\
          (FElem_Fp12 pbase base_val ⋆ (FElem_Fp12 pout old_out ⋆ Rr)) mem;
        ensures tr' mem' :=
          tr = tr' /\ exists out,
            (cyclotomic (Fp12_feval base_val) ->
             Fp12_feval out =
               P.fp12_conjugate PrimeField.M_pos (pw (Fp12_feval base_val) (Z.to_N e))) /\
            Fp12_bounded Fp12_loose out /\
            (FElem_Fp12 pout out ⋆ (FElem_Fp12 pbase base_val ⋆ Rr)) mem' }.

    Definition cyc_exp_inv_f (e : Z)
      (a_r a_t0 a_t1 a_one pbase pout : word) (one_v : Fp_felem) (base_val old_out : Fp12_felem)
      (Rr : mem -> Prop) (tr : Semantics.trace)
      (v : nat) (t : Semantics.trace) (m : mem) (l : locals) : Prop :=
      t = tr /\ (v <= 64)%nat /\
      exists (r : Fp12_felem) (x0 x1 : Fp6_felem),
        Fp12_bounded Fp12_tight r /\
        hidden (cyclotomic (Fp12_feval base_val) ->
                Fp12_feval r = pw (Fp12_feval base_val) (Z.to_N (Z.shiftr e (Z.of_nat v)))) /\
        (FElem_Fp12 a_r r ⋆ (FElem_Fp6 a_t0 x0 ⋆ (FElem_Fp6 a_t1 x1 ⋆ (FElem_Fp a_one one_v ⋆
          (FElem_Fp12 pbase base_val ⋆ (FElem_Fp12 pout old_out ⋆ Rr)))))) m /\
        map.get l "i" = Some (word.of_Z (Z.of_nat v)) /\
        map.get l "result" = Some a_r /\
        map.get l "cyc_t0" = Some a_t0 /\
        map.get l "cyc_t1" = Some a_t1 /\
        map.get l "cyc_one" = Some a_one /\
        map.get l "base" = Some pbase /\
        map.get l "out" = Some pout.

    Local Ltac solve_gets :=
      repeat (first [ rewrite map.get_put_same; reflexivity
                    | rewrite map.get_put_diff by congruence ]);
      try assumption.

    Local Ltac dealloc_with P :=
      match goal with
      | |- exists _ _, Memory.anybytes ?a _ _ /\ _ =>
        let H := fresh in
        eassert (H : (_ ⋆ P a _) _) by ecancel_assumption;
        destruct H as [? [? [[? ?] [? ?]]]];
        eexists _, _;
        split; [eapply AbstractField.FElem_to_bytes; eassumption|];
        split; [split; [eassumption | eassumption]|]
      end.

    Lemma bit_word_spec (e : Z) (v : nat) :
      (0 <= e < 2 ^ 64) -> (0 < v <= 64)%nat ->
      word.unsigned (word := word)
        (word.and (word.sru (word.of_Z e) (word.sub (word.of_Z (Z.of_nat v)) (word.of_Z 1)))
                  (word.of_Z 1)) =
      (if Z.testbit e (Z.of_nat (v - 1)) then 1 else 0).
    Proof.
      intros He Hv.
      assert (Hi : word.unsigned (word := word) (word.sub (word.of_Z (Z.of_nat v)) (word.of_Z 1))
                   = Z.of_nat (v - 1)).
      { rewrite word.unsigned_sub_nowrap; rewrite !word.unsigned_of_Z_nowrap; lia. }
      rewrite word.unsigned_and_nowrap, word.unsigned_sru_nowrap by (rewrite Hi; lia).
      rewrite Hi, !word.unsigned_of_Z_nowrap by lia.
      change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia.
      rewrite Zmod_odd, <- Z.bit0_odd, Z.shiftr_spec by lia.
      reflexivity.
    Qed.

    Lemma cyc_exp_neg_functional_ok :
      forall (name : string) (e : Z) functions
        (He : 0 <= e < 2 ^ 64)
        (EnvContains : map.get functions name = Some (snd (BLS12_Pairing.cyc_exp_neg_fn name e)))
        (HFp12mul : BLS12_CycExp.spec_of_Fp12_mul functions)
        (HFp12conj : BLS12_CycExp.spec_of_Fp12_conjugate functions)
        (HFp6mul : BLS12_CycExp.spec_of_Fp6_mul functions)
        (HFp6add : BLS12_CycExp.spec_of_Fp6_add functions)
        (HFp6mulv : BLS12_CycExp.spec_of_Fp6_mul_by_v functions)
        (HFpadd : BLS12_CycExp.spec_of_Fp_add functions)
        (HFfromword : BLS12_CycExp.spec_of_Fp_from_word functions),
      spec_of_cyc_exp_neg_functional name e functions.
    Proof.
      intros name e functions He EnvContains HFp12mul HFp12conj HFp6mul HFp6add HFp6mulv HFpadd HFfromword.
      unfold spec_of_cyc_exp_neg_functional.
      intros pout pbase old_out base_val Rr tr mem0 [Hbbase Hsep].
      apply hide in He.
      eapply start_func; [exact EnvContains | clear EnvContains].
      cbv [WeakestPrecondition.func].
      unfold BLS12_Pairing.cyc_exp_neg_fn. simpl snd. simpl fst. cbv match beta.
      eexists. split. { exact eq_refl. }

      straightline. split. { apply Z_mod_mult. }
      intros a_r mS_r mC_r HaS_r HmS_r.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls12_Fp12_params' _ _ _ _
        bls12_Fp12_rep' wordok mapok a_r mS_r) HaS_r) as [ri Hri].
      straightline. split. { apply Z_mod_mult. }
      intros a_t0 mS_t0 mC_t0 HaS_t0 HmS_t0.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls12_Fp6_params' _ _ _ _
        bls12_Fp6_rep' wordok mapok a_t0 mS_t0) HaS_t0) as [t0i Ht0i].
      straightline. split. { apply Z_mod_mult. }
      intros a_t1 mS_t1 mC_t1 HaS_t1 HmS_t1.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls12_Fp6_params' _ _ _ _
        bls12_Fp6_rep' wordok mapok a_t1 mS_t1) HaS_t1) as [t1i Ht1i].
      straightline. split. { apply Z_mod_mult. }
      intros a_one mS_one mC_one HaS_one HmS_one.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ _ _ _ _ _
        bls12_Fp_rep wordok mapok a_one mS_one) HaS_one) as [onei Honei].

      pose proof (proj1 (map.split_comm mC_r mem0 mS_r) HmS_r) as HmS_r'.
      assert (Hl1 : (FElem_Fp12 a_r ri ⋆ (FElem_Fp12 pbase base_val ⋆ (FElem_Fp12 pout old_out ⋆ Rr))) mC_r).
      { exists mS_r, mem0. exact (conj HmS_r' (conj Hri Hsep)). }
      pose proof (proj1 (map.split_comm mC_t0 mC_r mS_t0) HmS_t0) as HmS_t0'.
      assert (Hl2 : (FElem_Fp6 a_t0 t0i ⋆ (FElem_Fp12 a_r ri ⋆ (FElem_Fp12 pbase base_val ⋆ (FElem_Fp12 pout old_out ⋆ Rr)))) mC_t0).
      { exists mS_t0, mC_r. exact (conj HmS_t0' (conj Ht0i Hl1)). }
      pose proof (proj1 (map.split_comm mC_t1 mC_t0 mS_t1) HmS_t1) as HmS_t1'.
      assert (Hl3 : (FElem_Fp6 a_t1 t1i ⋆ (FElem_Fp6 a_t0 t0i ⋆ (FElem_Fp12 a_r ri ⋆ (FElem_Fp12 pbase base_val ⋆ (FElem_Fp12 pout old_out ⋆ Rr))))) mC_t1).
      { exists mS_t1, mC_t0. exact (conj HmS_t1' (conj Ht1i Hl2)). }
      pose proof (proj1 (map.split_comm mC_one mC_t1 mS_one) HmS_one) as HmS_one'.
      assert (Hl4 : (FElem_Fp a_one onei ⋆ (FElem_Fp6 a_t1 t1i ⋆ (FElem_Fp6 a_t0 t0i ⋆ (FElem_Fp12 a_r ri ⋆ (FElem_Fp12 pbase base_val ⋆ (FElem_Fp12 pout old_out ⋆ Rr)))))) mC_one).
      { exists mS_one, mC_t1. exact (conj HmS_one' (conj Honei Hl3)). }
      clear Hsep Hl1 Hl2 Hl3 Hri Ht0i Ht1i Honei HaS_r HaS_t0 HaS_t1 HaS_one HmS_r HmS_t0 HmS_t1 HmS_one
            HmS_r' HmS_t0' HmS_t1' HmS_one'.

      unfold BLS12_Pairing.cyc_exp_neg_body, BLS12_Pairing.cmd_seq_list.

      (* from_word(cyc_one, 1) *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _ onei). ecancel_assumption. }
      intros ? ? ? [? [? [one_v [Hfe_one [Hb_one Hsep_one]]]]]. subst.
      assert (Hone : Fp_feval one_v = F.one) by (rewrite Hfe_one; reflexivity).
      clear Hfe_one. apply hide in Hone.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* fp12_set_one "result" *)
      unfold1_cmd_goal; cbv beta match delta [cmd_body].
      eapply (fp12_set_one_functional_wp functions HFfromword a_r ri).
      { subst l2 l1 l0 l; solve_gets. }
      { ecancel_assumption. }
      intros m1 one12 Hb12 Hfe12 Hs12.
      apply hide in Hfe12.

      (* i = 64 *)
      repeat straightline.
      eapply Loops.while_localsmap
        with (v0 := 64%nat) (lt := Nat.lt)
             (invariant := cyc_exp_inv_f e a_r a_t0 a_t1 a_one pbase pout one_v base_val old_out Rr t').
      { exact lt_wf. }
      { unfold cyc_exp_inv_f. split; [reflexivity |]. split; [lia |].
        exists one12, t0i, t1i. split; [exact Hb12 |].
        split.
        { constructor. intros _. apply unhide in Hfe12. rewrite Hfe12.
          symmetry. apply cyc_exp_init. exact (unhide _ He). }
        split; [ecancel_assumption |].
        subst l3 l2 l1 l0 l i. repeat split; solve_gets. }
      { intros v t_v m_v l_v Hinv.
        destruct Hinv as [Ht [Hv_le [r_v [x0_v [x1_v [Hbr [Hfr [Hsep_v [Hgi [Hgr [Hgt0 [Hgt1 [Hgone [Hgb Hgo]]]]]]]]]]]]]].
        subst t_v.
        exists (word.of_Z (Z.of_nat v)). cbv [Markers.split].
        split. { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body WeakestPrecondition.get]. eexists. split; [exact Hgi | reflexivity]. }
        split.
        { intro Hne.
          assert (Hv_pos : (0 < v)%nat) by
            (destruct v; [exfalso; apply Hne; vm_compute; reflexivity | lia]).
          unfold BLS12_Pairing.cyc_exp_loop, BLS12_Pairing.cmd_seq_list.
          eexists. split.
          { unfold DEXPR. repeat (first [ solve [eval_dexprs_fast] | straightline ]). }
          cbv beta delta [dlet.dlet].
          intro l4.
          unfold1_cmd_goal; cbv beta match delta [cmd_body].
          eapply (cyc_sqr_functional_wp functions HFp6mul HFp6add HFp6mulv HFpadd a_r a_t0 a_t1 a_one r_v x0_v x1_v one_v).
          1-4: subst l4; solve_gets.
          { exact Hbr. }
          { exact Hb_one. }
          { exact (unhide _ Hone). }
          { ecancel_assumption. }
          intros m2 r2 x0' x1' Hb2 Hfe2 Hs2.
          apply hide in Hfe2.
          eexists. split.
          { unfold DEXPR. subst l4. repeat (first [ solve [eval_dexprs_fast] | straightline ]). }
          cbv beta delta [dlet.dlet].
          intro l5.
          unfold1_cmd_goal; cbv beta match delta [cmd_body].
          eexists. split.
          { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body WeakestPrecondition.get].
            eexists. split. { subst l5. rewrite map.get_put_same. reflexivity. } reflexivity. }
          (* the model of this iteration *)
          assert (Hstep : forall HB : cyclotomic (Fp12_feval base_val),
            (if Z.testbit e (Z.of_nat (v - 1))
             then P.fp12_mul PrimeField.M_pos (Fp12_feval r2) (Fp12_feval base_val)
             else Fp12_feval r2)
            = pw (Fp12_feval base_val) (Z.to_N (Z.shiftr e (Z.of_nat (v - 1))))).
          { intros HB.
            pose proof (cyc_exp_step (Fp12_feval base_val) e (v - 1) (proj1 (unhide _ He)) HB) as Hs.
            replace (S (v - 1)) with v in Hs by lia.
            rewrite <- ((unhide _ Hfr) HB) in Hs.
            rewrite <- (unhide _ Hfe2) in Hs.
            exact Hs. }
          pose proof (bit_word_spec e v (unhide _ He) (conj Hv_pos Hv_le)) as Hbitv.
          split.
          { intro Hbit.
            assert (Htb : Z.testbit e (Z.of_nat (v - 1)) = true).
            { destruct (Z.testbit e (Z.of_nat (v - 1))) eqn:Etb; [reflexivity |].
              exfalso. apply Hbit. try rewrite Etb in Hbitv. exact Hbitv. }
            rewrite Htb in Hstep.
            unfold1_cmd_goal; cbv beta match delta [cmd_body].
            eexists; split; [subst l5 l4; eval_dexprs_fast |].
            eapply Semantics.weaken_call.
            1: { eapply HFp12mul.
                 split; [exact Hb2 |].
                 split; [exact Hbbase |].
                 split; [eexists; ecancel_assumption_with_copy |].
                 split; [eexists; ecancel_assumption_with_copy |].
                 ecancel_assumption_with_copy. }
            intros ? ? ? [? [? [r3 [Hfe3 [Hb3 Hs3]]]]]. subst.
            apply F12mul_eq in Hfe3. apply hide in Hfe3.
            cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
            exists (v - 1)%nat. split; [| unfold Nat.lt; lia].
            unfold cyc_exp_inv_f. split; [reflexivity |]. split; [lia |].
            exists r3, x0', x1'. split; [exact Hb3 |].
            split. { constructor. intros HB. rewrite (unhide _ Hfe3). exact (Hstep HB). }
            split; [ecancel_assumption |].
            subst l5 l4.
            split. { rewrite map.get_put_diff by congruence. rewrite map.get_put_same. f_equal. cbv [Semantics.interp_binop]. rewrite Nat2Z.inj_sub by lia. ZnWords. }
            repeat split; solve_gets. }
          { intro Hbit0.
            assert (Htb : Z.testbit e (Z.of_nat (v - 1)) = false).
            { destruct (Z.testbit e (Z.of_nat (v - 1))) eqn:Etb; [| reflexivity].
              exfalso. try rewrite Etb in Hbitv.
              pose proof (eq_trans (eq_sym Hbitv) Hbit0) as Hc. discriminate Hc. }
            rewrite Htb in Hstep.
            repeat straightline.
            exists (v - 1)%nat. split; [| unfold Nat.lt; lia].
            unfold cyc_exp_inv_f. split; [reflexivity |]. split; [lia |].
            exists r2, x0', x1'. split; [exact Hb2 |].
            split. { constructor. intros HB. exact (Hstep HB). }
            split; [ecancel_assumption |].
            subst l5 l4.
            split. { rewrite map.get_put_diff by congruence. rewrite map.get_put_same. f_equal. cbv [Semantics.interp_binop]. rewrite Nat2Z.inj_sub by lia. ZnWords. }
            repeat split; solve_gets. } }
        { intro Heq.
          assert (Hv0 : v = 0%nat).
          { destruct v; [reflexivity | exfalso].
            rewrite word.unsigned_of_Z_nowrap in Heq by lia. lia. }
          subst v.
          unfold1_cmd_goal; cbv beta match delta [cmd_body].
          eexists; split; [eval_dexprs_fast |].
          eapply Semantics.weaken_call.
          1: { eapply HFp12conj.
               split; [exact Hbr |].
               split; [eexists; ecancel_assumption_with_copy |].
               ecancel_assumption_with_copy. }
          intros ? ? ? [? [? [o [Hfeo [Hbo Hso]]]]]. subst.
          apply F12conj_eq in Hfeo. apply hide in Hfeo.
          cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
          dealloc_with constr:(FElem_Fp).
          dealloc_with constr:(FElem_Fp6).
          dealloc_with constr:(FElem_Fp6).
          dealloc_with constr:(FElem_Fp12).
          cbv [list_map list_map_body WeakestPrecondition.get].
          split; [reflexivity |]. split; [reflexivity |].
          exists o.
          split.
          { intros HB. rewrite (unhide _ Hfeo), ((unhide _ Hfr) HB). rewrite cyc_exp_final. reflexivity. }
          split; [exact Hbo |].
          ecancel_assumption. } }
    Qed.

    Lemma bls12_Fp12_cyc_exp_x_neg_functional_ok :
      forall functions
        (EnvContains : map.get functions "bls12_Fp12_cyc_exp_x_neg" =
          Some (snd BLS12_Pairing.bls12_Fp12_cyc_exp_x_neg))
        (HFp12mul : BLS12_CycExp.spec_of_Fp12_mul functions)
        (HFp12conj : BLS12_CycExp.spec_of_Fp12_conjugate functions)
        (HFp6mul : BLS12_CycExp.spec_of_Fp6_mul functions)
        (HFp6add : BLS12_CycExp.spec_of_Fp6_add functions)
        (HFp6mulv : BLS12_CycExp.spec_of_Fp6_mul_by_v functions)
        (HFpadd : BLS12_CycExp.spec_of_Fp_add functions)
        (HFfromword : BLS12_CycExp.spec_of_Fp_from_word functions),
      spec_of_cyc_exp_neg_functional "bls12_Fp12_cyc_exp_x_neg" P.bls_x functions.
    Proof.
      intros. exact (cyc_exp_neg_functional_ok "bls12_Fp12_cyc_exp_x_neg" P.bls_x functions
        ltac:(cbv; split; congruence)
        EnvContains HFp12mul HFp12conj HFp6mul HFp6add HFp6mulv HFpadd HFfromword).
    Qed.

    Lemma bls12_Fp12_cyc_exp_c_neg_functional_ok :
      forall functions
        (EnvContains : map.get functions "bls12_Fp12_cyc_exp_c_neg" =
          Some (snd BLS12_Pairing.bls12_Fp12_cyc_exp_c_neg))
        (HFp12mul : BLS12_CycExp.spec_of_Fp12_mul functions)
        (HFp12conj : BLS12_CycExp.spec_of_Fp12_conjugate functions)
        (HFp6mul : BLS12_CycExp.spec_of_Fp6_mul functions)
        (HFp6add : BLS12_CycExp.spec_of_Fp6_add functions)
        (HFp6mulv : BLS12_CycExp.spec_of_Fp6_mul_by_v functions)
        (HFpadd : BLS12_CycExp.spec_of_Fp_add functions)
        (HFfromword : BLS12_CycExp.spec_of_Fp_from_word functions),
      spec_of_cyc_exp_neg_functional "bls12_Fp12_cyc_exp_c_neg" P.bls_c functions.
    Proof.
      intros. exact (cyc_exp_neg_functional_ok "bls12_Fp12_cyc_exp_c_neg" P.bls_c functions
        ltac:(cbv; split; congruence)
        EnvContains HFp12mul HFp12conj HFp6mul HFp6add HFp6mulv HFpadd HFfromword).
    Qed.

End BLS12_CycExpFunctional.
