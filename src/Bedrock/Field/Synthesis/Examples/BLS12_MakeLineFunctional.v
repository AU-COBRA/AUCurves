(** * Functional correctness of bls12_make_line.

    [bls12_make_line_ok] in BLS12_PairingHelpers.v states bounds and frame only.
    [bls12_make_line_functional_ok] below has the same preconditions and adds
      Fp12_feval out = make_line_feval_model (feval lam) (feval xt) (feval yt) (feval xp) (feval yp)
    where [make_line_feval_model] is written with the bedrock2 feval models of the callees
    (Fp2 Fmul/Fsub/Fopp of the instance, fp2_mul_fp_model, F.of_Z 0 for from_word 0).
    [make_line_feval_model_eq] identifies the model with [Pairing.make_line], and
    [bls12_make_line_pairing_ok] states the post with [Pairing.make_line] directly.

    The instances are those of BLS12_PairingHelpers (Existing Instance), so the statements
    use the same constants as [bls12_make_line_ok].
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
Require Import Bedrock.Field.Synthesis.Examples.BLS12_CurveInstances.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingHelpers.
Require Theory.BLS12Pairing.Pairing.
Require Bedrock.Field.FieldExtensions.Theory.QuadraticExtensions.
Require Bedrock.Field.Synthesis.Examples.BLS12_Fp2Feval.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section BLS12_MakeLineFunctional.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    Existing Instances
      BLS12_PairingHelpers.bls12_pf_params
      BLS12_PairingHelpers.bls12_pf_params_ok.
    Existing Instance prime_field_parameters.

    Local Notation Fp := (F PrimeField.M_pos).
    Local Notation Fp2 := ((Fp * Fp)%type).
    Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
    Local Notation Fp12 := ((Fp6 * Fp6)%type).

    Existing Instances
      BLS12_PairingHelpers.bls12_Fp_rep
      BLS12_PairingHelpers.bls12_Fp_rep_ok.

    Let fp2_prefix := "bls12_Fp2_".
    Let fp6_prefix := "bls12_Fp6_".
    Let fp12_prefix := "bls12_Fp12_".
    Let bls12_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-1).
    Let bls12_xi_re : F PrimeField.M_pos := @F.one PrimeField.M_pos.
    Let bls12_xi_im : F PrimeField.M_pos := @F.one PrimeField.M_pos.

    Existing Instances
      BLS12_PairingHelpers.bls12_Fp2_params' BLS12_PairingHelpers.bls12_Fp2_rep'
      BLS12_PairingHelpers.bls12_Fp6_params' BLS12_PairingHelpers.bls12_Fp6_rep'
      BLS12_PairingHelpers.bls12_Fp12_params' BLS12_PairingHelpers.bls12_Fp12_rep'.

    Local Notation FElem_Fp := (@AbstractField.FElem _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation FElem_Fp2 := (@AbstractField.FElem _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation FElem_Fp6 := (@AbstractField.FElem _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep').
    Local Notation FElem_Fp12 := (@AbstractField.FElem _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp_feval := (@AbstractField.feval _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp2_feval := (@AbstractField.feval _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp12_feval := (@AbstractField.feval _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp_bounded := (@AbstractField.bounded_by _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp2_bounded := (@AbstractField.bounded_by _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp_tight := (@AbstractField.tight_bounds _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp_loose := (@AbstractField.loose_bounds _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp2_tight := (@AbstractField.tight_bounds _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp2_loose := (@AbstractField.loose_bounds _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp2_felem := (@AbstractField.felem _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp_felem := (@AbstractField.felem _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp12_felem := (@AbstractField.felem _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').

    Local Notation fp_felem_offset :=
      (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bls12_Fp_rep)).
    Local Notation fst_felem := (@QuadraticFieldExtensionsSpecs.fst_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).
    Local Notation snd_felem := (@QuadraticFieldExtensionsSpecs.snd_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).

    Local Typeclasses Opaque bls12_Fp12_params'.
    Local Typeclasses Opaque bls12_Fp6_params'.
    Local Typeclasses Opaque bls12_Fp2_params'.

    (* ============================================================ *)
    (* The feval model of bls12_make_line                            *)
    (* ============================================================ *)

    Definition make_line_feval_model (lam xt yt : Fp2) (xp yp : Fp) : Fp12 :=
      let z : Fp := F.of_Z PrimeField.M_pos 0 in
      (((@AbstractField.Fsub _ bls12_Fp2_params'
           (@AbstractField.Fmul _ bls12_Fp2_params' lam xt) yt,
         @AbstractField.Fopp _ bls12_Fp2_params'
           (BLS12_PairingHelpers.fp2_mul_fp_model lam xp)),
        (z, z)),
       (((z, z), (yp, z)), (z, z))).

    Lemma make_line_feval_model_eq : forall lam xt yt xp yp,
      make_line_feval_model lam xt yt xp yp =
      Pairing.make_line PrimeField.M_pos lam xt yt xp yp.
    Proof.
      intros lam xt yt xp yp.
      unfold make_line_feval_model, Pairing.make_line.
      change (@AbstractField.Fmul _ bls12_Fp2_params')
        with (QuadraticExtensions.mulp2 PrimeField.M_pos (F.of_Z PrimeField.M_pos (-1))).
      rewrite BLS12_Fp2Feval.mulp2_eq_fp2_mul.
      reflexivity.
    Qed.


    Local Notation Fp_fsw := (@AbstractField.felem_size_in_words _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp2_fsw := (@AbstractField.felem_size_in_words _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').

    Lemma Fp2_feval_app (a b : Fp_felem) :
      length a = Fp_fsw ->
      Fp2_feval (a ++ b) = (Fp_feval a, Fp_feval b).
    Proof.
      intros Ha.
      change (Fp2_feval (a ++ b)) with
        (Fp_feval (firstn Fp_fsw (a ++ b)), Fp_feval (skipn Fp_fsw (a ++ b))).
      rewrite (QuadraticFieldExtensions.firstn_app' _ _ _ Ha).
      rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Ha).
      reflexivity.
    Qed.

    Local Notation Fp6_feval := (@AbstractField.feval _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep').
    Local Notation Fp6_felem := (@AbstractField.felem _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep').
    Local Notation Fp6_fsw := (@AbstractField.felem_size_in_words _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep').

    Lemma Fp6_feval_app3 (a b c : Fp2_felem) :
      length a = Fp2_fsw -> length b = Fp2_fsw ->
      Fp6_feval (a ++ b ++ c) = ((Fp2_feval a, Fp2_feval b), Fp2_feval c).
    Proof.
      intros Ha Hb.
      change (Fp6_feval (a ++ b ++ c)) with
        ((Fp2_feval (firstn Fp2_fsw (a ++ b ++ c)),
          Fp2_feval (firstn Fp2_fsw (skipn Fp2_fsw (a ++ b ++ c)))),
         Fp2_feval (skipn (2 * Fp2_fsw) (a ++ b ++ c))).
      assert (Hab : length (a ++ b) = (2 * Fp2_fsw)%nat).
      { rewrite length_app, Ha, Hb. lia. }
      rewrite (QuadraticFieldExtensions.firstn_app' _ _ _ Ha).
      rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Ha).
      rewrite (QuadraticFieldExtensions.firstn_app' _ _ _ Hb).
      rewrite (app_assoc a b c).
      rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Hab).
      reflexivity.
    Qed.

    Lemma Fp12_feval_app (a b : Fp6_felem) :
      length a = Fp6_fsw ->
      Fp12_feval (a ++ b) = (Fp6_feval a, Fp6_feval b).
    Proof.
      intros Ha.
      change (Fp12_feval (a ++ b)) with
        (Fp6_feval (firstn Fp6_fsw (a ++ b)), Fp6_feval (skipn Fp6_fsw (a ++ b))).
      rewrite (QuadraticFieldExtensions.firstn_app' _ _ _ Ha).
      rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Ha).
      reflexivity.
    Qed.

    Local Opaque BLS12_PairingHelpers.bls12_Fp_rep.
    Lemma Fp12_feval_concat (o2 o4 : Fp2_felem) (w5 w6 w7 w8 y w10 w11 w12 : Fp_felem) :
      length o2 = Fp2_fsw -> length o4 = Fp2_fsw ->
      length w5 = Fp_fsw -> length w6 = Fp_fsw ->
      length w7 = Fp_fsw -> length w8 = Fp_fsw ->
      length y = Fp_fsw -> length w10 = Fp_fsw -> length w11 = Fp_fsw ->
      Fp12_feval ((o2 ++ o4 ++ (w5 ++ w6)) ++ ((w7 ++ w8) ++ (y ++ w10) ++ (w11 ++ w12))) =
      (((Fp2_feval o2, Fp2_feval o4), (Fp_feval w5, Fp_feval w6)),
       (((Fp_feval w7, Fp_feval w8), (Fp_feval y, Fp_feval w10)), (Fp_feval w11, Fp_feval w12))).
    Proof.
      intros H2 H4 H5 H6 H7 H8 Hy H10 H11.
      assert (L6 : List.length (o2 ++ o4 ++ (w5 ++ w6)) = Fp6_fsw).
      rewrite !length_app, H2, H4, H5, H6.
      change Fp6_fsw with (3 * Fp2_fsw)%nat.
      change Fp2_fsw with (2 * Fp_fsw)%nat.
      lia.
      assert (L78 : List.length (w7 ++ w8) = Fp2_fsw).
      rewrite length_app, H7, H8. change Fp2_fsw with (2 * Fp_fsw)%nat. lia.
      assert (Ly10 : List.length (y ++ w10) = Fp2_fsw).
      rewrite length_app, Hy, H10. change Fp2_fsw with (2 * Fp_fsw)%nat. lia.
      rewrite (Fp12_feval_app (o2 ++ o4 ++ (w5 ++ w6)) ((w7 ++ w8) ++ (y ++ w10) ++ (w11 ++ w12)) L6).
      rewrite (Fp6_feval_app3 o2 o4 (w5 ++ w6) H2 H4).
      rewrite (Fp6_feval_app3 (w7 ++ w8) (y ++ w10) (w11 ++ w12) L78 Ly10).
      rewrite (Fp2_feval_app w5 w6 H5), (Fp2_feval_app w7 w8 H7), (Fp2_feval_app y w10 Hy), (Fp2_feval_app w11 w12 H11).
      reflexivity.
    Qed.

    Local Notation zero_word_feval := (F.of_Z PrimeField.M_pos (@word.unsigned 64 word (word.of_Z 0))).

    Lemma make_line_feval_final (lam xt yt out1 out2 out3 out4 : Fp2_felem)
      (xp yp fw5 fw6 fw7 fw8 fw10 fw11 fw12 : Fp_felem) :
      length out2 = Fp2_fsw -> length out4 = Fp2_fsw ->
      length fw5 = Fp_fsw -> length fw6 = Fp_fsw -> length fw7 = Fp_fsw -> length fw8 = Fp_fsw ->
      length yp = Fp_fsw -> length fw10 = Fp_fsw -> length fw11 = Fp_fsw ->
      Fp2_feval out1 = @AbstractField.Fmul _ bls12_Fp2_params' (Fp2_feval lam) (Fp2_feval xt) ->
      Fp2_feval out2 = @AbstractField.Fsub _ bls12_Fp2_params' (Fp2_feval out1) (Fp2_feval yt) ->
      Fp2_feval out3 = BLS12_PairingHelpers.fp2_mul_fp_model (Fp2_feval lam) (Fp_feval xp) ->
      Fp2_feval out4 = @AbstractField.Fopp _ bls12_Fp2_params' (Fp2_feval out3) ->
      Fp_feval fw5 = zero_word_feval -> Fp_feval fw6 = zero_word_feval ->
      Fp_feval fw7 = zero_word_feval -> Fp_feval fw8 = zero_word_feval ->
      Fp_feval fw10 = zero_word_feval -> Fp_feval fw11 = zero_word_feval ->
      Fp_feval fw12 = zero_word_feval ->
      Fp12_feval ((out2 ++ out4 ++ (fw5 ++ fw6)) ++ ((fw7 ++ fw8) ++ (yp ++ fw10) ++ (fw11 ++ fw12))) =
      make_line_feval_model (Fp2_feval lam) (Fp2_feval xt) (Fp2_feval yt) (Fp_feval xp) (Fp_feval yp).
    Proof.
      intros L2 L4 L5 L6 L7 L8 Ly L10 L11 E1 E2 E3 E4 E5 E6 E7 E8 E10 E11 E12.
      rewrite (Fp12_feval_concat out2 out4 fw5 fw6 fw7 fw8 yp fw10 fw11 fw12
                 L2 L4 L5 L6 L7 L8 Ly L10 L11).
      rewrite E2, E1, E4, E3, E5, E6, E7, E8, E10, E11, E12.
      rewrite word.unsigned_of_Z_0.
      reflexivity.
    Qed.
    Local Transparent BLS12_PairingHelpers.bls12_Fp_rep.


    (* Notations of BLS12_PairingHelpers used by the copied proof *)
    Local Notation fp2_felem_offset :=
      (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep')).
    Local Notation Fp6_felem_size := (@AbstractField.felem_size_in_words _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep').
    Local Notation fp6_felem_offset :=
      (Memory.bytes_per_word 64 * Z.of_nat Fp6_felem_size).
    Local Notation c0_felem := (@CubicFieldExtensionsSpecs.c0_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).
    Local Notation c1_felem := (@CubicFieldExtensionsSpecs.c1_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).
    Local Notation c2_felem := (@CubicFieldExtensionsSpecs.c2_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).
    Local Notation d0_felem := (@DodecicFieldExtensionsSpecs.d0_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).
    Local Notation d1_felem := (@DodecicFieldExtensionsSpecs.d1_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).
    Local Notation fp6_c1_off :=
      (@CubicFieldExtensions.fp6_c1_offset _ _ _ _ bls12_pf_params bls12_beta bls12_Fp_rep fp2_prefix).
    Local Notation fp6_c2_off :=
      (@CubicFieldExtensions.fp6_c2_offset _ _ _ _ bls12_pf_params bls12_beta bls12_Fp_rep fp2_prefix).

    Lemma bls12_make_line_functional_ok :
      forall functions
        (EnvContains : map.get functions "bls12_make_line" =
          Some (snd bls12_make_line))
        (HFp2mul : spec_of_Fp2_mul functions)
        (HFp2sub : spec_of_Fp2_sub functions)
        (HFp2opp : spec_of_Fp2_opp functions)
        (HFp2mulfp : spec_of_bls12_Fp2_mul_fp functions)
        (HFpcopy : spec_of_Fp_felem_copy functions)
        (HFfromword : spec_of_Fp_from_word functions),
      forall pout plam pxt pyt pxp pyp
        (old_out : @AbstractField.felem _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep')
        (lam xt yt : Fp2_felem) (xp yp : Fp_felem) Rr tr mem,
        Fp2_bounded Fp2_tight lam /\
        Fp2_bounded Fp2_tight xt /\
        Fp2_bounded Fp2_tight yt /\
        Fp_bounded Fp_loose xp /\
        Fp_bounded Fp_loose yp /\
        (FElem_Fp12 pout old_out ⋆
         (FElem_Fp2 plam lam ⋆
          (FElem_Fp2 pxt xt ⋆
           (FElem_Fp2 pyt yt ⋆
            (FElem_Fp pxp xp ⋆
             (FElem_Fp pyp yp ⋆ Rr)))))) mem ->
        WeakestPrecondition.call functions "bls12_make_line" tr mem
          [pout; plam; pxt; pyt; pxp; pyp]
          (fun tr' mem' rets =>
            rets = [] /\ tr = tr' /\
            exists out,
              Fp12_feval out =
                make_line_feval_model (Fp2_feval lam) (Fp2_feval xt) (Fp2_feval yt)
                  (Fp_feval xp) (Fp_feval yp) /\
              @AbstractField.bounded_by _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep'
                (@AbstractField.loose_bounds _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep') out /\
              (FElem_Fp12 pout out ⋆
               (FElem_Fp2 plam lam ⋆
                (FElem_Fp2 pxt xt ⋆
                 (FElem_Fp2 pyt yt ⋆
                  (FElem_Fp pxp xp ⋆
                   (FElem_Fp pyp yp ⋆ Rr)))))) mem').
    Proof.
      intros functions EnvContains HFp2mul HFp2sub HFp2opp HFp2mulfp HFpcopy HFfromword
        pout plam pxt pyt pxp pyp old_out lam xt yt xp yp Rr tr mem0
        [Hblam [Hbxt [Hbyt [Hbxp [Hbyp Hsep]]]]].
      eapply start_func; [exact EnvContains | clear EnvContains].
      cbv [WeakestPrecondition.func].
      unfold bls12_make_line. simpl snd. simpl fst.
      cbv match beta.
      eexists. split. { exact eq_refl. }
      repeat straightline.

      (* === Stackalloc tmp (Fp2-sized) === *)
      split. { apply Z_mod_mult. }
      intros a_tmp mStack mCombined HstackTmp Hm_split.

      (* Convert anybytes to FElem_Fp2 *)
      pose proof (@AbstractField.FElem_from_bytes _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep'
        wordok mapok a_tmp) as Hfb_tmp.
      unfold AbstractField.Placeholder in Hfb_tmp.
      pose proof (proj1 (Hfb_tmp mStack) HstackTmp) as [tmp_val Htmp_felem].
      clear Hfb_tmp.

      (* Decompose precondition sep *)
      destruct Hsep as [m_out [m_r1 [[Heq0 Hd0] [Hfe_out Hr1]]]].
      destruct Hr1 as [m_lam [m_r2 [[Heq1 Hd1] [Hfe_lam Hr2]]]].
      destruct Hr2 as [m_xt [m_r3 [[Heq2 Hd2] [Hfe_xt Hr3]]]].
      destruct Hr3 as [m_yt [m_r4 [[Heq3 Hd3] [Hfe_yt Hr4]]]].
      destruct Hr4 as [m_xp [m_r5 [[Heq4 Hd4] [Hfe_xp Hr5]]]].
      destruct Hr5 as [m_yp [m_rr [[Heq5 Hd5] [Hfe_yp Hrr]]]].
      subst m_r1 m_r2 m_r3 m_r4 m_r5 mem0.

      (* Split Fp12 output into Fp6 halves *)
      pose proof (DodecicFieldExtensions.Fp12_raw_FElem_split bls12_beta bls12_xi_re bls12_xi_im
        fp12_prefix fp6_prefix fp2_prefix pout old_out m_out Hfe_out)
        as [m_fp6_0 [m_fp6_1 [Hsep_fp12 [Hfe_fp6_0 Hfe_fp6_1]]]].
      destruct Hsep_fp12 as [Heq_fp12 Hd_fp12].
      subst m_out.

      (* Split each Fp6 into 3 Fp2 components *)
      pose proof (CubicFieldExtensions.Fp6_raw_FElem_split bls12_beta bls12_xi_re bls12_xi_im
        fp6_prefix fp2_prefix
        pout _ m_fp6_0 Hfe_fp6_0)
        as [m_o00 [m_o01_02 [Hsep_c0 [Ho00 Ho01_02]]]].
      destruct Ho01_02 as [m_o01 [m_o02 [Hsep_o01_02 [Ho01 Ho02]]]].
      destruct Hsep_c0 as [? Hd_c0]. destruct Hsep_o01_02 as [? Hd_o01_02]. subst.

      pose proof (CubicFieldExtensions.Fp6_raw_FElem_split bls12_beta bls12_xi_re bls12_xi_im
        fp6_prefix fp2_prefix
        (word.add pout (word.of_Z fp6_felem_offset)) _ m_fp6_1 Hfe_fp6_1)
        as [m_o10 [m_o11_12 [Hsep_c1 [Ho10 Ho11_12]]]].
      destruct Ho11_12 as [m_o11 [m_o12 [Hsep_o11_12 [Ho11 Ho12]]]].
      destruct Hsep_c1 as [? Hd_c1]. destruct Hsep_o11_12 as [? Hd_o11_12]. subst.

      (* Derive pairwise disjointness *)
      split_all_disjointness.
      destruct Hm_split as [Heq_comb Hd_comb].
      split_all_disjointness.
      rewrite !map.putmany_assoc in Heq_comb.

      (* The FElem types from Fp6_raw_FElem_split use
         Fp2_field_parameters/Fp2_field_representation applied to fp2_prefix.
         We define a local alias to match what the split hypotheses produce. *)
      set (FE2 := @AbstractField.FElem _
        (Fp2_field_parameters bls12_beta fp2_prefix) _ _ _ _
        (Fp2_field_representation bls12_beta fp2_prefix)).

      (* Build combined sep on mCombined with all sub-FElems *)
      assert (Hsep :
        (FE2 pout (c0_felem (d0_felem old_out)) ⋆
         (FE2 (word.add pout fp6_c1_off) (c1_felem (d0_felem old_out)) ⋆
          (FE2 (word.add pout fp6_c2_off) (c2_felem (d0_felem old_out)) ⋆
           (FE2 (word.add pout (word.of_Z fp6_felem_offset)) (c0_felem (d1_felem old_out)) ⋆
            (FE2 (word.add (word.add pout (word.of_Z fp6_felem_offset)) fp6_c1_off)
               (c1_felem (d1_felem old_out)) ⋆
             (FE2 (word.add (word.add pout (word.of_Z fp6_felem_offset)) fp6_c2_off)
                (c2_felem (d1_felem old_out)) ⋆
              (FE2 plam lam ⋆
               (FE2 pxt xt ⋆
                (FE2 pyt yt ⋆
                 (FElem_Fp pxp xp ⋆
                  (FElem_Fp pyp yp ⋆
                   (Rr ⋆
                    FE2 a_tmp tmp_val))))))))))))
        mCombined).
      { subst mCombined FE2.
        rewrite <- ?map.putmany_assoc.
        exists m_o00, (map.putmany m_o01 (map.putmany m_o02
          (map.putmany m_o10 (map.putmany m_o11 (map.putmany m_o12
            (map.putmany m_lam (map.putmany m_xt (map.putmany m_yt
              (map.putmany m_xp (map.putmany m_yp (map.putmany m_rr mStack))))))))))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Ho00 |].
        exists m_o01, (map.putmany m_o02
          (map.putmany m_o10 (map.putmany m_o11 (map.putmany m_o12
            (map.putmany m_lam (map.putmany m_xt (map.putmany m_yt
              (map.putmany m_xp (map.putmany m_yp (map.putmany m_rr mStack)))))))))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Ho01 |].
        exists m_o02, (map.putmany m_o10 (map.putmany m_o11 (map.putmany m_o12
          (map.putmany m_lam (map.putmany m_xt (map.putmany m_yt
            (map.putmany m_xp (map.putmany m_yp (map.putmany m_rr mStack))))))))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Ho02 |].
        exists m_o10, (map.putmany m_o11 (map.putmany m_o12
          (map.putmany m_lam (map.putmany m_xt (map.putmany m_yt
            (map.putmany m_xp (map.putmany m_yp (map.putmany m_rr mStack)))))))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Ho10 |].
        exists m_o11, (map.putmany m_o12
          (map.putmany m_lam (map.putmany m_xt (map.putmany m_yt
            (map.putmany m_xp (map.putmany m_yp (map.putmany m_rr mStack))))))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Ho11 |].
        exists m_o12, (map.putmany m_lam (map.putmany m_xt (map.putmany m_yt
          (map.putmany m_xp (map.putmany m_yp (map.putmany m_rr mStack)))))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Ho12 |].
        exists m_lam, (map.putmany m_xt (map.putmany m_yt
          (map.putmany m_xp (map.putmany m_yp (map.putmany m_rr mStack))))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfe_lam |].
        exists m_xt, (map.putmany m_yt
          (map.putmany m_xp (map.putmany m_yp (map.putmany m_rr mStack)))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfe_xt |].
        exists m_yt, (map.putmany m_xp (map.putmany m_yp (map.putmany m_rr mStack))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfe_yt |].
        exists m_xp, (map.putmany m_yp (map.putmany m_rr mStack)).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfe_xp |].
        exists m_yp, (map.putmany m_rr mStack).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfe_yp |].
        exists m_rr, mStack.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact Hrr | exact Htmp_felem]. }

      (* FE2 and FElem_Fp2 are definitionally equal.
         Subst FE2 so all subsequent references use FElem_Fp2. *)
      subst FE2.
      (* Fold opaque instance names in Hsep so ecancel_assumption can
         unify Hsep's FElem terms with the specs' FElem_Fp2 terms. *)
      change (Fp2_field_parameters bls12_beta fp2_prefix)
        with bls12_Fp2_params' in Hsep.
      change (Fp2_field_representation bls12_beta fp2_prefix)
        with bls12_Fp2_rep' in Hsep.

      (* Fp2-level relax_bounds helper *)
      pose proof (@Fp2_field_representation_ok _ _ _ _ bls12_pf_params
        bls12_Fp_rep bls12_Fp_rep_ok bls12_beta fp2_prefix) as Fp2_rep_ok.

      (* === 13 call steps: 4 Fp2-level + 9 Fp-level === *)
      (* Unfold cmd_seq_list so straightline can process cmd.seq *)
      unfold BLS12_Pairing.cmd_seq_list.
      (* Unfold expression helpers so straightline can evaluate args *)
      unfold BLS12_Pairing.expr_fp12_c0, BLS12_Pairing.expr_fp12_c1,
             BLS12_Pairing.expr_fp6_c0, BLS12_Pairing.expr_fp6_c1,
             BLS12_Pairing.expr_fp6_c2, BLS12_Pairing.expr_fp_snd.

      (* === Call 1: fp2_mul(pout, plam, pxt) === *)
      (* out.c0.c0 = lam * x_t *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { pose proof HFp2mul as HF1.
           unfold spec_of_Fp2_mul, AbstractField.binop_spec in HF1.
           eapply (HF1 pout plam pxt
             (c0_felem (d0_felem old_out)) lam xt _ tr).
           split; [apply (@AbstractField.relax_bounds _ bls12_Fp2_params' _ _ _ _
             bls12_Fp2_rep' Fp2_rep_ok); exact Hblam |].
           split; [apply (@AbstractField.relax_bounds _ bls12_Fp2_params' _ _ _ _
             bls12_Fp2_rep' Fp2_rep_ok); exact Hbxt |].
           split; [eexists; pose proof Hsep as H'; ecancel_assumption |].
           split; [eexists; pose proof Hsep as H'; ecancel_assumption |].
           pose proof Hsep as H'. ecancel_assumption. }
      intros t1 m1 rets1 [Hrets1 [Htr1 [out1 [Hfeval1 [Hbound1 Hsep1]]]]].
      subst rets1. symmetry in Htr1. subst t1.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* === Call 2: fp2_sub(pout, pout, pyt) === *)
      (* out.c0.c0 -= y_t *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { pose proof HFp2sub as HF2.
           unfold spec_of_Fp2_sub, AbstractField.binop_spec in HF2.
           eapply (HF2 pout pout pyt
             out1 out1 yt _ tr).
           split; [cbv [bin_xbounds AbstractField.bin_sub]; exact Hbound1 |].
           split; [cbv [bin_ybounds AbstractField.bin_sub]; exact Hbyt |].
           split; [eexists; pose proof Hsep1 as H'; ecancel_assumption |].
           split; [eexists; pose proof Hsep1 as H'; ecancel_assumption |].
           pose proof Hsep1 as H'. ecancel_assumption. }
      intros t2 m2 rets2 [Hrets2 [Htr2 [out2 [Hfeval2 [Hbound2 Hsep2]]]]].
      subst rets2. symmetry in Htr2. subst t2.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* === Call 3: fp2_mul_fp(a_tmp, plam, pxp) === *)
      (* tmp = lam * x_p *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { pose proof HFp2mulfp as HF3.
           unfold spec_of_bls12_Fp2_mul_fp in HF3.
           eapply (HF3 a_tmp plam pxp
             tmp_val lam xp _ tr).
           split; [exact Hblam |].
           split; [exact Hbxp |].
           pose proof Hsep2 as H'. ecancel_assumption. }
      intros t3 m3 rets3 [Hrets3 [Htr3 [out3 [Hfeval3 [Hbound3 Hsep3]]]]].
      subst rets3. symmetry in Htr3. subst t3.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* === Call 4: fp2_opp(out.c0.c1, tmp) === *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { pose proof HFp2opp as HF4.
           unfold spec_of_Fp2_opp, AbstractField.unop_spec in HF4.
           (* The evaluated arg address is word.add pout (word.of_Z (bytes_per_word * Fp2_felem_size))
              which equals word.add pout fp6_c1_off definitionally.
              We use subst args to let Coq's unification handle it. *)
           subst args.
           eapply (HF4
             (word.add pout fp6_c1_off)
             a_tmp
             (c1_felem (d0_felem old_out)) out3 _ tr).
           split; [cbv [un_xbounds AbstractField.un_opp]; exact Hbound3 |].
           split; [eexists; pose proof Hsep3 as H'; ecancel_assumption |].
           pose proof Hsep3 as H'. ecancel_assumption. }
      intros t4 m4 rets4 [Hrets4 [Htr4 [out4 [Hfeval4 [Hbound4 Hsep4]]]]].
      subst rets4. symmetry in Htr4. subst t4.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* === Calls 5-12: from_word / fp_copy at Fp level === *)
      (* Strategy: for each call, use ecancel to rearrange the running
         sep so the target FElem_Fp2 is first, then apply
         FElem_Fp2_split_in_sep to get FElem_Fp entries. *)

      (* --- Call 5: from_word(out.c0.c2 fst, 0) --- *)
      repeat straightline.
      (* Split out.c0.c2 FElem_Fp2 into two FElem_Fp *)
      eassert (Hsep4_split5 :
        (FElem_Fp2 (word.add pout fp6_c2_off)
           (c2_felem (d0_felem old_out)) ⋆ _) m4).
      { pose proof Hsep4 as H'. ecancel_assumption. }
      apply FElem_Fp2_split_in_sep in Hsep4_split5.
      (* Hsep4_split5 : (FElem_Fp (pout+c2off) fst *
                          (FElem_Fp (pout+c2off+fpoff) snd * R5)) m4 *)
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (fst_felem (c2_felem (d0_felem old_out))) _ tr).
           exact Hsep4_split5. }
      intros t5 m5' rets5 [Hrets5 [Htr5 [fw5 [Hfeval5 [Hbound5 Hsep5]]]]].
      subst rets5. symmetry in Htr5. subst t5.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* --- Call 6: from_word(out.c0.c2 snd, 0) --- *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (snd_felem (c2_felem (d0_felem old_out))) _ tr).
           (* The goal address comes from straightline and uses expanded
              offsets. We need to match it with the opaque fp6_c2_off in Hsep5.
              Strategy: change the goal address to match the hypothesis form. *)
           match goal with
           | |- (?P ⋆ ?Q) ?m =>
             change ((FElem_Fp
               (word.add (word.add pout fp6_c2_off) (word.of_Z fp_felem_offset))
               (snd_felem (c2_felem (d0_felem old_out))) ⋆ Q) m)
           end.
           pose proof Hsep5 as H'. ecancel_assumption. }
      intros t6 m6' rets6 [Hrets6 [Htr6 [fw6 [Hfeval6 [Hbound6 Hsep6]]]]].
      subst rets6. symmetry in Htr6. subst t6.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* --- Call 7: from_word(out.c1.c0 fst, 0) --- *)
      repeat straightline.
      eassert (Hsep6_split7 :
        (FElem_Fp2 (word.add pout (word.of_Z fp6_felem_offset))
           (c0_felem (d1_felem old_out)) ⋆ _) m6').
      { pose proof Hsep6 as H'. ecancel_assumption. }
      apply FElem_Fp2_split_in_sep in Hsep6_split7.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (fst_felem (c0_felem (d1_felem old_out))) _ tr).
           exact Hsep6_split7. }
      intros t7 m7' rets7 [Hrets7 [Htr7 [fw7 [Hfeval7 [Hbound7 Hsep7]]]]].
      subst rets7. symmetry in Htr7. subst t7.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* --- Call 8: from_word(out.c1.c0 snd, 0) --- *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (snd_felem (c0_felem (d1_felem old_out))) _ tr).
           (* Address normalization: change goal address to match hypothesis form *)
           match goal with
           | |- (?P ⋆ ?Q) ?m =>
             change ((FElem_Fp
               (word.add (word.add pout (word.of_Z fp6_felem_offset)) (word.of_Z fp_felem_offset))
               (snd_felem (c0_felem (d1_felem old_out))) ⋆ Q) m)
           end.
           pose proof Hsep7 as H'. ecancel_assumption. }
      intros t8 m8' rets8 [Hrets8 [Htr8 [fw8 [Hfeval8 [Hbound8 Hsep8]]]]].
      subst rets8. symmetry in Htr8. subst t8.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* --- Call 9: fp_copy(out.c1.c1 fst, y_p) --- *)
      repeat straightline.
      eassert (Hsep8_split9 :
        (FElem_Fp2 (word.add (word.add pout (word.of_Z fp6_felem_offset)) fp6_c1_off)
           (c1_felem (d1_felem old_out)) ⋆ _) m8').
      { pose proof Hsep8 as H'. ecancel_assumption. }
      apply FElem_Fp2_split_in_sep in Hsep8_split9.
      (* fp_copy spec: (FElem px x * FElem pout out * R) mem /\ (FElem pout out * Rout) mem
         Here: px = pyp, x = yp, pout = d1.c1.fst addr,
               out = fst_felem (c1_felem (d1_felem old_out)) *)
      eapply Semantics.weaken_call.
      1: { eapply (HFpcopy _ _
             (fst_felem (c1_felem (d1_felem old_out))) yp _ _ tr).
           (* change goal pout address to match the Fp2-split address *)
           match goal with
           | |- (_ /\ _) =>
             split; [|
               match goal with
               | |- (?P ⋆ ?Q) ?m =>
                 change ((FElem_Fp
                   (word.add (word.add pout (word.of_Z fp6_felem_offset)) fp6_c1_off)
                   (fst_felem (c1_felem (d1_felem old_out))) ⋆ Q) m)
               end;
               pose proof Hsep8_split9 as H'; ecancel_assumption]
           end.
           match goal with
           | |- (_ ⋆ _ ⋆ ?Q) ?m =>
             change ((FElem_Fp pyp yp ⋆
                      FElem_Fp (word.add (word.add pout (word.of_Z fp6_felem_offset)) fp6_c1_off)
                        (fst_felem (c1_felem (d1_felem old_out))) ⋆ Q) m)
           end.
           pose proof Hsep8_split9 as H'. ecancel_assumption. }
      intros t9 m9' rets9 [Hrets9 [Htr9 Hsep9]].
      subst rets9. symmetry in Htr9. subst t9.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* --- Call 10: from_word(out.c1.c1 snd, 0) --- *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (snd_felem (c1_felem (d1_felem old_out))) _ tr).
           (* Address normalization: straightline computed addr vs opaque fp6_c1_off form *)
           match goal with
           | |- (?P ⋆ ?Q) ?m =>
             change ((FElem_Fp
               (word.add (word.add (word.add pout (word.of_Z fp6_felem_offset)) fp6_c1_off)
                  (word.of_Z fp_felem_offset))
               (snd_felem (c1_felem (d1_felem old_out))) ⋆ Q) m)
           end.
           pose proof Hsep9 as H'. ecancel_assumption. }
      intros t10 m10' rets10 [Hrets10 [Htr10 [fw10 [Hfeval10 [Hbound10 Hsep10]]]]].
      subst rets10. symmetry in Htr10. subst t10.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* --- Call 11: from_word(out.c1.c2 fst, 0) --- *)
      repeat straightline.
      eassert (Hsep10_split11 :
        (FElem_Fp2 (word.add (word.add pout (word.of_Z fp6_felem_offset)) fp6_c2_off)
           (c2_felem (d1_felem old_out)) ⋆ _) m10').
      { pose proof Hsep10 as H'. ecancel_assumption. }
      apply FElem_Fp2_split_in_sep in Hsep10_split11.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (fst_felem (c2_felem (d1_felem old_out))) _ tr).
           (* change fst-half address to match Fp2-split form *)
           match goal with
           | |- (?P ⋆ ?Q) ?m =>
             change ((FElem_Fp
               (word.add (word.add pout (word.of_Z fp6_felem_offset)) fp6_c2_off)
               (fst_felem (c2_felem (d1_felem old_out))) ⋆ Q) m)
           end.
           exact Hsep10_split11. }
      intros t11 m11' rets11 [Hrets11 [Htr11 [fw11 [Hfeval11 [Hbound11 Hsep11]]]]].
      subst rets11. symmetry in Htr11. subst t11.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* --- Call 12: from_word(out.c1.c2 snd, 0) --- *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (snd_felem (c2_felem (d1_felem old_out))) _ tr).
           (* Address normalization for snd half of d1.c2 *)
           match goal with
           | |- (?P ⋆ ?Q) ?m =>
             change ((FElem_Fp
               (word.add (word.add (word.add pout (word.of_Z fp6_felem_offset)) fp6_c2_off)
                  (word.of_Z fp_felem_offset))
               (snd_felem (c2_felem (d1_felem old_out))) ⋆ Q) m)
           end.
           pose proof Hsep11 as H'. ecancel_assumption. }
      intros t12 m12' rets12 [Hrets12 [Htr12 [fw12 [Hfeval12 [Hbound12 Hsep12]]]]].
      subst rets12. symmetry in Htr12. subst t12.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* === Stack deallocation + final postcondition === *)
      (* The goal here is the stackalloc deallocation:
         we must provide anybytes for a_tmp and map.split,
         then prove the postcondition on the remaining memory.

         Step 1: Extract tmp FElem from sep and convert to anybytes.
         Step 2: Prove map.split.
         Step 3: Join Fp halves into Fp2, then Fp6, then Fp12.
         Step 4: Prove bounded_by loose.
      *)

      (* Handle remaining cmd.skip from cmd_seq_list *)
      repeat straightline.

      (* The stackalloc WP continuation needs:
         exists mSmall mStack',
           anybytes a_tmp <size> mStack' /\
           map.split m12' mSmall mStack' /\
           postcondition tr mSmall *)
      (* === Stack deallocation + final postcondition ===

         The goal here is the stackalloc deallocation continuation:
           exists mSmall mStack',
             anybytes a_tmp <size> mStack' /\
             map.split mFinal mSmall mStack' /\
             (rets = [] /\ tr = tr' /\
              exists out, Fp12_bounded loose out /\ (FElem_Fp12 pout out * ...) mSmall)

         To close this, one would need to:

         Step 1: Extract the FElem_Fp2 at a_tmp from the sep hypothesis.
           Use ecancel to isolate (FElem_Fp2 a_tmp tmp_val * rest) on the
           final memory. Then apply FElem_to_bytes to convert tmp's FElem
           to anybytes (Placeholder), giving anybytes a_tmp size mStack'.

         Step 2: Provide the map.split witness.
           After extracting mStack' for a_tmp, the remaining memory mSmall
           contains the 12 output Fp-level FElems + input FElems + Rr.
           Prove map.split mFinal mSmall mStack' from the sep structure.

         Step 3: Join 12 Fp output FElems into Fp12.
           - Pair Fp halves into 6 Fp2 via FElem_Fp_join_in_sep
           - Group 3 pairs of Fp2 into 2 Fp6 via Fp6_raw_FElem_join
           - Group 2 Fp6 into Fp12 via Fp12_raw_FElem_join

         Step 4: Prove bounded_by loose.
           The Fp2 sub-call specs guarantee tight or loose bounds on
           each component. Use relax_bounds where needed to obtain
           loose bounds at the Fp12 level.

         Step 5: Build the final sep.
           After joining, have FElem_Fp12 pout out. Combine with the
           surviving input FElems and Rr via ecancel.

         This is approximately 100 lines of proof script. *)
      (* --- Stack dealloc: a_tmp (Fp2-sized) --- *)
      eassert (Htmp_sep : (FElem_Fp2 a_tmp out3 ⋆ _) m12').
      { pose proof Hsep12 as H'. ecancel_assumption. }
      destruct Htmp_sep as [m_stk [m_rest [[Heq_stk Hd_stk] [Hftmp Hrest]]]].
      exists m_rest, m_stk.
      split. { exact (AbstractField.FElem_to_bytes a_tmp out3 m_stk Hftmp). }
      split. { split. { rewrite map.putmany_comm; [exact Heq_stk | exact (proj1 (map.disjoint_comm _ _) Hd_stk)]. } { exact (proj1 (map.disjoint_comm _ _) Hd_stk). } }

      (* Handle return value list *)
      cbv [list_map list_map_body].
      split. { exact eq_refl. }
      split. { exact eq_refl. }

      (* === Step 3: Join 12 Fp-level entries into Fp12 ===

         Hrest has on m_rest:
           8 FElem_Fp (fw5..fw12, yp copy)
           + 2 FElem_Fp2 (out2 @ pout, out4 @ pout+fp6_c1_off)
           + surviving inputs (lam, xt, yt, xp, yp)
           + Rr

         Join strategy:
         a) Pair Fp halves into 4 Fp2: d0.c2, d1.c0, d1.c1, d1.c2
         b) Join 3 Fp2 into Fp6: d0 (out2, out4, d0.c2), d1 (d1.c0, d1.c1, d1.c2)
         c) Join 2 Fp6 into Fp12
      *)

      (* --- Extract Fp-level lengths from FElem predicates --- *)
      pose proof fun p v m (H : FElem_Fp p v m) =>
        @QuadraticFieldExtensions.AbstractFElem_length _ _ _ _
          bls12_pf_params bls12_Fp_rep p v m H
        as FpLen.
      (* Extract each length by pulling the FElem from the current sep *)
      assert (Hlen_fw5 : length fw5 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw5 ⋆ _) m_rest) by
          (pose proof Hrest as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw6 : length fw6 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw6 ⋆ _) m_rest) by
          (pose proof Hrest as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw7 : length fw7 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw7 ⋆ _) m_rest) by
          (pose proof Hrest as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw8 : length fw8 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw8 ⋆ _) m_rest) by
          (pose proof Hrest as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_yp_copy : length yp = Fp_fsw).
      { assert (Htmp : (FElem_Fp pyp yp ⋆ _) m_rest) by
          (pose proof Hrest as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw10 : length fw10 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw10 ⋆ _) m_rest) by
          (pose proof Hrest as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw11 : length fw11 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw11 ⋆ _) m_rest) by
          (pose proof Hrest as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw12 : length fw12 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw12 ⋆ _) m_rest) by
          (pose proof Hrest as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      clear FpLen.

      (* --- Chain-join: combine Fp pairs into Fp2, chaining through the sep --- *)
      (* Join d0.c2: fw5 (fst) + fw6 (snd) — start from Hrest *)
      eassert (Hsep_a : (FElem_Fp _ fw5 ⋆ (FElem_Fp _ fw6 ⋆ _)) m_rest).
      { pose proof Hrest as H'. ecancel_assumption. }
      change (word.add pout (word.of_Z (2 * (Memory.bytes_per_word 64 * Z.of_nat Fp_fsw))))
        with (word.add pout fp6_c2_off) in Hsep_a.
      change (word.add (word.add pout fp6_c2_off) (word.of_Z (Memory.bytes_per_word 64 * Z.of_nat Fp_fsw)))
        with (word.add (word.add pout fp6_c2_off) (word.of_Z fp_felem_offset)) in Hsep_a.
      apply FElem_Fp_join_in_sep in Hsep_a; [| exact Hlen_fw5 | exact Hlen_fw6].

      (* Join d1.c0: fw7 + fw8 — chain from Hsep_a *)
      eassert (Hsep_b : (FElem_Fp _ fw7 ⋆ (FElem_Fp _ fw8 ⋆ _)) m_rest).
      { pose proof Hsep_a as H'. ecancel_assumption. }
      eassert (Hsep_b' : (FElem_Fp _ fw7 ⋆ (FElem_Fp (word.add _ (word.of_Z fp_felem_offset)) fw8 ⋆ _)) m_rest).
      { exact Hsep_b. }
      apply FElem_Fp_join_in_sep in Hsep_b'; [| exact Hlen_fw7 | exact Hlen_fw8].

      (* Join d1.c1: yp + fw10 — chain from Hsep_b' *)
      eassert (Hsep_c : (FElem_Fp _ yp ⋆ (FElem_Fp _ fw10 ⋆ _)) m_rest).
      { pose proof Hsep_b' as H'. ecancel_assumption. }
      eassert (Hsep_c' : (FElem_Fp _ yp ⋆ (FElem_Fp (word.add _ (word.of_Z fp_felem_offset)) fw10 ⋆ _)) m_rest).
      { exact Hsep_c. }
      apply FElem_Fp_join_in_sep in Hsep_c'; [| exact Hlen_yp_copy | exact Hlen_fw10].

      (* Join d1.c2: fw11 + fw12 — chain from Hsep_c' *)
      eassert (Hsep_d : (FElem_Fp _ fw11 ⋆ (FElem_Fp _ fw12 ⋆ _)) m_rest).
      { pose proof Hsep_c' as H'. ecancel_assumption. }
      eassert (Hsep_d' : (FElem_Fp _ fw11 ⋆ (FElem_Fp (word.add _ (word.of_Z fp_felem_offset)) fw12 ⋆ _)) m_rest).
      { exact Hsep_d. }
      apply FElem_Fp_join_in_sep in Hsep_d'; [| exact Hlen_fw11 | exact Hlen_fw12].
      (* Hsep_d' now has all 6 Fp2 values (no loose Fp entries) on m_rest *)

      (* === Step 3b: Rearrange into d0, d1, inputs order === *)
      eassert (Hsep_rearr :
        (FElem_Fp2 _ out2 ⋆
         (FElem_Fp2 _ out4 ⋆
          (FElem_Fp2 _ (fw5 ++ fw6) ⋆
           (FElem_Fp2 _ (fw7 ++ fw8) ⋆
            (FElem_Fp2 _ (yp ++ fw10) ⋆
             (FElem_Fp2 _ (fw11 ++ fw12) ⋆
              (FElem_Fp2 _ lam ⋆
               (FElem_Fp2 _ xt ⋆
                (FElem_Fp2 _ yt ⋆
                 (FElem_Fp _ xp ⋆
                  (FElem_Fp _ yp ⋆ Rr))))))))))) m_rest).
      { pose proof Hsep_d' as H'. ecancel_assumption. }

      (* Destructure to get d0 and d1 sub-memories *)
      destruct Hsep_rearr as [m_oc0 [m_r1 [[Heq_r1 Hd_r1] [Hoc0 Hr1]]]].
      destruct Hr1 as [m_oc1 [m_r2 [[Heq_r2 Hd_r2] [Hoc1 Hr2]]]].
      destruct Hr2 as [m_oc2 [m_r3 [[Heq_r3 Hd_r3] [Hoc2 Hr3]]]].
      destruct Hr3 as [m_d1c0m [m_r4 [[Heq_r4 Hd_r4] [Hd1c0m Hr4]]]].
      destruct Hr4 as [m_d1c1m [m_r5 [[Heq_r5 Hd_r5] [Hd1c1m Hr5]]]].
      destruct Hr5 as [m_d1c2m [m_inputs [[Heq_r6 Hd_r6] [Hd1c2m Hinputs]]]].
      subst.

      (* Build disjointness facts *)
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_r1) as [Hd_01 Hd_0r2].
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_0r2) as [Hd_02 Hd_0r3].
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_r2) as [Hd_12 Hd_1r3].
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_r3) as [Hd_23 Hd_2r4].
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_1r3) as [Hd_13 Hd_1r4].
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_r4) as [Hd_34 Hd_3r5].
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_r5) as [Hd_45 Hd_4inp].
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_3r5) as [Hd_35 Hd_3inp].
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_2r4) as [Hd_24 Hd_2r5].
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_2r5) as [Hd_25 Hd_2inp].
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_1r4) as [Hd_14 Hd_1r5].
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_1r5) as [Hd_15 Hd_1inp].
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_0r3) as [Hd_03 Hd_0r4].
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_0r4) as [Hd_04 Hd_0r5].
      pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_0r5) as [Hd_05 Hd_0inp].

      (* === Build Fp6 for d0 === *)
      assert (Hsep_d0_fp6 : (FElem_Fp2 pout out2 ⋆
        (FElem_Fp2 (word.add pout fp6_c1_off) out4 ⋆
         FElem_Fp2 (word.add pout fp6_c2_off) (fw5 ++ fw6)))
        (map.putmany m_oc0 (map.putmany m_oc1 m_oc2))).
      { exists m_oc0, (map.putmany m_oc1 m_oc2).
        split; [split; [reflexivity | apply map.disjoint_putmany_r; split; [exact Hd_01 | exact Hd_02]] |].
        split; [exact Hoc0 |].
        exists m_oc1, m_oc2.
        split; [split; [reflexivity | exact Hd_12] |].
        split; [exact Hoc1 | exact Hoc2]. }
      Local Notation Fp2_felem_size := (@AbstractField.felem_size_in_words _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
      assert (Hlen_out2_fp2 : length out2 = Fp2_felem_size).
      { (* FElem = Bignum n, which stores length = n in its predicate *)
        unfold AbstractField.FElem, Bignum.Bignum in Hoc0.
        destruct Hoc0 as [me [ma [_ [[_ Hlen] _]]]]. exact Hlen. }
      assert (Hlen_out4_fp2 : length out4 = Fp2_felem_size).
      { unfold AbstractField.FElem, Bignum.Bignum in Hoc1.
        destruct Hoc1 as [me [ma [_ [[_ Hlen] _]]]]. exact Hlen. }
      assert (Hlen_d0c2_fp2 : length (fw5 ++ fw6) = Fp2_felem_size).
      { rewrite length_app, Hlen_fw5, Hlen_fw6. reflexivity. }
      pose proof (@CubicFieldExtensions.Fp6_raw_FElem_join _ _ _ _
        wordok mapok bls12_pf_params bls12_beta bls12_xi_re bls12_xi_im bls12_Fp_rep fp6_prefix fp2_prefix
        pout out2 out4 (fw5 ++ fw6) _ Hlen_out2_fp2 Hlen_out4_fp2 Hlen_d0c2_fp2 Hsep_d0_fp6)
        as Hfe_d0.

      (* === Build Fp6 for d1 === *)
      assert (Hlen_d1c0_fp2 : length (fw7 ++ fw8) = Fp2_felem_size).
      { rewrite length_app, Hlen_fw7, Hlen_fw8. reflexivity. }
      assert (Hlen_d1c1_fp2 : length (yp ++ fw10) = Fp2_felem_size).
      { rewrite length_app, Hlen_yp_copy, Hlen_fw10. reflexivity. }
      assert (Hlen_d1c2_fp2 : length (fw11 ++ fw12) = Fp2_felem_size).
      { rewrite length_app, Hlen_fw11, Hlen_fw12. reflexivity. }
      (* Need sep: (FElem_Fp2 base (fw7++fw8) * (FElem_Fp2 (base+c1) (yp++fw10) *
                     FElem_Fp2 (base+c2) (fw11++fw12))) m_d1 *)
      (* But the addresses for d1 Fp2s use (pout+fp6_off+X) while Fp6_raw_FElem_join
         expects base and (base+fp6_c1_offset) and (base+fp6_c2_offset).
         For d1, base = pout+fp6_felem_offset.
         The addresses for d1.c1 and d1.c2 from the rearranged sep use
         evar-unified addresses. We need to change them to
         (word.add base fp6_c1_off) and (word.add base fp6_c2_off). *)
      eassert (Hsep_d1_fp6 : (FElem_Fp2 _ (fw7 ++ fw8) ⋆
        (FElem_Fp2 (word.add _ fp6_c1_off) (yp ++ fw10) ⋆
         FElem_Fp2 (word.add _ fp6_c2_off) (fw11 ++ fw12)))
        (map.putmany m_d1c0m (map.putmany m_d1c1m m_d1c2m))).
      { exists m_d1c0m, (map.putmany m_d1c1m m_d1c2m).
        split; [split; [reflexivity | apply map.disjoint_putmany_r; split; [exact Hd_34 | exact Hd_35]] |].
        split; [exact Hd1c0m |].
        exists m_d1c1m, m_d1c2m.
        split; [split; [reflexivity | exact Hd_45] |].
        split; [exact Hd1c1m | exact Hd1c2m]. }
      pose proof (@CubicFieldExtensions.Fp6_raw_FElem_join _ _ _ _
        wordok mapok bls12_pf_params bls12_beta bls12_xi_re bls12_xi_im bls12_Fp_rep fp6_prefix fp2_prefix
        _ (fw7 ++ fw8) (yp ++ fw10) (fw11 ++ fw12) _ Hlen_d1c0_fp2 Hlen_d1c1_fp2 Hlen_d1c2_fp2 Hsep_d1_fp6)
        as Hfe_d1.

      (* === Build Fp12: join d0 and d1 === *)
      assert (Hlen_d0_fp6 : length (out2 ++ out4 ++ (fw5 ++ fw6)) = Fp6_fsw).
      { rewrite !length_app, Hlen_out2_fp2, Hlen_out4_fp2, Hlen_fw5, Hlen_fw6.
        reflexivity. }
      assert (Hlen_d1_fp6 : length ((fw7 ++ fw8) ++ (yp ++ fw10) ++ (fw11 ++ fw12)) = Fp6_fsw).
      { rewrite !length_app, Hlen_fw7, Hlen_fw8, Hlen_yp_copy, Hlen_fw10, Hlen_fw11, Hlen_fw12.
        reflexivity. }
      set (m_fp12 := map.putmany (map.putmany m_oc0 (map.putmany m_oc1 m_oc2))
                                  (map.putmany m_d1c0m (map.putmany m_d1c1m m_d1c2m))).
      assert (Hsep_fp12 : (FElem_Fp6 pout (out2 ++ out4 ++ (fw5 ++ fw6)) ⋆
        FElem_Fp6 (word.add pout (word.of_Z fp6_felem_offset))
          ((fw7 ++ fw8) ++ (yp ++ fw10) ++ (fw11 ++ fw12))) m_fp12).
      { subst m_fp12. exists (map.putmany m_oc0 (map.putmany m_oc1 m_oc2)),
          (map.putmany m_d1c0m (map.putmany m_d1c1m m_d1c2m)).
        split; [split; [reflexivity |] |].
        { apply map.disjoint_putmany_l. split.
          { apply map.disjoint_putmany_r. split; [exact Hd_03 | apply map.disjoint_putmany_r; split; [exact Hd_04 | exact Hd_05]]. }
          { apply map.disjoint_putmany_l. split.
            { apply map.disjoint_putmany_r. split; [exact Hd_13 | apply map.disjoint_putmany_r; split; [exact Hd_14 | exact Hd_15]]. }
            { apply map.disjoint_putmany_r. split; [exact Hd_23 | apply map.disjoint_putmany_r; split; [exact Hd_24 | exact Hd_25]]. } } }
        split; [exact Hfe_d0 | exact Hfe_d1]. }
      pose proof (@DodecicFieldExtensions.Fp12_raw_FElem_join _ _ _ _
        wordok mapok bls12_pf_params bls12_Fp_rep bls12_beta bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix
        pout (out2 ++ out4 ++ (fw5 ++ fw6))
        ((fw7 ++ fw8) ++ (yp ++ fw10) ++ (fw11 ++ fw12)) m_fp12
        Hlen_d0_fp6 Hlen_d1_fp6 Hsep_fp12)
        as Hfe_fp12.
      (* Hfe_fp12 : FElem_Fp12 pout <big_concat> m_fp12 *)

      (* === Step 4: Provide the existential witness and prove bounded === *)
      set (the_out := (out2 ++ out4 ++ (fw5 ++ fw6)) ++
                       ((fw7 ++ fw8) ++ (yp ++ fw10) ++ (fw11 ++ fw12))).
      exists the_out.
      split.
      { (* FEVAL *)
        exact (make_line_feval_final lam xt yt out1 out2 out3 out4
                 xp yp fw5 fw6 fw7 fw8 fw10 fw11 fw12
                 Hlen_out2_fp2 Hlen_out4_fp2 Hlen_fw5 Hlen_fw6 Hlen_fw7 Hlen_fw8
                 Hlen_yp_copy Hlen_fw10 Hlen_fw11
                 Hfeval1 Hfeval2 Hfeval3 Hfeval4 Hfeval5 Hfeval6 Hfeval7 Hfeval8
                 Hfeval10 Hfeval11 Hfeval12). }
      split.
      { (* bounded_by loose_bounds the_out *)
        subst the_out.
        (* Decompose Fp2 bounds into Fp bounds *)
        pose proof Hbound2 as Hb2.
        pose proof Hbound4 as Hb4.
        unfold Fp2_bounded, AbstractField.bounded_by,
               bls12_Fp2_rep', bls12_Fp2_params',
               QuadraticFieldExtensionsSpecs.Fp2_field_representation in Hb2, Hb4.
        cbv beta in Hb2, Hb4.
        destruct Hb2 as [Hb2a Hb2b]. destruct Hb4 as [Hb4a Hb4b].
        (* relax all tight to loose *)
        pose proof (@AbstractField.relax_bounds _ _ _ _ _ _
          bls12_Fp_rep bls12_Fp_rep_ok) as RB.
        (* Build Fp2-level loose bounds for joined pairs *)
        Local Ltac mk_fp2_loose Hfa Hfb Hlen :=
          unfold Fp2_bounded, AbstractField.bounded_by,
                 bls12_Fp2_rep', bls12_Fp2_params',
                 QuadraticFieldExtensionsSpecs.Fp2_field_representation;
          cbv beta;
          unfold QuadraticFieldExtensionsSpecs.fst_felem,
                 QuadraticFieldExtensionsSpecs.snd_felem;
          rewrite firstn_app' by exact Hlen;
          rewrite QuadraticFieldExtensions.skipn_app by exact Hlen;
          exact (conj Hfa Hfb).
        assert (Hb_d0c2 : Fp2_bounded Fp2_loose (fw5 ++ fw6))
          by (mk_fp2_loose (RB _ Hbound5) (RB _ Hbound6) Hlen_fw5).
        assert (Hb_d1c0 : Fp2_bounded Fp2_loose (fw7 ++ fw8))
          by (mk_fp2_loose (RB _ Hbound7) (RB _ Hbound8) Hlen_fw7).
        assert (Hb_d1c1 : Fp2_bounded Fp2_loose (yp ++ fw10))
          by (mk_fp2_loose Hbyp (RB _ Hbound10) Hlen_yp_copy).
        assert (Hb_d1c2 : Fp2_bounded Fp2_loose (fw11 ++ fw12))
          by (mk_fp2_loose (RB _ Hbound11) (RB _ Hbound12) Hlen_fw11).
        assert (Hb_out2_l : Fp2_bounded Fp2_loose out2).
        { unfold Fp2_bounded, AbstractField.bounded_by,
                 bls12_Fp2_rep', bls12_Fp2_params',
                 QuadraticFieldExtensionsSpecs.Fp2_field_representation.
          cbv beta. exact (conj (RB _ Hb2a) (RB _ Hb2b)). }
        assert (Hb_out4_l : Fp2_bounded Fp2_loose out4).
        { unfold Fp2_bounded, AbstractField.bounded_by,
                 bls12_Fp2_rep', bls12_Fp2_params',
                 QuadraticFieldExtensionsSpecs.Fp2_field_representation.
          cbv beta. exact (conj (RB _ Hb4a) (RB _ Hb4b)). }
        (* Build Fp6 bounds *)
        (* Lift tight to loose at the Fp level ([relax_bounds] of the Fp representation) and
           assemble the Fp6 / Fp12 bounds through the representation structure, with the
           instances made transparent locally. *)
        Local Typeclasses Transparent bls12_Fp12_params'.
        Local Typeclasses Transparent bls12_Fp12_rep'.
        Local Typeclasses Transparent bls12_Fp6_params'.
        Local Typeclasses Transparent bls12_Fp6_rep'.
        Local Typeclasses Transparent bls12_Fp2_params'.
        Local Typeclasses Transparent bls12_Fp2_rep'.
        cbv [AbstractField.bounded_by AbstractField.loose_bounds
             bls12_Fp12_rep' bls12_Fp12_params'
             bls12_Fp6_rep' bls12_Fp6_params'
             bls12_Fp2_rep' bls12_Fp2_params'
             bls12_beta bls12_xi_re bls12_xi_im
             DodecicFieldExtensionsSpecs.Fp12_field_representation
             DodecicFieldExtensionsSpecs.Fp12_field_parameters
             DodecicFieldExtensionsSpecs.d0_felem
             DodecicFieldExtensionsSpecs.d1_felem
             CubicFieldExtensionsSpecs.Fp6_field_representation
             CubicFieldExtensionsSpecs.Fp6_field_parameters
             CubicFieldExtensionsSpecs.c0_felem
             CubicFieldExtensionsSpecs.c1_felem
             CubicFieldExtensionsSpecs.c2_felem
             QuadraticFieldExtensionsSpecs.Fp2_field_representation
             QuadraticFieldExtensionsSpecs.Fp2_field_parameters
             QuadraticFieldExtensionsSpecs.fst_felem
             QuadraticFieldExtensionsSpecs.snd_felem].
        cbv beta.
        (* firstn/skipn simplification.
           The key insight: after cbv, all sizes are in terms of Fp_fsw.
           Fp2_fsw = 2*Fp_fsw, Fp6_fsw = 3*(2*Fp_fsw) = 6*Fp_fsw, Fp12_fsw = 12*Fp_fsw.
           Build all needed length equalities with the correct numeric form. *)
        assert (Hlen_d0_num : length (out2 ++ out4 ++ fw5 ++ fw6) = (3 * (2 * Fp_fsw))%nat).
        { rewrite !length_app. rewrite Hlen_fw5, Hlen_fw6.
          unfold AbstractField.FElem, Bignum.Bignum in Hoc0, Hoc1.
          destruct Hoc0 as [? [? [_ [[_ Hl0] _]]]].
          destruct Hoc1 as [? [? [_ [[_ Hl1] _]]]].
          rewrite Hl0, Hl1. reflexivity. }
        (* firstn at Fp12 level: extract d0 *)
        rewrite (firstn_app' _ _ _ Hlen_d0_num).
        rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Hlen_d0_num).
        (* Build Fp2 length hypotheses compatible with the unfolded form *)
        assert (Hlen_out2_num : length out2 = (2 * Fp_fsw)%nat).
        { unfold AbstractField.FElem, Bignum.Bignum in Hoc0.
          destruct Hoc0 as [? [? [_ [[_ Hl] _]]]]. exact Hl. }
        assert (Hlen_out4_num : length out4 = (2 * Fp_fsw)%nat).
        { unfold AbstractField.FElem, Bignum.Bignum in Hoc1.
          destruct Hoc1 as [? [? [_ [[_ Hl] _]]]]. exact Hl. }
        (* The Fp6 bounded_by from DodecicFieldExtensions didn't fully unfold.
           Split the conjunction and handle each Fp6 half. *)
        split.
        (* d0 bound *)
        { change (DodecicFieldExtensionsSpecs.Fp6_repr_inst bls12_beta bls12_xi_re bls12_xi_im) with bls12_Fp6_rep'.
          unfold AbstractField.bounded_by, AbstractField.loose_bounds,
                 bls12_Fp6_rep', bls12_Fp6_params',
                 CubicFieldExtensionsSpecs.Fp6_field_representation,
                 CubicFieldExtensionsSpecs.Fp6_field_parameters,
                 CubicFieldExtensionsSpecs.c0_felem,
                 CubicFieldExtensionsSpecs.c1_felem,
                 CubicFieldExtensionsSpecs.c2_felem.
          cbv beta.
          (* Solve each Fp6 bounded goal by unfolding to Fp2 *)
          cbv [DodecicFieldExtensionsSpecs.Fp6_repr_inst bls12_beta bls12_xi_re bls12_xi_im
               CubicFieldExtensionsSpecs.Fp6_field_representation
               CubicFieldExtensionsSpecs.Fp6_field_parameters
               CubicFieldExtensionsSpecs.c0_felem
               CubicFieldExtensionsSpecs.c1_felem
               CubicFieldExtensionsSpecs.c2_felem
               AbstractField.bounded_by AbstractField.loose_bounds].
          cbv beta.
          rewrite (firstn_app' _ _ _ Hlen_out2_num).
          rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Hlen_out2_num).
          (* For c1: firstn uses Fp2_fsw from the Fp6 context which may differ from
             Hlen_out4_num's 2*Fp_fsw. Use eassert to match the exact form. *)
          match goal with |- context [firstn ?n (out4 ++ _)] =>
            assert (Hlen_out4_c1 : length out4 = n) by exact Hlen_out4_num
          end.
          rewrite (firstn_app' _ _ _ Hlen_out4_c1).
          (* c2: skipn (2*(2*Fp_fsw)) (out2 ++ out4 ++ fw5 ++ fw6) = fw5 ++ fw6 *)
          assert (Hlen_out2_out4 : length (out2 ++ out4) = (2 * (2 * Fp_fsw))%nat).
          { rewrite length_app, Hlen_out2_num, Hlen_out4_num. reflexivity. }
          rewrite (app_assoc out2 out4).
          rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Hlen_out2_out4).
          exact (conj Hb_out2_l (conj Hb_out4_l Hb_d0c2)). }
        (* d1 bound *)
        { cbv [DodecicFieldExtensionsSpecs.Fp6_repr_inst bls12_beta bls12_xi_re bls12_xi_im
               CubicFieldExtensionsSpecs.Fp6_field_representation
               CubicFieldExtensionsSpecs.Fp6_field_parameters
               CubicFieldExtensionsSpecs.c0_felem
               CubicFieldExtensionsSpecs.c1_felem
               CubicFieldExtensionsSpecs.c2_felem
               AbstractField.bounded_by AbstractField.loose_bounds].
          cbv beta.
          assert (Hlen_d1c0_inner : length (fw7 ++ fw8) = (2 * Fp_fsw)%nat).
          { rewrite length_app, Hlen_fw7, Hlen_fw8. reflexivity. }
          assert (Hlen_yp_fw10 : length (yp ++ fw10) = (2 * Fp_fsw)%nat).
          { rewrite length_app, Hlen_yp_copy, Hlen_fw10. reflexivity. }
          rewrite (firstn_app' _ _ _ Hlen_d1c0_inner).
          rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Hlen_d1c0_inner).
          match goal with |- context [firstn ?n ((yp ++ fw10) ++ _)] =>
            assert (Hlen_yp_fw10_c1 : length (yp ++ fw10) = n) by
              (rewrite length_app, Hlen_yp_copy, Hlen_fw10; reflexivity)
          end.
          rewrite (firstn_app' _ _ _ Hlen_yp_fw10_c1).
          (* c2: skipn (2*Fp2_fsw) ((fw7++fw8) ++ (yp++fw10) ++ fw11 ++ fw12) *)
          assert (Hlen_d1_c0c1 : length ((fw7 ++ fw8) ++ (yp ++ fw10)) = (2 * (2 * Fp_fsw))%nat).
          { rewrite !length_app, Hlen_fw7, Hlen_fw8, Hlen_yp_copy, Hlen_fw10. reflexivity. }
          rewrite (app_assoc (fw7 ++ fw8) (yp ++ fw10)).
          rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Hlen_d1_c0c1).
          exact (conj Hb_d1c0 (conj Hb_d1c1 Hb_d1c2)). } }
      { (* (FElem_Fp12 pout the_out ⋆ inputs) m_rest *)
        subst m_fp12. subst the_out.
        exists (map.putmany (map.putmany m_oc0 (map.putmany m_oc1 m_oc2))
                            (map.putmany m_d1c0m (map.putmany m_d1c1m m_d1c2m))),
               m_inputs.
        split; [split |].
        { rewrite ?map.putmany_assoc. reflexivity. }
        { apply map.disjoint_putmany_l. split.
          { apply map.disjoint_putmany_l. split.
            { exact Hd_0inp. }
            { apply map.disjoint_putmany_l. split; [exact Hd_1inp | exact Hd_2inp]. } }
          { apply map.disjoint_putmany_l. split.
            { exact Hd_3inp. }
            { apply map.disjoint_putmany_l. split; [exact Hd_4inp | exact Hd_r6]. } } }
        split; [exact Hfe_fp12 | exact Hinputs]. }
    Qed.


    (** The post stated with [Pairing.make_line] directly. *)
    Lemma bls12_make_line_pairing_ok :
      forall functions
        (EnvContains : map.get functions "bls12_make_line" =
          Some (snd bls12_make_line))
        (HFp2mul : spec_of_Fp2_mul functions)
        (HFp2sub : spec_of_Fp2_sub functions)
        (HFp2opp : spec_of_Fp2_opp functions)
        (HFp2mulfp : spec_of_bls12_Fp2_mul_fp functions)
        (HFpcopy : spec_of_Fp_felem_copy functions)
        (HFfromword : spec_of_Fp_from_word functions),
      forall pout plam pxt pyt pxp pyp
        (old_out : Fp12_felem)
        (lam xt yt : Fp2_felem) (xp yp : Fp_felem) Rr tr mem,
        Fp2_bounded Fp2_tight lam /\
        Fp2_bounded Fp2_tight xt /\
        Fp2_bounded Fp2_tight yt /\
        Fp_bounded Fp_loose xp /\
        Fp_bounded Fp_loose yp /\
        (FElem_Fp12 pout old_out ⋆
         (FElem_Fp2 plam lam ⋆
          (FElem_Fp2 pxt xt ⋆
           (FElem_Fp2 pyt yt ⋆
            (FElem_Fp pxp xp ⋆
             (FElem_Fp pyp yp ⋆ Rr)))))) mem ->
        WeakestPrecondition.call functions "bls12_make_line" tr mem
          [pout; plam; pxt; pyt; pxp; pyp]
          (fun tr' mem' rets =>
            rets = [] /\ tr = tr' /\
            exists out,
              Fp12_feval out =
                Pairing.make_line PrimeField.M_pos (Fp2_feval lam) (Fp2_feval xt) (Fp2_feval yt)
                  (Fp_feval xp) (Fp_feval yp) /\
              @AbstractField.bounded_by _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep'
                (@AbstractField.loose_bounds _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep') out /\
              (FElem_Fp12 pout out ⋆
               (FElem_Fp2 plam lam ⋆
                (FElem_Fp2 pxt xt ⋆
                 (FElem_Fp2 pyt yt ⋆
                  (FElem_Fp pxp xp ⋆
                   (FElem_Fp pyp yp ⋆ Rr)))))) mem').
    Proof.
      intros functions EnvContains HFp2mul HFp2sub HFp2opp HFp2mulfp HFpcopy HFfromword
        pout plam pxt pyt pxp pyp old_out lam xt yt xp yp Rr tr mem0 Hpre.
      eapply Semantics.weaken_call.
      { exact (bls12_make_line_functional_ok functions EnvContains HFp2mul HFp2sub HFp2opp
                 HFp2mulfp HFpcopy HFfromword pout plam pxt pyt pxp pyp old_out
                 lam xt yt xp yp Rr tr mem0 Hpre). }
      cbv beta. intros tr' mem' rets [Hrets [Htr [out [Hfe [Hb Hs]]]]].
      split; [exact Hrets |]. split; [exact Htr |].
      exists out. split; [| split; [exact Hb | exact Hs]].
      rewrite Hfe. apply make_line_feval_model_eq.
    Qed.

    (** fnspec form, for callers that use [straightline_call] / [mcall]. *)
    Definition spec_of_bls12_make_line_functional : spec_of "bls12_make_line" :=
      fnspec! "bls12_make_line" (pout plam pxt pyt pxp pyp : word)
        / (old_out : Fp12_felem) (lam xt yt : Fp2_felem)
          (xp yp : Fp_felem) Rr,
      { requires tr mem :=
          Fp2_bounded Fp2_tight lam /\
          Fp2_bounded Fp2_tight xt /\
          Fp2_bounded Fp2_tight yt /\
          Fp_bounded Fp_loose xp /\
          Fp_bounded Fp_loose yp /\
          (FElem_Fp12 pout old_out ⋆
           (FElem_Fp2 plam lam ⋆
            (FElem_Fp2 pxt xt ⋆
             (FElem_Fp2 pyt yt ⋆
              (FElem_Fp pxp xp ⋆
               (FElem_Fp pyp yp ⋆ Rr)))))) mem;
        ensures tr' mem' :=
          tr = tr' /\
          exists out,
            Fp12_feval out =
              make_line_feval_model (Fp2_feval lam) (Fp2_feval xt) (Fp2_feval yt)
                (Fp_feval xp) (Fp_feval yp) /\
            @AbstractField.bounded_by _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep'
              (@AbstractField.loose_bounds _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep') out /\
            (FElem_Fp12 pout out ⋆
             (FElem_Fp2 plam lam ⋆
              (FElem_Fp2 pxt xt ⋆
               (FElem_Fp2 pyt yt ⋆
                (FElem_Fp pxp xp ⋆
                 (FElem_Fp pyp yp ⋆ Rr)))))) mem' }.

    Lemma bls12_make_line_functional_spec :
      forall functions
        (EnvContains : map.get functions "bls12_make_line" =
          Some (snd bls12_make_line))
        (HFp2mul : spec_of_Fp2_mul functions)
        (HFp2sub : spec_of_Fp2_sub functions)
        (HFp2opp : spec_of_Fp2_opp functions)
        (HFp2mulfpEnv : map.get functions "bls12_Fp2_mul_fp" = Some (snd bls12_Fp2_mul_fp))
        (HFpmul : spec_of_Fp_mul functions)
        (HFpcopy : spec_of_Fp_felem_copy functions)
        (HFfromword : spec_of_Fp_from_word functions),
      spec_of_bls12_make_line_functional functions.
    Proof.
      intros. unfold spec_of_bls12_make_line_functional.
      intros pout plam pxt pyt pxp pyp old_out lam xt yt xp yp Rr tr mem0 Hpre.
      eapply Semantics.weaken_call.
      { exact (bls12_make_line_functional_ok functions EnvContains HFp2mul HFp2sub HFp2opp
                 (bls12_Fp2_mul_fp_ok functions HFp2mulfpEnv HFpmul) HFpcopy HFfromword
                 pout plam pxt pyt pxp pyp old_out lam xt yt xp yp Rr tr mem0 Hpre). }
      cbv beta. intros tr' mem' rets [Hrets [Htr Hex]].
      subst rets. exact (conj eq_refl (conj Htr Hex)).
    Qed.

End BLS12_MakeLineFunctional.
