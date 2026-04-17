(** Inv proof with fast iteration via MCP. *)
Require Import Rupicola.Lib.Api.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.WPTactics.
Require Import Bedrock.Field.FieldExtensions.WPFp2Auto.
Require Import Bedrock.Field.FieldExtensions.SepFromPutmany.
Require Import Bedrock.Field.Synthesis.Examples.bls12_377_Fp2.
Require Import Bedrock.Field.Synthesis.Examples.bls12_377_instances.
Require Import Bedrock.Field.Synthesis.Examples.bls12_377_prime_certif.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Algebra.Field.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope.

Section P.
  Existing Instances Bitwidth64.BW64
    Defaults64.default_parameters Defaults64.default_parameters_ok
    bls377_prime_parameters bls377_prime_parameters_ok
    bls377_field_representation bls377_field_representation_ok.
  Existing Instance prime_field_parameters.
  Existing Instances bls377_Fp2_params bls377_Fp2_rep bls377_Fp2_rep_ok.
  Local Notation F := (F PrimeField.M_pos).
  Let beta := bls377_beta.
  Let fp2_prefix := "bls377_Fp2_".
  Local Instance spec_of_F_add : spec_of (AbstractField.add (F:=F)) :=
    AbstractField.binop_spec AbstractField.bin_add (F:=F).
  Local Instance spec_of_F_sub : spec_of (AbstractField.sub (F:=F)) :=
    AbstractField.binop_spec AbstractField.bin_sub (F:=F).
  Local Instance spec_of_F_mul : spec_of (AbstractField.mul (F:=F)) :=
    AbstractField.binop_spec AbstractField.bin_mul (F:=F).
  Local Instance spec_of_F_square : spec_of (AbstractField.square (F:=F)) :=
    AbstractField.unop_spec AbstractField.un_square (F:=F).
  Local Instance spec_of_F_inv : spec_of (AbstractField.inv (F:=F)) :=
    AbstractField.unop_spec AbstractField.un_inv (F:=F).
  Local Notation FElem_Fp := (@AbstractField.FElem _ _ _ _ _ _ bls377_field_representation).

  Let Fp_ftf := @Algebra.Field.field_theory_for_stdlib_tactic
    (F.F PrimeField.M_pos) (@eq (F.F PrimeField.M_pos))
    (@F.zero PrimeField.M_pos) (@F.one PrimeField.M_pos)
    (@F.opp PrimeField.M_pos) (@F.add PrimeField.M_pos)
    (@F.mul PrimeField.M_pos) (@F.sub PrimeField.M_pos)
    (@F.inv PrimeField.M_pos) (@F.div PrimeField.M_pos)
    (@F.field_modulo PrimeField.M_pos prime_bls12_377).
  Add Field Fp_field_local : Fp_ftf.
  Local Notation Fp := (F.F PrimeField.M_pos).
  Local Notation Fadd := (@F.add PrimeField.M_pos).
  Local Notation Fmul := (@F.mul PrimeField.M_pos).
  Local Notation Fopp := (@F.opp PrimeField.M_pos).
  Local Notation Fone := (@F.one PrimeField.M_pos).
  Local Lemma five_times (v : Fp) :
    Fadd (Fadd (Fadd v v) (Fadd v v)) v = Fmul (F.of_Z PrimeField.M_pos 5) v.
  Proof. change (F.of_Z PrimeField.M_pos 5) with (Fadd (Fadd Fone Fone) (Fadd Fone (Fadd Fone Fone))).
    ring. Qed.

  Local Ltac saturate_disjointness :=
    repeat match goal with
    | H : map.disjoint ?a (map.putmany ?b ?c) |- _ =>
      lazymatch goal with
      | _ : map.disjoint a b, _ : map.disjoint a c |- _ => fail
      | _ => pose proof (proj1 (map.disjoint_putmany_r a b c) H) as [? ?] end
    | H : map.disjoint (map.putmany ?a ?b) ?c |- _ =>
      lazymatch goal with
      | _ : map.disjoint a c, _ : map.disjoint b c |- _ => fail
      | _ => pose proof (proj1 (map.disjoint_putmany_l a b c) H) as [? ?] end
    end.
  Local Ltac wp_stk_lift :=
    split; [apply Z_mod_mult |];
    let a := fresh "a" in let mS := fresh "mS" in let mC := fresh "mC" in
    intros a mS mC ?Hany ?Hsp;
    let Hfb := fresh in
    pose proof (@AbstractField.FElem_from_bytes _ _ _ _ _ _
      bls377_field_representation ltac:(exact _) ltac:(exact _) a) as Hfb;
    unfold AbstractField.Placeholder in Hfb;
    let sv := fresh "sv" in let Hfe := fresh "Hfe" in
    destruct (proj1 (Hfb mS) Hany) as [sv Hfe]; clear Hfb Hany;
    let Heq := fresh in let Hd := fresh "Hd" in
    destruct Hsp as [Heq Hd];
    repeat match goal with
    | Hsep : (_ ⋆ _) ?m |- _ =>
        let Hsep' := fresh Hsep in
        pose proof (sep_lift_putmany _ _ _ _ Hsep Hd) as Hsep';
        clear Hsep; rename Hsep' into Hsep
    end;
    subst mC; repeat straightline; saturate_disjointness.

  Local Ltac fold_offset :=
    change (Memory.bytes_per_word 64 *
            Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bls377_field_representation))%Z
      with (@AbstractField.felem_size_in_bytes _ _ _ _ _ _ bls377_field_representation) in *.

  Local Ltac wp_postcall :=
    cbv beta;
    intros ? ? ? [? [? [? [? [? ?]]]]];
    try subst;
    repeat match goal with H : map.disjoint _ _ |- _ => clear H end;
    cbv [map.putmany_of_list_zip];
    try (eexists; split; [exact eq_refl |]);
    repeat straightline.

  Lemma bls377_Fp2_inv_nested :
    forall functions,
    map.get functions (fst Fp2_inv) = Some (snd Fp2_inv) ->
    spec_of_F_square functions -> spec_of_F_square functions ->
    spec_of_F_add functions -> spec_of_F_add functions ->
    spec_of_F_add functions -> spec_of_F_add functions ->
    spec_of_F_inv functions ->
    spec_of_F_mul functions ->
    spec_of_F_sub functions -> spec_of_F_sub functions ->
    spec_of_F_mul functions ->
    forall pout px out x Rr tr mem0,
    @AbstractField.bounded_by _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep
      (@AbstractField.tight_bounds _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep) x ->
    (FElem px x ⋆ (FElem pout out ⋆ Rr)) mem0 ->
    WeakestPrecondition.call functions (fst Fp2_inv) tr mem0 [pout; px]
      (fun tr' mem' rets => rets = [] /\ tr = tr' /\
        exists out',
          (let fev := @AbstractField.feval _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep in
           let a0 := fst (fev x) in let a1 := snd (fev x) in
           let norm := Fadd (Fmul a0 a0) (Fmul (F.of_Z PrimeField.M_pos 5) (Fmul a1 a1)) in
           let inv_norm := @F.inv PrimeField.M_pos norm in
           fev out' = (Fmul a0 inv_norm, Fmul (Fopp a1) inv_norm)) /\
          @AbstractField.bounded_by _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep
            (@AbstractField.loose_bounds _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep) out' /\
          (FElem pout out' ⋆ (FElem px x ⋆ Rr)) mem').
  Proof.
    intros functions HEnv HFsqr1 HFsqr2 HFadd1 HFadd2 HFadd3 HFadd4
           HFinv HFmul1 HFsub1 HFsub2 HFmul2.
    intros pout px out x Rr tr mem0 Hbx Hsep.
    eapply start_func; [exact HEnv | clear HEnv].
    cbv match beta delta [WeakestPrecondition.func Fp2_inv
      bls12_377_Fp2.expr_2nd_felem bls12_377_Fp2.felem_offset].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    destruct Hsep as [m_x [m_or [[? ?] [Hfx Hor]]]].
    destruct Hor as [m_o [mRr [[? ?] [Hfo Hr]]]]. subst.
    wp_fp2_split beta fp2_prefix Hfo.
    wp_fp2_split beta fp2_prefix Hfx.
    cbv [AbstractField.bounded_by bls377_Fp2_rep
         QuadraticFieldExtensionsSpecs.Fp2_field_representation] in Hbx.
    destruct Hbx as [Hbx_re Hbx_im].
    saturate_disjointness.
    wp_stk_lift. wp_stk_lift. wp_stk_lift.
    assert (Hmsep :
      (FElem_Fp a sv ⋆ (FElem_Fp a0 sv0 ⋆ (FElem_Fp a1 sv1 ⋆
       (FElem_Fp px (fst_felem x) ⋆
        (FElem_Fp (word.add px (word.of_Z (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bls377_field_representation)))) (snd_felem x) ⋆
         (FElem_Fp pout (fst_felem out) ⋆
          (FElem_Fp (word.add pout (word.of_Z (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bls377_field_representation)))) (snd_felem out) ⋆
           Rr)))))))
      (map.putmany (map.putmany (map.putmany (map.putmany (map.putmany m1 m2) (map.putmany (map.putmany m m0) mRr)) mS) mS0) mS1)).
    { build_sep_reorder. }
    fold_offset.
    (* Call 1: sqr(asq, inx.re) *)
    eapply Semantics.weaken_call.
    1: { eapply HFsqr1. fold_offset.
         refine (conj _ (conj (ex_intro _ _ _) _)).
         3: ecancel_assumption. 2: ecancel_assumption. exact Hbx_re. }
    wp_postcall.
    (* Call 2: sqr(bsq, inx.im) *)
    eapply Semantics.weaken_call.
    1: { eapply HFsqr2. fold_offset.
         refine (conj _ (conj (ex_intro _ _ _) _)).
         3: ecancel_assumption. 2: ecancel_assumption. exact Hbx_im. }
    wp_postcall.
    (* Call 3: add(norm, bsq, bsq) *)
    eapply Semantics.weaken_call.
    1: { eapply HFadd1. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds AbstractField.bin_outbounds
                    AbstractField.un_outbounds AbstractField.un_square
                    AbstractField.bin_add]; assumption. }
    wp_postcall.
    (* Call 4: add(norm, norm, norm) *)
    eapply Semantics.weaken_call.
    1: { eapply HFadd2. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds AbstractField.bin_outbounds
                    AbstractField.bin_add]; assumption. }
    wp_postcall.
    (* Call 5: add(norm, norm, bsq) *)
    eapply Semantics.weaken_call.
    1: { eapply HFadd3. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds AbstractField.bin_outbounds
                    AbstractField.un_outbounds AbstractField.un_square
                    AbstractField.bin_add]; assumption. }
    wp_postcall.
    (* Call 6: add(norm, asq, norm) *)
    eapply Semantics.weaken_call.
    1: { eapply HFadd4. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds AbstractField.bin_outbounds
                    AbstractField.un_outbounds AbstractField.un_square
                    AbstractField.bin_add]; assumption. }
    wp_postcall.
    (* Call 7: inv(norm, norm) *)
    eapply Semantics.weaken_call.
    1: { eapply HFinv. fold_offset.
         refine (conj _ (conj (ex_intro _ _ _) _)).
         3: ecancel_assumption. 2: ecancel_assumption.
         cbv [AbstractField.un_xbounds AbstractField.un_inv
              AbstractField.bin_outbounds AbstractField.bin_add]; assumption. }
    wp_postcall.
    (* Call 8: mul(out.re, inx.re, norm) *)
    eapply Semantics.weaken_call.
    1: { eapply HFmul1. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: first [ exact Hbx_re
                    | cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds AbstractField.bin_outbounds
                           AbstractField.un_outbounds AbstractField.un_inv
                           AbstractField.bin_mul AbstractField.bin_add]; assumption ]. }
    wp_postcall.
    (* Call 9: sub(asq, bsq, bsq) — asq := 0 *)
    eapply Semantics.weaken_call.
    1: { eapply HFsub1. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds AbstractField.bin_outbounds
                    AbstractField.un_outbounds AbstractField.un_square
                    AbstractField.bin_sub]; assumption. }
    wp_postcall.
    (* Call 10: sub(asq, asq, inx.im) — asq := -b *)
    eapply Semantics.weaken_call.
    1: { eapply HFsub2. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: first [ exact Hbx_im
                    | cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds AbstractField.bin_outbounds
                           AbstractField.bin_sub]; assumption ]. }
    wp_postcall.
    (* Call 11: mul(out.im, asq, norm) *)
    eapply Semantics.weaken_call.
    1: { eapply HFmul2. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds AbstractField.bin_outbounds
                    AbstractField.un_outbounds AbstractField.un_inv
                    AbstractField.bin_mul AbstractField.bin_sub]; assumption. }
    wp_postcall.
    (* === Postcondition === *)
    (* H30 sep order: pout+off(x10), a(x9), pout(x7), a1(x6), a0(x1), px(fst x), px+off(snd x), Rr *)
    destruct H30 as [m_oim [m_rest1 [[? Hdj1] [Hfe_oim Hrest1]]]]. subst.
    destruct Hrest1 as [m_asq [m_rest2 [[? Hdj2] [Hfe_asq Hrest2]]]]. subst.
    destruct Hrest2 as [m_ore [m_rest3 [[? Hdj3] [Hfe_ore Hrest3]]]]. subst.
    destruct Hrest3 as [m_norm [m_rest4 [[? Hdj4] [Hfe_norm Hrest4]]]]. subst.
    destruct Hrest4 as [m_bsq [m_rest5 [[? Hdj5] [Hfe_bsq Hrest5]]]]. subst.
    (* Convert stack FElems to anybytes: a1(norm), a0(bsq), a(asq) *)
    pose proof (AbstractField.FElem_to_bytes a1 x6 m_norm Hfe_norm) as Hab_norm.
    unfold AbstractField.Placeholder in Hab_norm.
    pose proof (AbstractField.FElem_to_bytes a0 x1 m_bsq Hfe_bsq) as Hab_bsq.
    unfold AbstractField.Placeholder in Hab_bsq.
    pose proof (AbstractField.FElem_to_bytes a x9 m_asq Hfe_asq) as Hab_asq.
    unfold AbstractField.Placeholder in Hab_asq.
    saturate_disjointness.
    (* Stack dealloc 1: remove m_norm (a1) — position 4 in chain *)
    (* Chain: oim, asq, ore, norm, bsq, rest5 *)
    exists (map.putmany m_oim (map.putmany m_asq (map.putmany m_ore (map.putmany m_bsq m_rest5)))), m_norm.
    split. { exact Hab_norm. }
    split. { unfold map.split. split.
      { rewrite (map.putmany_comm m_norm (map.putmany m_bsq m_rest5) Hdj4).
        rewrite !map.putmany_assoc. reflexivity. }
      { repeat (apply (proj2 (map.disjoint_putmany_l _ _ _)); split);
        first [ assumption | apply map.disjoint_comm; assumption ]. } }
    (* Stack dealloc 2: remove m_bsq (a0) — now last before rest5 *)
    exists (map.putmany m_oim (map.putmany m_asq (map.putmany m_ore m_rest5))), m_bsq.
    split. { exact Hab_bsq. }
    split. { unfold map.split. split.
      { rewrite (map.putmany_comm m_bsq m_rest5 Hdj5).
        rewrite !map.putmany_assoc. reflexivity. }
      { repeat (apply (proj2 (map.disjoint_putmany_l _ _ _)); split);
        first [ assumption | apply map.disjoint_comm; assumption ]. } }
    (* Stack dealloc 3: remove m_asq (a) — now position 2 *)
    exists (map.putmany m_oim (map.putmany m_ore m_rest5)), m_asq.
    split. { exact Hab_asq. }
    split. { unfold map.split. split.
      { rewrite (map.putmany_comm m_asq (map.putmany m_ore m_rest5)
          ltac:(apply (proj2 (map.disjoint_putmany_r _ _ _)); split;
                first [ assumption | apply map.disjoint_comm; assumption ])).
        rewrite !map.putmany_assoc. reflexivity. }
      { repeat (apply (proj2 (map.disjoint_putmany_l _ _ _)); split);
        first [ assumption | apply map.disjoint_comm; assumption ]. } }
    cbv [list_map WeakestPrecondition.get].
    split. { reflexivity. } split. { reflexivity. }
    (* Fp2 output join: m_ore (pout, x7=out.re) + m_oim (pout+off, x10=out.im) *)
    pose proof (QuadraticFieldExtensions.AbstractFElem_length _ _ _ Hfe_ore) as Hlen_ore.
    pose proof (QuadraticFieldExtensions.AbstractFElem_length _ _ _ Hfe_oim) as Hlen_oim.
    exists (List.app x7 x10).
    split.
    { (* feval *)
      assert (Hfeval_out :
        @AbstractField.feval _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep (List.app x7 x10) =
        (@AbstractField.feval _ _ _ _ _ _ bls377_field_representation x7,
         @AbstractField.feval _ _ _ _ _ _ bls377_field_representation x10)).
      { unfold AbstractField.feval, bls377_Fp2_rep,
               QuadraticFieldExtensionsSpecs.Fp2_field_representation,
               QuadraticFieldExtensionsSpecs.fst_felem,
               QuadraticFieldExtensionsSpecs.snd_felem.
        rewrite (QuadraticFieldExtensions.firstn_app' _ _ _ Hlen_ore).
        rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Hlen_ore).
        reflexivity. }
      assert (Hfeval_x :
        @AbstractField.feval _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep x =
        (@AbstractField.feval _ _ _ _ _ _ bls377_field_representation (fst_felem x),
         @AbstractField.feval _ _ _ _ _ _ bls377_field_representation (snd_felem x))).
      { unfold AbstractField.feval, bls377_Fp2_rep,
               QuadraticFieldExtensionsSpecs.Fp2_field_representation.
        reflexivity. }
      rewrite Hfeval_out, Hfeval_x.
      repeat match goal with
      | H : @AbstractField.feval _ _ _ _ _ _ bls377_field_representation _ = _ |- _ =>
        cbv [AbstractField.bin_model AbstractField.bin_add AbstractField.Fadd
             AbstractField.un_model AbstractField.un_square AbstractField.Fsquare
             AbstractField.un_inv AbstractField.Finv
             AbstractField.bin_mul AbstractField.Fmul
             AbstractField.bin_sub AbstractField.Fsub] in H
      end.
      repeat match goal with
      | H : @AbstractField.feval _ _ _ _ _ _ bls377_field_representation _ = _ |- _ =>
        first [ rewrite H | clear H ]
      end.
      cbn -[Fadd Fopp Fmul F.sub F.zero Fone F.of_Z F.inv F.div PrimeField.M_pos feval].
      apply injective_projections; cbn [fst snd].
      - rewrite five_times. ring.
      - rewrite five_times. ring. }
    split.
    { (* bounded_by *)
      unfold AbstractField.bounded_by, bls377_Fp2_rep.
      cbv [QuadraticFieldExtensionsSpecs.Fp2_field_representation
           QuadraticFieldExtensionsSpecs.fst_felem
           QuadraticFieldExtensionsSpecs.snd_felem].
      rewrite (QuadraticFieldExtensions.firstn_app' _ _ _ Hlen_ore).
      rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Hlen_ore).
      split; (cbv [AbstractField.bin_outbounds AbstractField.bin_mul AbstractField.bin_sub] in *; assumption). }
    { (* sep *)
      assert (Hjoin_out : (FElem_Fp pout x7 ⋆
        FElem_Fp (word.add pout (word.of_Z (@AbstractField.felem_size_in_bytes _ _ _ _ _ _ bls377_field_representation))) x10)
        (map.putmany m_ore m_oim)).
      { exists m_ore, m_oim. split. { split.
        { rewrite map.putmany_comm by (first [assumption | apply map.disjoint_comm; assumption]). reflexivity. }
        first [assumption | apply map.disjoint_comm; assumption]. }
        split; [exact Hfe_ore | exact Hfe_oim]. }
      fold_offset.
      pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_join _ _ _ _
        ltac:(exact _) ltac:(exact _) _ _ beta fp2_prefix
        pout x7 x10 (map.putmany m_ore m_oim)
        Hlen_ore Hlen_oim Hjoin_out) as Hfp2_out.
      exists (map.putmany m_ore m_oim), m_rest5.
      split. { split.
        { rewrite map.putmany_assoc.
          rewrite (map.putmany_comm m_oim m_ore) by
            (first [assumption | apply map.disjoint_comm; assumption]).
          reflexivity. }
        apply (proj2 (map.disjoint_putmany_l _ _ _)); split;
        first [assumption | apply map.disjoint_comm; assumption]. }
      split. { exact Hfp2_out. }
      (* Reconstruct FElem px x *)
      destruct Hrest5 as [m_xre [m_rest6 [[? Hdx1] [Hfe_xre Hrest6]]]]. subst.
      destruct Hrest6 as [m_xim [mR [[? Hdx2] [Hfe_xim HrR]]]]. subst.
      pose proof (QuadraticFieldExtensions.AbstractFElem_length _ _ _ Hfe_xre) as Hlen_xre.
      pose proof (QuadraticFieldExtensions.AbstractFElem_length _ _ _ Hfe_xim) as Hlen_xim.
      saturate_disjointness.
      assert (Hjoin_x : (FElem_Fp px (fst_felem x) ⋆
        FElem_Fp (word.add px (word.of_Z (@AbstractField.felem_size_in_bytes _ _ _ _ _ _ bls377_field_representation))) (snd_felem x))
        (map.putmany m_xre m_xim)).
      { exists m_xre, m_xim. split. { split. { reflexivity. }
        first [assumption | apply map.disjoint_comm; assumption]. }
        split; assumption. }
      fold_offset.
      pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_join _ _ _ _
        ltac:(exact _) ltac:(exact _) _ _ beta fp2_prefix
        px (fst_felem x) (snd_felem x) (map.putmany m_xre m_xim)
        Hlen_xre Hlen_xim Hjoin_x) as Hfx'.
      assert (Hx_eq : x = List.app (fst_felem x) (snd_felem x)).
      { unfold QuadraticFieldExtensionsSpecs.fst_felem, QuadraticFieldExtensionsSpecs.snd_felem.
        symmetry. apply List.firstn_skipn. }
      rewrite Hx_eq.
      exists (map.putmany m_xre m_xim), mR.
      split. { split. { rewrite map.putmany_assoc. reflexivity. }
        apply (proj2 (map.disjoint_putmany_l _ _ _)); split; assumption. }
      split. { exact Hfx'. }
      exact HrR. }
  Qed.

End P.
