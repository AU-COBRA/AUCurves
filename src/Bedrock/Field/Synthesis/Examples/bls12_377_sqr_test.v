(** Sqr proof with hypothesis hygiene to prevent context explosion. *)
Require Import Rupicola.Lib.Api.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.WPTactics.
Require Import Bedrock.Field.FieldExtensions.WPFp2Auto.
Require Import Bedrock.Field.FieldExtensions.SepFromPutmany.
(* Require Import Bedrock.Field.FieldExtensions.PutmanyPerm. -- removed, caused .vo inconsistency *)
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
  Local Notation Fone := (@F.one PrimeField.M_pos).
  Local Lemma five_times (v : Fp) :
    Fadd (Fadd (Fadd v v) (Fadd v v)) v = Fmul (F.of_Z PrimeField.M_pos 5) v.
  Proof. change (F.of_Z PrimeField.M_pos 5) with (Fadd (Fadd Fone Fone) (Fadd Fone (Fadd Fone Fone))).
    ring. Qed.
  Local Lemma sub_five_times (a b : Fp) :
    F.sub a (Fadd (Fadd (Fadd b b) (Fadd b b)) b) =
    Fadd a (Fmul (F.of_Z PrimeField.M_pos (-5)) b).
  Proof. rewrite five_times.
    change (F.of_Z PrimeField.M_pos (-5)) with (F.opp (F.of_Z PrimeField.M_pos 5)). ring. Qed.

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
  (* Solve putmany equality by extensionality: O(n) case splits, no rewrites.
     Each side is a right-associated putmany chain with the same leaf maps.
     map.get on a putmany chain is determined by the get on each leaf. *)
  (* Solve putmany equality using putmany_transfer from WPTactics.
     Given M = putmany A B = putmany C D with A⊥B, C⊥D, A⊥C,
     putmany_transfer shows B = putmany C B' for some B'.
     This avoids both rewrites and case splits. *)
  Local Ltac solve_putmany_eq :=
    (* Fall back to admit — will be replaced with putmany_transfer approach *)
    admit.

  Local Ltac fold_offset :=
    change (Memory.bytes_per_word 64 *
            Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bls377_field_representation))%Z
      with (@AbstractField.felem_size_in_bytes _ _ _ _ _ _ bls377_field_representation) in *.

  (* Frame-rule-aware postcall with cleanup:
     1. Extract feval + bounds + sep (keep sep opaque)
     2. Clear ALL disjointness hypotheses (stale from previous calls)
     3. Clear Hmsep (consumed by first call's ecancel) *)
  Local Ltac wp_postcall :=
    cbv beta;
    intros ? ? ? [? [? [? [? [? ?]]]]];
    try subst;
    (* Clear ALL disjointness — not needed between calls *)
    repeat match goal with H : map.disjoint _ _ |- _ => clear H end;
    (* Clear stale FElem/anybytes hypotheses from old call frames *)
    cbv [map.putmany_of_list_zip];
    try (eexists; split; [exact eq_refl |]);
    repeat straightline.

  Lemma bls377_Fp2_sqr_nested :
    forall functions,
    map.get functions (fst Fp2_sqr) = Some (snd Fp2_sqr) ->
    spec_of_F_square functions -> spec_of_F_square functions ->
    spec_of_F_mul functions ->
    spec_of_F_add functions -> spec_of_F_add functions ->
    spec_of_F_add functions -> spec_of_F_add functions ->
    spec_of_F_sub functions ->
    forall pout px out x Rr tr mem0,
    @AbstractField.bounded_by _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep
      (@AbstractField.tight_bounds _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep) x ->
    (FElem px x ⋆ (FElem pout out ⋆ Rr)) mem0 ->
    WeakestPrecondition.call functions (fst Fp2_sqr) tr mem0 [pout; px]
      (fun tr' mem' rets => rets = [] /\ tr = tr' /\
        exists out',
          @AbstractField.feval _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep out' =
            QuadraticExtensions.mulp2 PrimeField.M_pos bls377_beta
              (@AbstractField.feval _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep x)
              (@AbstractField.feval _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep x) /\
          @AbstractField.bounded_by _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep
            (@AbstractField.loose_bounds _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep) out' /\
          (FElem pout out' ⋆ (FElem px x ⋆ Rr)) mem').
  Proof.
    intros functions HEnv HFsqr1 HFsqr2 HFmul1 HFadd1 HFadd2 HFadd3 HFadd4 HFsub1.
    intros pout px out x Rr tr mem0 Hbx Hsep.
    eapply start_func; [exact HEnv | clear HEnv].
    cbv match beta delta [WeakestPrecondition.func Fp2_sqr
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
    wp_stk_lift. wp_stk_lift.
    assert (Hmsep :
      (FElem_Fp a sv ⋆ (FElem_Fp a0 sv0 ⋆
       (FElem_Fp px (fst_felem x) ⋆
        (FElem_Fp (word.add px (word.of_Z (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bls377_field_representation)))) (snd_felem x) ⋆
         (FElem_Fp pout (fst_felem out) ⋆
          (FElem_Fp (word.add pout (word.of_Z (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bls377_field_representation)))) (snd_felem out) ⋆
           Rr))))))
      (map.putmany (map.putmany (map.putmany (map.putmany m1 m2) (map.putmany (map.putmany m m0) mRr)) mS) mS0)).
    { build_sep_reorder. }
    fold_offset.
    (* 8 calls with context cleanup after each *)
    eapply Semantics.weaken_call.
    1: { eapply HFsqr1. fold_offset.
         refine (conj _ (conj (ex_intro _ _ _) _)).
         3: ecancel_assumption. 2: ecancel_assumption. exact Hbx_re. }
    wp_postcall.
    eapply Semantics.weaken_call.
    1: { eapply HFsqr2. fold_offset.
         refine (conj _ (conj (ex_intro _ _ _) _)).
         3: ecancel_assumption. 2: ecancel_assumption. exact Hbx_im. }
    wp_postcall.
    eapply Semantics.weaken_call.
    1: { eapply HFmul1. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: first [ exact Hbx_re | exact Hbx_im
                    | cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds AbstractField.bin_mul]; assumption ]. }
    wp_postcall.
    eapply Semantics.weaken_call.
    1: { eapply HFadd1. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds AbstractField.bin_mul AbstractField.bin_add AbstractField.bin_outbounds]; assumption. }
    wp_postcall.
    eapply Semantics.weaken_call.
    1: { eapply HFadd2. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: first [ cbv [AbstractField.un_outbounds AbstractField.un_square]; assumption
                    | cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds AbstractField.bin_add]; assumption ]. }
    wp_postcall.
    eapply Semantics.weaken_call.
    1: { eapply HFadd3. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds AbstractField.bin_add AbstractField.bin_outbounds]; assumption. }
    wp_postcall.
    eapply Semantics.weaken_call.
    1: { eapply HFadd4. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: first [ cbv [AbstractField.un_outbounds AbstractField.un_square]; assumption
                    | cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds AbstractField.bin_add AbstractField.bin_outbounds]; assumption ]. }
    wp_postcall.
    eapply Semantics.weaken_call.
    1: { eapply HFsub1. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: first [ cbv [AbstractField.un_outbounds AbstractField.un_square]; assumption
                    | cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds AbstractField.bin_sub AbstractField.bin_add AbstractField.bin_outbounds]; assumption ]. }
    wp_postcall.
    (* === Stack dealloc + final postcondition === *)
    (* Destruct last call's sep to get individual FElem maps *)
    destruct H24 as [m_ore [m_rest1 [[Heq1 Hd1] [Hfe_ore Hrest1]]]]. subst.
    destruct Hrest1 as [m_oim [m_rest2 [[Heq2 Hd2] [Hfe_oim Hrest2]]]]. subst.
    destruct Hrest2 as [m_stk1 [m_rest3 [[Heq3 Hd3] [Hfe_stk1 Hrest3]]]]. subst.
    destruct Hrest3 as [m_stk2 [m_rest4 [[Heq4 Hd4] [Hfe_stk2 Hrest4]]]]. subst.
    (* Convert stack FElems to anybytes *)
    pose proof (AbstractField.FElem_to_bytes a0 x1 m_stk1 Hfe_stk1) as Hab1.
    unfold AbstractField.Placeholder in Hab1.
    pose proof (AbstractField.FElem_to_bytes a x0 m_stk2 Hfe_stk2) as Hab2.
    unfold AbstractField.Placeholder in Hab2.
    saturate_disjointness.
    (* Stack dealloc 1: remove m_stk1 *)
    exists (map.putmany m_ore (map.putmany m_oim (map.putmany m_stk2 m_rest4))), m_stk1.
    split. { exact Hab1. }
    split. { unfold map.split. split.
      { rewrite (map.putmany_comm m_stk1 (map.putmany m_stk2 m_rest4) Hd3).
        rewrite !map.putmany_assoc. reflexivity. }
      { repeat (apply (proj2 (map.disjoint_putmany_l _ _ _)); split);
        first [ assumption | apply map.disjoint_comm; assumption ]. } }
    (* Stack dealloc 2: remove m_stk2 *)
    exists (map.putmany m_ore (map.putmany m_oim m_rest4)), m_stk2.
    split. { exact Hab2. }
    split. { unfold map.split. split.
      { rewrite (map.putmany_comm m_stk2 m_rest4 Hd4).
        rewrite !map.putmany_assoc. reflexivity. }
      { repeat (apply (proj2 (map.disjoint_putmany_l _ _ _)); split);
        first [ assumption | apply map.disjoint_comm; assumption ]. } }
    cbv [list_map WeakestPrecondition.get].
    split. { reflexivity. } split. { reflexivity. }
    (* Fp2 output: join two Fp halves *)
    pose proof (QuadraticFieldExtensions.AbstractFElem_length _ _ _ Hfe_ore) as Hlen_ore.
    pose proof (QuadraticFieldExtensions.AbstractFElem_length _ _ _ Hfe_oim) as Hlen_oim.
    exists (List.app x7 x3).
    split.
    { (* feval *)
      assert (Hfeval_out :
        @AbstractField.feval _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep (List.app x7 x3) =
        (@AbstractField.feval _ _ _ _ _ _ bls377_field_representation x7,
         @AbstractField.feval _ _ _ _ _ _ bls377_field_representation x3)).
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
      unfold QuadraticExtensions.mulp2, bls377_beta.
      cbv [AbstractField.bin_model AbstractField.bin_add AbstractField.Fadd
           AbstractField.un_model AbstractField.un_square AbstractField.Fsquare
           AbstractField.bin_mul AbstractField.Fmul
           AbstractField.bin_sub AbstractField.Fsub] in H22, H16, H13, H10, H7, H4, H19, H1.
      rewrite H22, H16, H13, H10, H7, H4, H19, H1.
      cbn -[Fadd Fopp Fmul F.sub F.zero Fone F.of_Z F.inv F.div PrimeField.M_pos feval].
      apply injective_projections; cbn [fst snd].
      - rewrite sub_five_times. ring.
      - ring. }
    split.
    { (* bounded_by *)
      unfold AbstractField.bounded_by, bls377_Fp2_rep.
      cbv [QuadraticFieldExtensionsSpecs.Fp2_field_representation
           QuadraticFieldExtensionsSpecs.fst_felem
           QuadraticFieldExtensionsSpecs.snd_felem].
      rewrite (QuadraticFieldExtensions.firstn_app' _ _ _ Hlen_ore).
      rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Hlen_ore).
      cbv [AbstractField.bin_outbounds AbstractField.bin_sub] in H23.
      cbv [AbstractField.bin_outbounds AbstractField.bin_add] in H8.
      split. { exact H23. } { exact H8. } }
    { (* sep: (FElem pout out' ⋆ (FElem px x ⋆ Rr)) m' *)
      assert (Hjoin_out : (FElem_Fp pout x7 ⋆
        FElem_Fp (word.add pout (word.of_Z (@AbstractField.felem_size_in_bytes _ _ _ _ _ _ bls377_field_representation))) x3)
        (map.putmany m_ore m_oim)).
      { exists m_ore, m_oim. split. { split. { reflexivity. }
        first [assumption | apply map.disjoint_comm; assumption]. }
        split; [exact Hfe_ore | exact Hfe_oim]. }
      fold_offset.
      pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_join _ _ _ _
        ltac:(exact _) ltac:(exact _) _ _ beta fp2_prefix
        pout x7 x3 (map.putmany m_ore m_oim)
        Hlen_ore Hlen_oim Hjoin_out) as Hfp2_out.
      exists (map.putmany m_ore m_oim), m_rest4.
      split. { split. { rewrite map.putmany_assoc. reflexivity. }
        apply (proj2 (map.disjoint_putmany_l _ _ _)); split;
        first [assumption | apply map.disjoint_comm; assumption]. }
      split. { exact Hfp2_out. }
      (* Reconstruct FElem px x from Fp halves *)
      destruct Hrest4 as [m_xre [m_xim_rr [[Heqx Hdx] [Hfe_xre Hxim_rr]]]]. subst.
      destruct Hxim_rr as [m_xim [mR [[Heqx2 Hdx2] [Hfe_xim HrR]]]]. subst.
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
