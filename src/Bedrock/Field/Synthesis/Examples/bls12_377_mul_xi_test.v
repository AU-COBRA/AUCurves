(** Test file for developing the bls377_Fp2_mul_xi proof interactively. *)
Require Import Rupicola.Lib.Api.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.WPTactics.
Require Import Bedrock.Field.FieldExtensions.WPFp2Auto.
Require Import Bedrock.Field.FieldExtensions.SepFromPutmany.
Require Import Bedrock.Field.Synthesis.Examples.bls12_377_Fp2.
Require Import Bedrock.Field.Synthesis.Examples.bls12_377_instances.
Require Import Bedrock.Field.Synthesis.Examples.bls12_377_prime_certif.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Theory.BLS12Pairing.Fp6.
Require Import Bedrock.Field.FieldExtensions.PairingFieldOps.
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
  Local Instance spec_of_F_opp : spec_of (@AbstractField.opp _ prime_field_parameters) :=
    AbstractField.unop_spec AbstractField.un_opp (F:=F).
  Local Instance spec_of_F_felem_copy : spec_of (AbstractField.felem_copy (F:=F)) :=
    AbstractField.spec_of_felem_copy (F:=F).

  Local Notation FElem_Fp := (@AbstractField.FElem _ _ _ _ _ _ bls377_field_representation).

  (* Field theory for ring/field tactics *)
  Let Fp_ftf := @Algebra.Field.field_theory_for_stdlib_tactic
    (F.F PrimeField.M_pos) (@eq (F.F PrimeField.M_pos))
    (@F.zero PrimeField.M_pos) (@F.one PrimeField.M_pos)
    (@F.opp PrimeField.M_pos) (@F.add PrimeField.M_pos)
    (@F.mul PrimeField.M_pos) (@F.sub PrimeField.M_pos)
    (@F.inv PrimeField.M_pos) (@F.div PrimeField.M_pos)
    (@F.field_modulo PrimeField.M_pos prime_bls12_377).
  Add Field Fp_field_local : Fp_ftf.

  (* Helper: F.of_Z 0 = F.zero, F.of_Z 1 = F.one *)
  Local Lemma of_Z_0 : F.of_Z PrimeField.M_pos 0 = @F.zero PrimeField.M_pos.
  Proof. reflexivity. Qed.
  Local Lemma of_Z_1 : F.of_Z PrimeField.M_pos 1 = @F.one PrimeField.M_pos.
  Proof. reflexivity. Qed.
  Local Notation Fp := (F.F PrimeField.M_pos).
  Local Notation Fadd := (@F.add PrimeField.M_pos).
  Local Notation Fmul := (@F.mul PrimeField.M_pos).
  Local Notation Fopp := (@F.opp PrimeField.M_pos).
  Local Notation Fone := (@F.one PrimeField.M_pos).

  (* Helper: 5x = x+x+(x+x)+x via iterated add *)
  Local Lemma five_times (v : Fp) :
    Fadd (Fadd (Fadd v v) (Fadd v v)) v = Fmul (F.of_Z PrimeField.M_pos 5) v.
  Proof. change (F.of_Z PrimeField.M_pos 5) with (Fadd (Fadd Fone Fone) (Fadd Fone (Fadd Fone Fone))).
    ring. Qed.
  (* Helper: opp(5x) = F.of_Z(-5) * x *)
  Local Lemma opp_five_times (v : Fp) :
    Fopp (Fadd (Fadd (Fadd v v) (Fadd v v)) v) =
    Fmul (F.of_Z PrimeField.M_pos (-5)) v.
  Proof.
    rewrite five_times.
    change (F.of_Z PrimeField.M_pos (-5)) with (Fopp (F.of_Z PrimeField.M_pos 5)).
    ring.
  Qed.

  Local Ltac saturate_disjointness :=
    repeat match goal with
    | H : map.disjoint ?a (map.putmany ?b ?c) |- _ =>
      lazymatch goal with
      | _ : map.disjoint a b, _ : map.disjoint a c |- _ => fail
      | _ => let H1 := fresh "Hd" in let H2 := fresh "Hd" in
             pose proof (proj1 (map.disjoint_putmany_r a b c) H) as [H1 H2] end
    | H : map.disjoint (map.putmany ?a ?b) ?c |- _ =>
      lazymatch goal with
      | _ : map.disjoint a c, _ : map.disjoint b c |- _ => fail
      | _ => let H1 := fresh "Hd" in let H2 := fresh "Hd" in
             pose proof (proj1 (map.disjoint_putmany_l a b c) H) as [H1 H2] end
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
    cbv beta; intros ? ? ? ?;
    repeat match goal with
    | H : exists _, _ /\ _ |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    end;
    try subst;
    cbv [map.putmany_of_list_zip];
    try (eexists; split; [exact eq_refl |]);
    repeat straightline.

  Lemma test_mul_xi :
    forall functions,
    map.get functions (fst Fp2_mul_xi) = Some (snd Fp2_mul_xi) ->
    spec_of_F_add functions -> spec_of_F_add functions -> spec_of_F_add functions ->
    spec_of_F_felem_copy functions -> spec_of_F_opp functions ->
    forall pout px out x Rr tr mem0,
    @AbstractField.bounded_by _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep
      (@AbstractField.tight_bounds _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep) x ->
    (FElem px x ⋆ (FElem pout out ⋆ Rr)) mem0 ->
    WeakestPrecondition.call functions (fst Fp2_mul_xi) tr mem0 [pout; px]
      (fun tr' mem' rets => rets = [] /\ tr = tr' /\
        exists out',
          @AbstractField.feval _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep out' =
            Fp6.fp2_mul_xi PrimeField.M_pos bls377_beta bls377_xi_re bls377_xi_im
              (@AbstractField.feval _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep x) /\
          @AbstractField.bounded_by _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep
            (@AbstractField.loose_bounds _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep) out' /\
          (FElem pout out' ⋆ (FElem px x ⋆ Rr)) mem').
  Proof.
    intros functions HEnv HFadd1 HFadd2 HFadd3 HFcopy HFopp.
    intros pout px out x Rr tr mem0 Hbx Hsep.
    eapply start_func; [exact HEnv | clear HEnv].
    cbv match beta delta [WeakestPrecondition.func Fp2_mul_xi
      bls12_377_Fp2.expr_2nd_felem bls12_377_Fp2.felem_offset].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* === Setup === *)
    destruct Hsep as [m_x [m_or [[? ?] [Hfx Hor]]]].
    destruct Hor as [m_o [mRr [[? ?] [Hfo Hr]]]]. subst.
    wp_fp2_split beta fp2_prefix Hfo.
    wp_fp2_split beta fp2_prefix Hfx.
    cbv [AbstractField.bounded_by bls377_Fp2_rep
         QuadraticFieldExtensionsSpecs.Fp2_field_representation] in Hbx.
    destruct Hbx as [Hbx_re Hbx_im].
    saturate_disjointness.
    wp_stk_lift.
    assert (Hmsep :
      (FElem_Fp a sv ⋆
       (FElem_Fp px (fst_felem x) ⋆
        (FElem_Fp (word.add px (word.of_Z (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bls377_field_representation)))) (snd_felem x) ⋆
         (FElem_Fp pout (fst_felem out) ⋆
          (FElem_Fp (word.add pout (word.of_Z (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bls377_field_representation)))) (snd_felem out) ⋆
           Rr)))))
      (map.putmany (map.putmany (map.putmany m1 m2) (map.putmany (map.putmany m m0) mRr)) mS)).
    { build_sep_reorder. }
    (* === Call 1: add(tmp, x.im, x.im) === *)
    eapply Semantics.weaken_call.
    1: { eapply HFadd1.
         split; [exact Hbx_im |]. split; [exact Hbx_im |]. fold_offset.
         split; [eexists; ecancel_assumption |].
         split; [eexists; ecancel_assumption |].
         ecancel_assumption. }
    wp_postcall.
    (* === Call 2: add(tmp, tmp, tmp) === *)
    eapply Semantics.weaken_call.
    1: { eapply HFadd2. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds
                    AbstractField.bin_add]; assumption. }
    wp_postcall.
    (* === Call 3: add(tmp, tmp, x.im) === *)
    eapply Semantics.weaken_call.
    1: { eapply HFadd3. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: first [ exact Hbx_im
                    | cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds
                           AbstractField.bin_add]; assumption ]. }
    wp_postcall.
    (* === Call 4: copy(out.im, x.re) === *)
    eapply Semantics.weaken_call.
    1: { eapply HFcopy. fold_offset.
         split; [ecancel_assumption |]. ecancel_assumption. }
    wp_postcall.
    (* === Call 5: opp(out.re, tmp) === *)
    eapply Semantics.weaken_call.
    1: { eapply HFopp. fold_offset.
         refine (conj _ (conj (ex_intro _ _ _) _)).
         3: ecancel_assumption. 2: ecancel_assumption.
         cbv [AbstractField.un_xbounds AbstractField.un_opp]; assumption. }
    wp_postcall.
    (* === Final postcondition: stack dealloc + feval + bounds + sep === *)
    (* The context should have:
       - FElem hypotheses for opp output (out.re), copy output (out.im), stack tmp
       - feval hypotheses from all 5 calls
       - A sep on the current memory
       - The goal is: exists m' mStack', anybytes ... /\ split ... /\ list_map ... *)
    (* Step 1: find the stack FElem and convert to anybytes *)
    (* H13 : (FElem pout x3 ⋆ (FElem (pout+off) (fst_felem x) ⋆
              (FElem a x2 ⋆ (FElem px xre ⋆ (FElem (px+off) xim ⋆ Rr))))) m'3
       x0 = 2*xim, x1 = 4*xim, x2 = 5*xim, x3 = opp(x2) = -5*xim
       copy output at pout+off = fst_felem x = xre *)
    (* Step 1: Decompose H13 to extract stack FElem (a, x2) *)
    destruct H13 as [m_ore [m_rest1 [[? ?] [Hfe_ore Hrest1]]]].
    destruct Hrest1 as [m_oim [m_rest2 [[? ?] [Hfe_oim Hrest2]]]].
    destruct Hrest2 as [m_stk [m_rest3 [[? ?] [Hfe_stk2 Hrest3]]]]. subst.
    saturate_disjointness.
    (* Step 2: Convert stack FElem to anybytes *)
    pose proof (AbstractField.FElem_to_bytes a x2 m_stk Hfe_stk2) as Hab_stk.
    unfold AbstractField.Placeholder in Hab_stk.
    (* Step 3: Provide stack region and rest *)
    (* m'3 = putmany m_ore (putmany m_oim (putmany m_stk m_rest3))
       We need: m'3 = putmany m' m_stk for some m' *)
    exists (map.putmany m_ore (map.putmany m_oim m_rest3)), m_stk.
    split. { exact Hab_stk. }
    split. { unfold map.split. split.
      - (* Reorder: swap m_stk past m_rest3 to the end *)
        rewrite (map.putmany_comm m_stk m_rest3) by assumption.
        rewrite <- !map.putmany_assoc. reflexivity.
      - (* disjoint (putmany m_ore (putmany m_oim m_rest3)) m_stk *)
        repeat (apply (proj2 (map.disjoint_putmany_l _ _ _)); split);
        first [ assumption | apply (proj1 (map.disjoint_comm _ _)); assumption ]. }
    (* Step 4: list_map for empty return list *)
    cbv [list_map WeakestPrecondition.get].
    split. { reflexivity. }
    split. { reflexivity. }
    (* Step 5: Construct Fp2 output *)
    (* out' = x3 ++ fst_felem x where x3 = -5*xim (opp result),
       fst_felem x = xre (copy result) *)
    pose proof (QuadraticFieldExtensions.AbstractFElem_length _ _ _ Hfe_ore) as Hlen_ore.
    pose proof (QuadraticFieldExtensions.AbstractFElem_length _ _ _ Hfe_oim) as Hlen_oim.
    exists (List.app x3 (fst_felem x)).
    split.
    { (* feval (x3 ++ fst_felem x) = fp2_mul_xi beta xi_re xi_im (feval x) *)
      (* x0 = 2*xim, x1 = 4*xim, x2 = 5*xim, x3 = -x2 = -5*xim *)
      (* fst_felem x = xre (copied to out.im) *)
      (* So out' = (-5*xim, xre) = fp2_mul_xi(-5, 0, 1)(xre, xim) *)
      (* Decompose Fp2 feval into pair of Fp feval using length *)
      assert (Hfeval_out :
        @AbstractField.feval _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep (List.app x3 (fst_felem x)) =
        (@AbstractField.feval _ _ _ _ _ _ bls377_field_representation x3,
         @AbstractField.feval _ _ _ _ _ _ bls377_field_representation (fst_felem x))).
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
      (* Reduce model projections in hypotheses *)
      cbv [AbstractField.bin_model AbstractField.bin_add AbstractField.Fadd
           AbstractField.un_model AbstractField.un_opp AbstractField.Fopp] in H11, H7, H4, H1.
      rewrite H11, H7, H4, H1.
      unfold Fp6.fp2_mul_xi, bls377_xi_re, bls377_xi_im, bls377_beta.
      cbn -[F.add F.opp F.mul F.sub F.zero F.one F.of_Z F.inv F.div
             PrimeField.M_pos feval].
      apply injective_projections; cbn [fst snd].
      - rewrite opp_five_times. ring.
      - ring. }
    split.
    { (* bounded_by loose_bounds (x3 ++ fst_felem x) *)
      unfold AbstractField.bounded_by, bls377_Fp2_rep.
      cbv [QuadraticFieldExtensionsSpecs.Fp2_field_representation
           QuadraticFieldExtensionsSpecs.fst_felem
           QuadraticFieldExtensionsSpecs.snd_felem].
      rewrite (QuadraticFieldExtensions.firstn_app' _ _ _ Hlen_ore).
      rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Hlen_ore).
      cbv [AbstractField.un_outbounds AbstractField.un_opp] in H12.
      split.
      - exact H12. (* opp output has loose_bounds *)
      - exact Hbx_re. (* copy preserves original tight_bounds = loose_bounds *) }
    { (* (FElem pout (x3 ++ fst_felem x) ⋆ Rr) m_rest *)
      (* Join the two Fp halves into one Fp2 FElem *)
      assert (Hjoin : (FElem_Fp pout x3 ⋆
        FElem_Fp (word.add pout (word.of_Z (@AbstractField.felem_size_in_bytes _ _ _ _ _ _ bls377_field_representation))) (fst_felem x))
        (map.putmany m_ore m_oim)).
      { exists m_ore, m_oim. split. { split. { reflexivity. }
        first [assumption | apply (proj1 (map.disjoint_comm _ _)); assumption]. }
        split; [exact Hfe_ore | exact Hfe_oim]. }
      fold_offset.
      pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_join _ _ _ _
        ltac:(exact _) ltac:(exact _) _ _ beta fp2_prefix
        pout x3 (fst_felem x) (map.putmany m_ore m_oim)
        Hlen_ore Hlen_oim Hjoin) as Hfp2_out.
      (* Reconstruct x's Fp2 FElem from Hrest3's components *)
      (* Hrest3 : (FElem_Fp px xre ⋆ (FElem_Fp (px+off) xim ⋆ Rr)) m_rest3 *)
      (* We need: (FElem pout out' ⋆ (FElem px x ⋆ Rr)) (putmany (putmany m_ore m_oim) m_rest3) *)
      exists (map.putmany m_ore m_oim), m_rest3.
      split. { split. { rewrite map.putmany_assoc. reflexivity. }
        apply (proj2 (map.disjoint_putmany_l _ _ _)); split;
        first [assumption | apply (proj1 (map.disjoint_comm _ _)); assumption]. }
      split. { exact Hfp2_out. }
      (* Now: (FElem px x ⋆ Rr) m_rest3 *)
      (* Hrest3 has Fp-level seps. We need Fp2-level FElem px x. *)
      (* Hfx : FElem px x (map.putmany m1 m2) — still valid since m1, m2 unchanged *)
      (* m_rest3 should be = putmany m1 (putmany m2 mRr) *)
      (* Need to show (FElem px x ⋆ Rr) m_rest3 *)
      destruct Hrest3 as [m_xre [m_xim_rr [[? ?] [Hfe_xre Hxim_rr]]]]. subst.
      destruct Hxim_rr as [m_xim [mR [[? ?] [Hfe_xim HrR]]]]. subst.
      saturate_disjointness.
      exists (map.putmany m_xre m_xim), mR.
      split. { split. { rewrite map.putmany_assoc. reflexivity. }
        apply (proj2 (map.disjoint_putmany_l _ _ _)); split;
        first [assumption | apply (proj1 (map.disjoint_comm _ _)); assumption]. }
      split.
      { (* FElem px x (putmany m_xre m_xim) *)
        (* m_xre has FElem_Fp px (fst_felem x), m_xim has FElem_Fp (px+off) (snd_felem x)
           — same content as m1, m2 from the Fp2 split. Rejoin via Fp2_raw_FElem_join. *)
        pose proof (QuadraticFieldExtensions.AbstractFElem_length _ _ _ Hfe_xre) as Hlen_xre.
        pose proof (QuadraticFieldExtensions.AbstractFElem_length _ _ _ Hfe_xim) as Hlen_xim.
        assert (Hjoin_x : (FElem_Fp px (fst_felem x) ⋆
          FElem_Fp (word.add px (word.of_Z (@AbstractField.felem_size_in_bytes _ _ _ _ _ _ bls377_field_representation))) (snd_felem x))
          (map.putmany m_xre m_xim)).
        { exists m_xre, m_xim. split. { split. { reflexivity. }
          first [assumption | apply (proj1 (map.disjoint_comm _ _)); assumption]. }
          split; [exact Hfe_xre | exact Hfe_xim]. }
        fold_offset.
        pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_join _ _ _ _
          ltac:(exact _) ltac:(exact _) _ _ beta fp2_prefix
          px (fst_felem x) (snd_felem x) (map.putmany m_xre m_xim)
          Hlen_xre Hlen_xim Hjoin_x) as Hfx'.
        assert (Hx_eq : x = List.app (fst_felem x) (snd_felem x)).
        { unfold QuadraticFieldExtensionsSpecs.fst_felem, QuadraticFieldExtensionsSpecs.snd_felem.
          symmetry. apply List.firstn_skipn. }
        rewrite Hx_eq. exact Hfx'. }
      exact HrR. }
  Qed.

End P.

(* Standalone feval lemma outside Section for MCP *)
Require Import Bedrock.Field.Synthesis.Examples.bls12_377_prime.

Definition bls377_M : positive := Eval vm_compute in (Z.to_pos bls12_377_prime.m).

Local Definition bls377_ftf := @Algebra.Field.field_theory_for_stdlib_tactic
  (F.F bls377_M) (@eq (F.F bls377_M))
  (@F.zero bls377_M) (@F.one bls377_M)
  (@F.opp bls377_M) (@F.add bls377_M) (@F.mul bls377_M) (@F.sub bls377_M)
  (@F.inv bls377_M) (@F.div bls377_M)
  (@F.field_modulo bls377_M prime_bls12_377).
Local Add Field bls377_ftf_field : bls377_ftf.

Local Lemma opp_five_generic (v : F.F bls377_M) :
  F.opp (F.add (F.add (F.add v v) (F.add v v)) v) =
  F.mul (F.of_Z bls377_M (-5)) v.
Proof.
  change (F.of_Z bls377_M (-5)) with (F.opp (F.of_Z bls377_M 5)).
  change (F.of_Z bls377_M 5) with
    (F.add (F.add (@F.one bls377_M) (@F.one bls377_M))
           (F.add (@F.one bls377_M) (F.add (@F.one bls377_M) (@F.one bls377_M)))).
  ring.
Qed.

Lemma mul_xi_feval_id (a0 a1 : F.F bls377_M) :
  (F.opp (F.add (F.add (F.add a1 a1) (F.add a1 a1)) a1), a0) =
  Fp6.fp2_mul_xi bls377_M (F.of_Z bls377_M (-5)) (@F.zero bls377_M) (@F.one bls377_M) (a0, a1).
Proof.
  unfold Fp6.fp2_mul_xi. cbn [fst snd].
  f_equal.
  - rewrite opp_five_generic. ring.
  - ring.
Qed.
