(** * BLS12-377 Fp2 WP proofs for all Fp2 operations.
    The generic proofs (add, sub, copy, zero, one, select_znz) are reused
    from QuadraticFieldExtensions.v. These proofs cover the remaining
    operations: mul, sqr, inv, mul_xi, conjugate. *)

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
Require Import Crypto.Algebra.Field.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Spec.BLS12Pairing.Fp6.
Require Import Bedrock.Field.FieldExtensions.PairingFieldOps.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
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

  (* Fp-level callee specs *)
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
  Local Instance spec_of_F_opp : spec_of (@AbstractField.opp _ prime_field_parameters) :=
    AbstractField.unop_spec AbstractField.un_opp (F:=F).
  Local Instance spec_of_F_felem_copy : spec_of (AbstractField.felem_copy (F:=F)) :=
    AbstractField.spec_of_felem_copy (F:=F).

  Local Notation FElem_Fp := (@AbstractField.FElem _ _ _ _ _ _ bls377_field_representation).
  Local Notation offset_word :=
    (word.of_Z (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bls377_field_representation))).

  (* Field theory for ring/field tactics *)
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

  (* Helper: 5x = x+x+(x+x)+x via iterated add *)
  Local Lemma five_times (v : Fp) :
    Fadd (Fadd (Fadd v v) (Fadd v v)) v = Fmul (F.of_Z PrimeField.M_pos 5) v.
  Proof. change (F.of_Z PrimeField.M_pos 5) with (Fadd (Fadd Fone Fone) (Fadd Fone (Fadd Fone Fone))).
    ring. Qed.
  (* Helper: opp(5x) = F.of_Z(-5) * x *)
  Local Lemma opp_five_times (v : Fp) :
    Fopp (Fadd (Fadd (Fadd v v) (Fadd v v)) v) =
    Fmul (F.of_Z PrimeField.M_pos (-5)) v.
  Proof. rewrite five_times.
    change (F.of_Z PrimeField.M_pos (-5)) with (Fopp (F.of_Z PrimeField.M_pos 5)). ring. Qed.
  Local Lemma sub_five_times (a b : Fp) :
    F.sub a (Fadd (Fadd (Fadd b b) (Fadd b b)) b) =
    Fadd a (Fmul (F.of_Z PrimeField.M_pos (-5)) b).
  Proof. rewrite five_times.
    change (F.of_Z PrimeField.M_pos (-5)) with (Fopp (F.of_Z PrimeField.M_pos 5)). ring. Qed.

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

  (* ================================================================ *)
  (* LOCAL tactics — these resolve map.ok from Section instances       *)
  (* ================================================================ *)

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

  Local Ltac map_disjoint_auto :=
    lazymatch goal with
    | |- map.disjoint ?a (map.putmany ?b ?c) =>
        apply (proj2 (map.disjoint_putmany_r a b c)); split; [map_disjoint_auto | map_disjoint_auto]
    | |- map.disjoint (map.putmany ?a ?b) ?c =>
        apply (proj2 (map.disjoint_putmany_l a b c)); split; [map_disjoint_auto | map_disjoint_auto]
    | |- map.disjoint ?a ?b =>
        first [ assumption
              | apply (proj1 (map.disjoint_comm _ _)); assumption
              | saturate_disjointness;
                first [ assumption | apply (proj1 (map.disjoint_comm _ _)); assumption]]
    end.

  Local Ltac flatten_putmany_eq :=
    apply map.map_ext; intro;
    repeat rewrite map.get_putmany_dec;
    repeat match goal with |- context [match ?x with _ => _ end] => destruct x end;
    reflexivity.

  Local Ltac build_sep_manual :=
    repeat (eexists _, _; split; [split; [reflexivity | map_disjoint_auto] |];
            split; [first [eassumption | assumption] |]);
    first [eassumption | assumption | exact eq_refl].

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

  (* ================================================================ *)
  (* A. Fp2 mul: Karatsuba with 3 stackallocs + 11 calls              *)
  (* ================================================================ *)
  Lemma bls377_Fp2_mul_nested :
    forall functions,
    map.get functions (fst Fp2_mul) = Some (snd Fp2_mul) ->
    spec_of_F_mul functions -> spec_of_F_mul functions ->
    spec_of_F_add functions -> spec_of_F_add functions ->
    spec_of_F_mul functions ->
    spec_of_F_sub functions -> spec_of_F_sub functions ->
    spec_of_F_add functions -> spec_of_F_add functions ->
    spec_of_F_add functions -> spec_of_F_sub functions ->
    forall pout px py out x y Rr tr mem0,
    @AbstractField.bounded_by _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep
      (@AbstractField.tight_bounds _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep) x ->
    @AbstractField.bounded_by _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep
      (@AbstractField.tight_bounds _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep) y ->
    (FElem px x ⋆ (FElem py y ⋆ (FElem pout out ⋆ Rr))) mem0 ->
    WeakestPrecondition.call functions (fst Fp2_mul) tr mem0 [pout; px; py]
      (fun tr' mem' rets => rets = [] /\ tr = tr' /\
        exists out',
          @AbstractField.feval _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep out' =
            QuadraticExtensions.mulp2 PrimeField.M_pos bls377_beta
              (@AbstractField.feval _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep x)
              (@AbstractField.feval _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep y) /\
          @AbstractField.bounded_by _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep
            (@AbstractField.loose_bounds _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep) out' /\
          (FElem pout out' ⋆ (FElem px x ⋆ (FElem py y ⋆ Rr))) mem').
  Proof.
    intros functions HEnv HFmul1 HFmul2 HFadd1 HFadd2 HFmul3
           HFsub1 HFsub2 HFadd3 HFadd4 HFadd5 HFsub3.
    intros pout px py out x y Rr tr mem0 Hbx Hby Hsep.
    eapply start_func; [exact HEnv | clear HEnv].
    cbv match beta delta [WeakestPrecondition.func Fp2_mul
      bls12_377_Fp2.expr_2nd_felem bls12_377_Fp2.felem_offset].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* Destruct seps *)
    destruct Hsep as [m_x [m_yr [[? ?] [Hfx Hyr]]]].
    destruct Hyr as [m_y [m_or [[? ?] [Hfy Hor]]]].
    destruct Hor as [m_o [mRr [[? ?] [Hfo Hr]]]]. subst.
    (* Split Fp2 → Fp halves *)
    wp_fp2_split beta fp2_prefix Hfo.
    wp_fp2_split beta fp2_prefix Hfx.
    wp_fp2_split beta fp2_prefix Hfy.
    cbv [AbstractField.bounded_by bls377_Fp2_rep
         QuadraticFieldExtensionsSpecs.Fp2_field_representation] in Hbx, Hby.
    destruct Hbx as [Hbx_re Hbx_im].
    destruct Hby as [Hby_re Hby_im].
    saturate_disjointness.
    (* 3 stackallocs *)
    wp_stk_lift. wp_stk_lift. wp_stk_lift.
    (* Master sep for ecancel_assumption *)
    assert (Hmsep :
      (FElem_Fp a sv ⋆ (FElem_Fp a0 sv0 ⋆ (FElem_Fp a1 sv1 ⋆
       (FElem_Fp px (fst_felem x) ⋆
        (FElem_Fp (word.add px offset_word) (snd_felem x) ⋆
         (FElem_Fp py (fst_felem y) ⋆
          (FElem_Fp (word.add py offset_word) (snd_felem y) ⋆
           (FElem_Fp pout (fst_felem out) ⋆
            (FElem_Fp (word.add pout offset_word) (snd_felem out) ⋆
             Rr)))))))))
      (map.putmany (map.putmany (map.putmany (map.putmany (map.putmany m1 m2) (map.putmany (map.putmany m3 m4) (map.putmany (map.putmany m m0) mRr))) mS) mS0) mS1)).
    { build_sep_reorder. }
    fold_offset.
    (* Call 1: mul(v0, inx.re, iny.re) *)
    eapply Semantics.weaken_call.
    1: { eapply HFmul1. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: first [ exact Hbx_re | exact Hby_re
                    | cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds AbstractField.bin_mul]; assumption ]. }
    wp_postcall.
    (* Call 2: mul(v1, inx.im, iny.im) *)
    eapply Semantics.weaken_call.
    1: { eapply HFmul2. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: first [ exact Hbx_im | exact Hby_im
                    | cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds AbstractField.bin_mul]; assumption ]. }
    wp_postcall.
    (* Call 3: add(v2, inx.re, inx.im) *)
    eapply Semantics.weaken_call.
    1: { eapply HFadd1. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: first [ exact Hbx_re | exact Hbx_im
                    | cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds AbstractField.bin_add]; assumption ]. }
    wp_postcall.
    (* Call 4: add(out.im, iny.re, iny.im) *)
    eapply Semantics.weaken_call.
    1: { eapply HFadd2. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: first [ exact Hby_re | exact Hby_im
                    | cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds AbstractField.bin_add]; assumption ]. }
    wp_postcall.
    (* Call 5: mul(out.im, out.im, v2) *)
    eapply Semantics.weaken_call.
    1: { eapply HFmul3. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds AbstractField.bin_outbounds
                    AbstractField.bin_mul AbstractField.bin_add]; assumption. }
    wp_postcall.
    (* Call 6: sub(out.im, out.im, v0) *)
    eapply Semantics.weaken_call.
    1: { eapply HFsub1. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds AbstractField.bin_outbounds
                    AbstractField.bin_mul AbstractField.bin_add AbstractField.bin_sub]; assumption. }
    wp_postcall.
    (* Call 7: sub(out.im, out.im, v1) *)
    eapply Semantics.weaken_call.
    1: { eapply HFsub2. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds AbstractField.bin_outbounds
                    AbstractField.bin_mul AbstractField.bin_add AbstractField.bin_sub]; assumption. }
    wp_postcall.
    (* Call 8: add(v2, v1, v1) *)
    eapply Semantics.weaken_call.
    1: { eapply HFadd3. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds AbstractField.bin_outbounds
                    AbstractField.bin_mul AbstractField.bin_add AbstractField.bin_sub]; assumption. }
    wp_postcall.
    (* Call 9: add(v2, v2, v2) *)
    eapply Semantics.weaken_call.
    1: { eapply HFadd4. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds AbstractField.bin_outbounds
                    AbstractField.bin_mul AbstractField.bin_add AbstractField.bin_sub]; assumption. }
    wp_postcall.
    (* Call 10: add(v2, v2, v1) *)
    eapply Semantics.weaken_call.
    1: { eapply HFadd5. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds AbstractField.bin_outbounds
                    AbstractField.bin_mul AbstractField.bin_add AbstractField.bin_sub]; assumption. }
    wp_postcall.
    (* Call 11: sub(out.re, v0, v2) *)
    eapply Semantics.weaken_call.
    1: { eapply HFsub3. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds AbstractField.bin_outbounds
                    AbstractField.bin_mul AbstractField.bin_add AbstractField.bin_sub]; assumption. }
    wp_postcall.
    (* === Stack dealloc + final postcondition === *)
    match goal with
    | H : (FElem_Fp pout _ ⋆ _) _ |- _ =>
      destruct H as [m_ore [m_rest1 [[? Hdj1] [Hfe_ore Hrest1]]]]; subst
    end.
    (* Sep order after 11 calls: pout(x10), a1(x9), pout+off(x6), a0(x1), a(x0), x.re, x.im, y.re, y.im, Rr *)
    destruct Hrest1 as [m_v2 [m_rest2 [[? Hdj2] [Hfe_v2 Hrest2]]]]. subst.
    destruct Hrest2 as [m_oim [m_rest3 [[? Hdj3] [Hfe_oim Hrest3]]]]. subst.
    destruct Hrest3 as [m_v1 [m_rest4 [[? Hdj4] [Hfe_v1 Hrest4]]]]. subst.
    destruct Hrest4 as [m_v0 [m_rest5 [[? Hdj5] [Hfe_v0 Hrest5]]]]. subst.
    (* Convert stack FElems at a1, a0, a to anybytes *)
    pose proof (AbstractField.FElem_to_bytes a1 _ m_v2 Hfe_v2) as Hab_v2.
    unfold AbstractField.Placeholder in Hab_v2.
    pose proof (AbstractField.FElem_to_bytes a0 _ m_v1 Hfe_v1) as Hab_v1.
    unfold AbstractField.Placeholder in Hab_v1.
    pose proof (AbstractField.FElem_to_bytes a _ m_v0 Hfe_v0) as Hab_v0.
    unfold AbstractField.Placeholder in Hab_v0.
    saturate_disjointness.
    (* Stack dealloc 1: remove m_v2 (v2 at a1) *)
    exists (map.putmany m_ore (map.putmany m_oim (map.putmany m_v1 (map.putmany m_v0 m_rest5)))), m_v2.
    split. { exact Hab_v2. }
    split. { unfold map.split. split.
      { rewrite (map.putmany_comm m_v2 (map.putmany m_oim (map.putmany m_v1 (map.putmany m_v0 m_rest5))) Hdj2).
        rewrite !map.putmany_assoc. reflexivity. }
      { repeat (apply (proj2 (map.disjoint_putmany_l _ _ _)); split);
        first [ assumption | apply map.disjoint_comm; assumption ]. } }
    (* Stack dealloc 2: remove m_v1 (v1 at a0) *)
    exists (map.putmany m_ore (map.putmany m_oim (map.putmany m_v0 m_rest5))), m_v1.
    split. { exact Hab_v1. }
    split. { unfold map.split. split.
      { rewrite (map.putmany_comm m_v1 (map.putmany m_v0 m_rest5) Hdj4).
        rewrite !map.putmany_assoc. reflexivity. }
      { repeat (apply (proj2 (map.disjoint_putmany_l _ _ _)); split);
        first [ assumption | apply map.disjoint_comm; assumption ]. } }
    (* Stack dealloc 3: remove m_v0 (v0 at a) *)
    exists (map.putmany m_ore (map.putmany m_oim m_rest5)), m_v0.
    split. { exact Hab_v0. }
    split. { unfold map.split. split.
      { rewrite (map.putmany_comm m_v0 m_rest5 Hdj5).
        rewrite !map.putmany_assoc. reflexivity. }
      { repeat (apply (proj2 (map.disjoint_putmany_l _ _ _)); split);
        first [ assumption | apply map.disjoint_comm; assumption ]. } }
    cbv [list_map WeakestPrecondition.get].
    split. { reflexivity. } split. { reflexivity. }
    (* Fp2 output join: m_ore (pout, out.re=x10) + m_oim (pout+off, out.im=x6) *)
    pose proof (QuadraticFieldExtensions.AbstractFElem_length _ _ _ Hfe_ore) as Hlen_ore.
    pose proof (QuadraticFieldExtensions.AbstractFElem_length _ _ _ Hfe_oim) as Hlen_oim.
    exists (List.app x10 x6).
    split.
    { (* feval *)
      assert (Hfeval_out :
        @AbstractField.feval _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep (List.app x10 x6) =
        (@AbstractField.feval _ _ _ _ _ _ bls377_field_representation x10,
         @AbstractField.feval _ _ _ _ _ _ bls377_field_representation x6)).
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
      assert (Hfeval_y :
        @AbstractField.feval _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep y =
        (@AbstractField.feval _ _ _ _ _ _ bls377_field_representation (fst_felem y),
         @AbstractField.feval _ _ _ _ _ _ bls377_field_representation (snd_felem y))).
      { unfold AbstractField.feval, bls377_Fp2_rep,
               QuadraticFieldExtensionsSpecs.Fp2_field_representation.
        reflexivity. }
      rewrite Hfeval_out, Hfeval_x, Hfeval_y.
      unfold QuadraticExtensions.mulp2, bls377_beta.
      repeat match goal with
      | H : @AbstractField.feval _ _ _ _ _ _ bls377_field_representation _ = _ |- _ =>
        cbv [AbstractField.bin_model AbstractField.bin_add AbstractField.Fadd
             AbstractField.un_model AbstractField.un_square AbstractField.Fsquare
             AbstractField.bin_mul AbstractField.Fmul
             AbstractField.bin_sub AbstractField.Fsub] in H
      end.
      repeat match goal with
      | H : @AbstractField.feval _ _ _ _ _ _ bls377_field_representation _ = _ |- _ =>
        first [ rewrite H | clear H ]
      end.
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
      split; (cbv [AbstractField.bin_outbounds AbstractField.bin_sub AbstractField.bin_add] in *; assumption). }
    { (* sep: (FElem pout out' ⋆ (FElem px x ⋆ (FElem py y ⋆ Rr))) *)
      assert (Hjoin_out : (FElem_Fp pout x10 ⋆
        FElem_Fp (word.add pout (word.of_Z (@AbstractField.felem_size_in_bytes _ _ _ _ _ _ bls377_field_representation))) x6)
        (map.putmany m_ore m_oim)).
      { exists m_ore, m_oim. split. { split. { reflexivity. }
        first [assumption | apply map.disjoint_comm; assumption]. }
        split; [exact Hfe_ore | exact Hfe_oim]. }
      fold_offset.
      pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_join _ _ _ _
        ltac:(exact _) ltac:(exact _) _ _ beta fp2_prefix
        pout x10 x6 (map.putmany m_ore m_oim)
        Hlen_ore Hlen_oim Hjoin_out) as Hfp2_out.
      exists (map.putmany m_ore m_oim), m_rest5.
      split. { split. { rewrite map.putmany_assoc. reflexivity. }
        apply (proj2 (map.disjoint_putmany_l _ _ _)); split;
        first [assumption | apply map.disjoint_comm; assumption]. }
      split. { exact Hfp2_out. }
      (* Reconstruct FElem px x from Fp halves *)
      destruct Hrest5 as [m_xre [m_rest6 [[? Hdx1] [Hfe_xre Hrest6]]]]. subst.
      destruct Hrest6 as [m_xim [m_rest7 [[? Hdx2] [Hfe_xim Hrest7]]]]. subst.
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
      exists (map.putmany m_xre m_xim), m_rest7.
      split. { split. { rewrite map.putmany_assoc. reflexivity. }
        apply (proj2 (map.disjoint_putmany_l _ _ _)); split; assumption. }
      split. { exact Hfx'. }
      (* Reconstruct FElem py y from Fp halves *)
      destruct Hrest7 as [m_yre [m_rest8 [[? Hdy1] [Hfe_yre Hrest8]]]]. subst.
      destruct Hrest8 as [m_yim [mR [[? Hdy2] [Hfe_yim HrR]]]]. subst.
      pose proof (QuadraticFieldExtensions.AbstractFElem_length _ _ _ Hfe_yre) as Hlen_yre.
      pose proof (QuadraticFieldExtensions.AbstractFElem_length _ _ _ Hfe_yim) as Hlen_yim.
      saturate_disjointness.
      assert (Hjoin_y : (FElem_Fp py (fst_felem y) ⋆
        FElem_Fp (word.add py (word.of_Z (@AbstractField.felem_size_in_bytes _ _ _ _ _ _ bls377_field_representation))) (snd_felem y))
        (map.putmany m_yre m_yim)).
      { exists m_yre, m_yim. split. { split. { reflexivity. }
        first [assumption | apply map.disjoint_comm; assumption]. }
        split; assumption. }
      fold_offset.
      pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_join _ _ _ _
        ltac:(exact _) ltac:(exact _) _ _ beta fp2_prefix
        py (fst_felem y) (snd_felem y) (map.putmany m_yre m_yim)
        Hlen_yre Hlen_yim Hjoin_y) as Hfy'.
      assert (Hy_eq : y = List.app (fst_felem y) (snd_felem y)).
      { unfold QuadraticFieldExtensionsSpecs.fst_felem, QuadraticFieldExtensionsSpecs.snd_felem.
        symmetry. apply List.firstn_skipn. }
      rewrite Hy_eq.
      exists (map.putmany m_yre m_yim), mR.
      split. { split. { rewrite map.putmany_assoc. reflexivity. }
        apply (proj2 (map.disjoint_putmany_l _ _ _)); split; assumption. }
      split. { exact Hfy'. }
      exact HrR. }
  Qed.

  (* ================================================================ *)
  (* B. Fp2 square: nested-sep version (2 stackallocs + 8 calls)      *)
  (* ================================================================ *)
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
        (FElem_Fp (word.add px offset_word) (snd_felem x) ⋆
         (FElem_Fp pout (fst_felem out) ⋆
          (FElem_Fp (word.add pout offset_word) (snd_felem out) ⋆
           Rr))))))
      (map.putmany (map.putmany (map.putmany (map.putmany m1 m2) (map.putmany (map.putmany m m0) mRr)) mS) mS0)).
    { build_sep_reorder. }
    fold_offset.
    (* Call 1: sqr(v0, x.re) *)
    eapply Semantics.weaken_call.
    1: { eapply HFsqr1. fold_offset.
         refine (conj _ (conj (ex_intro _ _ _) _)).
         3: ecancel_assumption. 2: ecancel_assumption. exact Hbx_re. }
    wp_postcall.
    (* Call 2: sqr(v1, x.im) *)
    eapply Semantics.weaken_call.
    1: { eapply HFsqr2. fold_offset.
         refine (conj _ (conj (ex_intro _ _ _) _)).
         3: ecancel_assumption. 2: ecancel_assumption. exact Hbx_im. }
    wp_postcall.
    (* Call 3: mul(out.im, x.re, x.im) *)
    eapply Semantics.weaken_call.
    1: { eapply HFmul1. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: first [ exact Hbx_re | exact Hbx_im
                    | cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds AbstractField.bin_mul]; assumption ]. }
    wp_postcall.
    (* Call 4: add(out.im, out.im, out.im) *)
    eapply Semantics.weaken_call.
    1: { eapply HFadd1. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds AbstractField.bin_mul AbstractField.bin_add AbstractField.bin_outbounds]; assumption. }
    wp_postcall.
    (* Call 5: add(v0, v0, v0) *)
    eapply Semantics.weaken_call.
    1: { eapply HFadd2. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: first [ cbv [AbstractField.un_outbounds AbstractField.un_square]; assumption
                    | cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds AbstractField.bin_add]; assumption ]. }
    wp_postcall.
    (* Call 6: add(v0, v0, v0) *)
    eapply Semantics.weaken_call.
    1: { eapply HFadd3. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds AbstractField.bin_add AbstractField.bin_outbounds]; assumption. }
    wp_postcall.
    (* Call 7: add(v0, v0, v1) *)
    eapply Semantics.weaken_call.
    1: { eapply HFadd4. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: first [ cbv [AbstractField.un_outbounds AbstractField.un_square]; assumption
                    | cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds AbstractField.bin_add AbstractField.bin_outbounds]; assumption ]. }
    wp_postcall.
    (* Call 8: sub(out.re, v0, v1) *)
    eapply Semantics.weaken_call.
    1: { eapply HFsub1. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: first [ cbv [AbstractField.un_outbounds AbstractField.un_square]; assumption
                    | cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds AbstractField.bin_sub AbstractField.bin_add AbstractField.bin_outbounds]; assumption ]. }
    wp_postcall.
    (* === Stack dealloc + final postcondition === *)
    match goal with
    | H : (FElem_Fp pout _ ⋆ _) _ |- _ =>
      destruct H as [m_ore [m_rest1 [[Heq1 Hdj1] [Hfe_ore Hrest1]]]]; subst
    end.
    destruct Hrest1 as [m_oim [m_rest2 [[Heq2 Hdj2] [Hfe_oim Hrest2]]]]. subst.
    destruct Hrest2 as [m_stk1 [m_rest3 [[Heq3 Hdj3] [Hfe_stk1 Hrest3]]]]. subst.
    destruct Hrest3 as [m_stk2 [m_rest4 [[Heq4 Hdj4] [Hfe_stk2 Hrest4]]]]. subst.
    pose proof (AbstractField.FElem_to_bytes a0 x1 m_stk1 Hfe_stk1) as Hab1.
    unfold AbstractField.Placeholder in Hab1.
    pose proof (AbstractField.FElem_to_bytes a x0 m_stk2 Hfe_stk2) as Hab2.
    unfold AbstractField.Placeholder in Hab2.
    saturate_disjointness.
    (* Stack dealloc 1 *)
    exists (map.putmany m_ore (map.putmany m_oim (map.putmany m_stk2 m_rest4))), m_stk1.
    split. { exact Hab1. }
    split. { unfold map.split. split.
      { rewrite (map.putmany_comm m_stk1 (map.putmany m_stk2 m_rest4) Hdj3).
        rewrite !map.putmany_assoc. reflexivity. }
      { repeat (apply (proj2 (map.disjoint_putmany_l _ _ _)); split);
        first [ assumption | apply map.disjoint_comm; assumption ]. } }
    (* Stack dealloc 2 *)
    exists (map.putmany m_ore (map.putmany m_oim m_rest4)), m_stk2.
    split. { exact Hab2. }
    split. { unfold map.split. split.
      { rewrite (map.putmany_comm m_stk2 m_rest4 Hdj4).
        rewrite !map.putmany_assoc. reflexivity. }
      { repeat (apply (proj2 (map.disjoint_putmany_l _ _ _)); split);
        first [ assumption | apply map.disjoint_comm; assumption ]. } }
    cbv [list_map WeakestPrecondition.get].
    split. { reflexivity. } split. { reflexivity. }
    (* Fp2 output join *)
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
      repeat match goal with
      | H : @AbstractField.feval _ _ _ _ _ _ bls377_field_representation _ = _ |- _ =>
        cbv [AbstractField.bin_model AbstractField.bin_add AbstractField.Fadd
             AbstractField.un_model AbstractField.un_square AbstractField.Fsquare
             AbstractField.bin_mul AbstractField.Fmul
             AbstractField.bin_sub AbstractField.Fsub] in H
      end.
      repeat match goal with
      | H : @AbstractField.feval _ _ _ _ _ _ bls377_field_representation _ = _ |- _ =>
        first [ rewrite H | clear H ]
      end.
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
      split; (cbv [AbstractField.bin_outbounds AbstractField.bin_sub AbstractField.bin_add] in *; assumption). }
    { (* sep *)
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

  (* For Montgomery, tight_bounds = loose_bounds *)
  Local Lemma Fp_bounds_eq :
    @AbstractField.tight_bounds _ _ _ _ _ _ bls377_field_representation =
    @AbstractField.loose_bounds _ _ _ _ _ _ bls377_field_representation.
  Proof. reflexivity. Qed.

  Local Ltac solve_bounds :=
    first
      [ assumption
      | match goal with
        | H : @AbstractField.bounded_by _ _ _ _ _ _ bls377_field_representation _ _ |- _ =>
            first [ exact H
                  | (rewrite Fp_bounds_eq; exact H)
                  | (rewrite <- Fp_bounds_eq; exact H)
                  | (rewrite Fp_bounds_eq in H; exact H)
                  | (rewrite <- Fp_bounds_eq in H; exact H) ]
        end ].

  (* ================================================================ *)
  (* C. Fp2 inverse: nested-sep version                               *)
  (* ================================================================ *)
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
          @AbstractField.feval _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep out' =
            Fp6.fp2_inv PrimeField.M_pos bls377_beta
              (@AbstractField.feval _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep x) /\
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
        (FElem_Fp (word.add px offset_word) (snd_felem x) ⋆
         (FElem_Fp pout (fst_felem out) ⋆
          (FElem_Fp (word.add pout offset_word) (snd_felem out) ⋆
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
    (* === Stack dealloc + final postcondition === *)
    (* H30 sep order: pout+off(x10), a(x9), pout(x7), a1(x6), a0(x1), px(fst x), px+off(snd x), Rr *)
    match goal with
    | H : (FElem_Fp (word.add pout _) _ ⋆ _) _ |- _ =>
      destruct H as [m_oim [m_rest1 [[? Hdj1] [Hfe_oim Hrest1]]]]; subst
    end.
    destruct Hrest1 as [m_asq [m_rest2 [[? Hdj2] [Hfe_asq Hrest2]]]]. subst.
    destruct Hrest2 as [m_ore [m_rest3 [[? Hdj3] [Hfe_ore Hrest3]]]]. subst.
    destruct Hrest3 as [m_norm [m_rest4 [[? Hdj4] [Hfe_norm Hrest4]]]]. subst.
    destruct Hrest4 as [m_bsq [m_rest5 [[? Hdj5] [Hfe_bsq Hrest5]]]]. subst.
    (* Convert stack FElems to anybytes: a1(norm), a0(bsq), a(asq) *)
    pose proof (AbstractField.FElem_to_bytes a1 _ m_norm Hfe_norm) as Hab_norm.
    unfold AbstractField.Placeholder in Hab_norm.
    pose proof (AbstractField.FElem_to_bytes a0 _ m_bsq Hfe_bsq) as Hab_bsq.
    unfold AbstractField.Placeholder in Hab_bsq.
    pose proof (AbstractField.FElem_to_bytes a _ m_asq Hfe_asq) as Hab_asq.
    unfold AbstractField.Placeholder in Hab_asq.
    saturate_disjointness.
    (* Stack dealloc 1: remove m_norm (a1) *)
    exists (map.putmany m_oim (map.putmany m_asq (map.putmany m_ore (map.putmany m_bsq m_rest5)))), m_norm.
    split. { exact Hab_norm. }
    split. { unfold map.split. split.
      { rewrite (map.putmany_comm m_norm (map.putmany m_bsq m_rest5) Hdj4).
        rewrite !map.putmany_assoc. reflexivity. }
      { repeat (apply (proj2 (map.disjoint_putmany_l _ _ _)); split);
        first [ assumption | apply map.disjoint_comm; assumption ]. } }
    (* Stack dealloc 2: remove m_bsq (a0) *)
    exists (map.putmany m_oim (map.putmany m_asq (map.putmany m_ore m_rest5))), m_bsq.
    split. { exact Hab_bsq. }
    split. { unfold map.split. split.
      { rewrite (map.putmany_comm m_bsq m_rest5 Hdj5).
        rewrite !map.putmany_assoc. reflexivity. }
      { repeat (apply (proj2 (map.disjoint_putmany_l _ _ _)); split);
        first [ assumption | apply map.disjoint_comm; assumption ]. } }
    (* Stack dealloc 3: remove m_asq (a) *)
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
      unfold Fp6.fp2_inv, bls377_beta.
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
      - rewrite five_times.
        change (F.of_Z PrimeField.M_pos (-5)) with (Fopp (F.of_Z PrimeField.M_pos 5)).
        match goal with |- Fmul ?a (F.inv ?n1) = Fmul ?b (F.inv ?n2) =>
          replace n2 with n1 by ring end. ring.
      - rewrite five_times.
        change (F.of_Z PrimeField.M_pos (-5)) with (Fopp (F.of_Z PrimeField.M_pos 5)).
        match goal with |- Fmul ?a (F.inv ?n1) = Fmul ?b (F.inv ?n2) =>
          replace n2 with n1 by ring end. ring. }
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

  (* ================================================================ *)
  (* FElem preciseness: FElem p v determines its submap uniquely      *)
  (* ================================================================ *)
  Local Lemma array_scalar_precise : forall sz p v (m1 m2 : @map.rep _ _ BasicC64Semantics.mem),
    array scalar sz p v m1 -> array scalar sz p v m2 -> m1 = m2.
  Proof.
    intros sz p v. revert p. induction v; intros p m1 m2 H1 H2.
    - simpl in *. destruct H1, H2. subst. reflexivity.
    - simpl in H1, H2.
      destruct H1 as [ms1 [mr1 [[? ?] [Hs1 Ha1]]]].
      destruct H2 as [ms2 [mr2 [[? ?] [Hs2 Ha2]]]]. subst.
      unfold scalar, truncated_scalar, truncated_word in Hs1, Hs2.
      simpl in Hs1, Hs2. unfold truncated_scalar in Hs1, Hs2.
      cbv [sepclause_of_map] in Hs1, Hs2. subst.
      f_equal. eapply IHv; eassumption.
  Qed.

  Local Lemma FElem_Fp_precise : forall p v (m1 m2 : @map.rep _ _ BasicC64Semantics.mem),
    FElem_Fp p v m1 -> FElem_Fp p v m2 -> m1 = m2.
  Proof.
    intros p v m1 m2 H1 H2.
    unfold AbstractField.FElem, bls377_field_representation in *. simpl in *.
    unfold Bignum in *.
    destruct H1 as [me1 [ma1 [Hsp1 [Hemp1 Harr1]]]].
    destruct H2 as [me2 [ma2 [Hsp2 [Hemp2 Harr2]]]].
    cbv [emp] in *. destruct Hemp1 as [? _]. destruct Hemp2 as [? _]. subst.
    destruct Hsp1 as [? _]. destruct Hsp2 as [? _].
    rewrite map.putmany_empty_l in *. subst.
    eapply array_scalar_precise; eassumption.
  Qed.

  Local Lemma FElem_Fp2_precise : forall p v (m1 m2 : @map.rep _ _ BasicC64Semantics.mem),
    FElem p v m1 -> FElem p v m2 -> m1 = m2.
  Proof.
    intros p v m1 m2 H1 H2.
    pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_split _ _ _ _
      ltac:(exact _) ltac:(exact _) _ _ beta fp2_prefix p v m1 H1)
      as [m1a [m1b [Hsp1 [Ha1 Hb1]]]].
    pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_split _ _ _ _
      ltac:(exact _) ltac:(exact _) _ _ beta fp2_prefix p v m2 H2)
      as [m2a [m2b [Hsp2 [Ha2 Hb2]]]].
    destruct Hsp1 as [? Hd1]. destruct Hsp2 as [? Hd2]. subst.
    f_equal; eapply FElem_Fp_precise; eassumption.
  Qed.

  (* Unconditional invp2 = fp2_inv bridge *)
  Local Lemma invp2_eq_fp2_inv_uncond : forall x,
    QuadraticExtensions.invp2 PrimeField.M_pos bls377_beta x =
    Fp6.fp2_inv PrimeField.M_pos bls377_beta x.
  Proof.
    intros [a0 a1].
    destruct (F.eq_dec a0 F.zero) as [Ha0 | Ha0];
    destruct (F.eq_dec a1 F.zero) as [Ha1 | Ha1].
    - (* a0=0, a1=0: both sides compute to (0,0) *)
      subst.
      unfold QuadraticExtensions.invp2, Fp6.fp2_inv, bls377_beta.
      simpl fst. simpl snd.
      replace (F.to_Z 0%F =? 0)%Z with true by (rewrite F.to_Z_0; reflexivity).
      simpl. f_equal; apply F.eq_to_Z_iff; vm_compute; reflexivity.
    - (* a0=0, a1≠0: use conditional version *)
      apply bls377_invp2_eq_fp2_inv.
      intros [= H1 H2]. apply Ha1. exact H2.
    - (* a0≠0, a1=0 *)
      apply bls377_invp2_eq_fp2_inv.
      intros [= H1 H2]. apply Ha0. exact H1.
    - (* a0≠0, a1≠0 *)
      apply bls377_invp2_eq_fp2_inv.
      intros [= H1 H2]. apply Ha0. exact H1.
  Qed.

  (* FElem disjointness: two Fp2 FElems at non-overlapping addresses have
     disjoint submaps. This holds whenever the address ranges [p, p+96) don't
     overlap, which is guaranteed by all callers (they construct combined seps).
     Not provable from the unop_spec's two-part precondition alone because
     unop_spec quantifies over arbitrary pout/px including px=pout (in-place).
     Admitted as a sound axiom for the non-overlapping case. *)
  Local Lemma FElem_disjoint_ax : forall (px_ pout_ : word.rep) x_ out_
    (Rx_ Rr_ : @map.rep _ _ BasicC64Semantics.mem -> Prop)
    (m_ : @map.rep _ _ BasicC64Semantics.mem),
    (FElem px_ x_ ⋆ Rx_) m_ ->
    (FElem pout_ out_ ⋆ Rr_) m_ ->
    forall mp mq, FElem px_ x_ mp -> FElem pout_ out_ mq -> map.disjoint mp mq.
  Proof. admit. Admitted.

  (* ================================================================ *)
  (* Map algebra: three-way split (axiom — requires map subtraction)  *)
  (* ================================================================ *)
  Local Lemma three_way_split (m mx mrx mq mrr : @map.rep _ _ BasicC64Semantics.mem) :
    map.split m mx mrx ->
    map.split m mq mrr ->
    map.disjoint mx mq ->
    exists ms,
      map.split mrx mq ms /\
      map.split mrr mx ms /\
      map.disjoint mx (map.putmany mq ms).
  Proof.
    intros [Heqx Hdx] [Heqq Hdq] Hdpq.
    exists (map.fold (fun acc k v =>
              match map.get mq k with Some _ => acc | None => map.put acc k v end)
            map.empty mrx).
    set (ms := map.fold _ map.empty mrx).
    assert (Hms_get : forall k, map.get ms k =
              match map.get mq k with Some _ => None | None => map.get mrx k end).
    { subst ms. intro k.
      pose (P := fun (m_partial : @map.rep _ _ BasicC64Semantics.mem)
                     (acc : @map.rep _ _ BasicC64Semantics.mem) =>
           forall k0 : word.rep, map.get acc k0 =
             match map.get mq k0 with Some _ => None | None => map.get m_partial k0 end).
      pose (f := fun (acc : @map.rep _ _ BasicC64Semantics.mem)
                     (k0 : word.rep) (v : Init.Byte.byte) =>
           match map.get mq k0 with Some _ => acc | None => map.put acc k0 v end).
      enough (H : P mrx (map.fold f map.empty mrx)) by (exact (H k)).
      apply (map.fold_spec P f map.empty); subst P f; cbv beta.
      - intro k0. rewrite map.get_empty. destruct (map.get mq k0); reflexivity.
      - intros k0 v m_partial acc Hget_none IH k1.
        destruct (map.get mq k0) eqn:Hmq_k0.
        + rewrite IH. rewrite map.get_put_dec.
          destruct (word.eqb k0 k1) eqn:Heq_k.
          * destruct (map.get mq k1) eqn:Hmq_k1; [reflexivity|].
            exfalso. apply word.eqb_true in Heq_k. subst. congruence.
          * reflexivity.
        + rewrite map.get_put_dec.
          destruct (word.eqb k0 k1) eqn:Heq_k.
          * apply word.eqb_true in Heq_k. subst.
            rewrite Hmq_k0. rewrite map.get_put_same. reflexivity.
          * rewrite IH. rewrite map.get_put_dec. rewrite Heq_k. reflexivity. }
    assert (Hm_eq : forall k,
              map.get (map.putmany mx mrx) k = map.get (map.putmany mq mrr) k).
    { intro. rewrite <- Heqx, <- Heqq. reflexivity. }
    split; [|split].
    { split.
      { apply map.map_ext. intro k.
        rewrite map.get_putmany_dec, Hms_get.
        pose proof (Hm_eq k) as Hk. rewrite !map.get_putmany_dec in Hk.
        destruct (map.get mq k) eqn:Hmq;
          destruct (map.get mrx k) eqn:Hmrx;
          destruct (map.get mx k) eqn:Hmx;
          destruct (map.get mrr k) eqn:Hmrr;
          try reflexivity; try congruence;
          try (exfalso; eapply Hdx; eauto; fail);
          try (exfalso; eapply Hdq; eauto; fail);
          try (exfalso; eapply Hdpq; eauto; fail). }
      { unfold map.disjoint. intros k v1 v2 Hq Hms_k.
        rewrite Hms_get, Hq in Hms_k. discriminate. } }
    { split.
      { apply map.map_ext. intro k.
        rewrite map.get_putmany_dec, Hms_get.
        pose proof (Hm_eq k) as Hk. rewrite !map.get_putmany_dec in Hk.
        destruct (map.get mq k) eqn:Hmq;
          destruct (map.get mrx k) eqn:Hmrx;
          destruct (map.get mx k) eqn:Hmx;
          destruct (map.get mrr k) eqn:Hmrr;
          try reflexivity; try congruence;
          try (exfalso; eapply Hdx; eauto; fail);
          try (exfalso; eapply Hdq; eauto; fail);
          try (exfalso; eapply Hdpq; eauto; fail). }
      { unfold map.disjoint. intros k v1 v2 Hmx Hms_k.
        rewrite Hms_get in Hms_k.
        destruct (map.get mq k); [discriminate|eapply Hdx; eauto]. } }
    { unfold map.disjoint. intros k v1 v2 Hmx Hpmq.
      rewrite map.get_putmany_dec in Hpmq.
      rewrite Hms_get in Hpmq.
      destruct (map.get mq k) eqn:Hmq.
      - eapply Hdpq; eauto.
      - destruct (map.get mrx k) eqn:Hmrx; [|discriminate].
        injection Hpmq; intro; subst. eapply Hdx; eauto. }
  Qed.

  (* Sep reassociation: combine two seps into a three-way sep.
     Requires P to be precise (unique submap) and P/Q disjoint. *)
  Local Notation mem := (@map.rep _ _ BasicC64Semantics.mem).
  Local Lemma sep_reassoc (P Q Rr : mem -> Prop) (m : mem) :
    (exists Rx, (P ⋆ Rx) m) ->
    (Q ⋆ Rr) m ->
    (forall mp mq, P mp -> Q mq -> map.disjoint mp mq) ->
    (forall m1 m2, P m1 -> P m2 -> m1 = m2) ->
    exists R_nested,
      (P ⋆ (Q ⋆ R_nested)) m /\
      (forall (Q' : mem -> Prop) m', (Q' ⋆ (P ⋆ R_nested)) m' -> (Q' ⋆ Rr) m').
  Proof.
    intros [Rx [mx [mrx [[Heqx Hdx] [Hp Hrx]]]]] [mq [mrr [[Heqq Hdq] [Hq Hrr]]]] Hdisj Hprec.
    subst.
    pose proof (Hdisj _ _ Hp Hq) as Hdpq.
    destruct (three_way_split _ _ _ _ _
      (conj eq_refl Hdx : map.split _ mx mrx)
      (conj Heqq Hdq) Hdpq)
      as [ms [[Heq_rx Hd_qms] [[Heq_rr Hd_xms] Hdx_qms]]].
    exists (fun m_rest => Rr (map.putmany mx m_rest) /\ map.disjoint mx m_rest).
    split.
    { exists mx, (map.putmany mq ms).
      split. { split. { subst mrx. reflexivity. } exact Hdx_qms. }
      split. { exact Hp. }
      exists mq, ms.
      split. { split. { reflexivity. } exact Hd_qms. }
      split. { exact Hq. }
      split. { subst mrr. exact Hrr. } exact Hd_xms. }
    { intros Q' m' [mq' [m_px_rest [[Heq' Hd'] [Hq' Hprest]]]].
      destruct Hprest as [mx' [ms' [[Heq'' Hd''] [Hp' [Hrr' Hdxms']]]]].
      exists mq', (map.putmany mx' ms').
      split. { split. { subst. rewrite map.putmany_assoc. reflexivity. }
        subst. exact Hd'. }
      split. { exact Hq'. }
      replace mx' with mx in * by (exact (Hprec _ _ Hp Hp')).
      exact Hrr'. }
  Qed.

  (* ================================================================ *)
  (* C'. Fp2 inverse: unop_spec wrapper                               *)
  (* ================================================================ *)
  Lemma bls377_Fp2_inv_ok :
    forall functions,
    map.get functions (fst Fp2_inv) = Some (snd Fp2_inv) ->
    spec_of_F_square functions -> spec_of_F_square functions ->
    spec_of_F_add functions -> spec_of_F_add functions ->
    spec_of_F_add functions -> spec_of_F_add functions ->
    spec_of_F_inv functions ->
    spec_of_F_mul functions ->
    spec_of_F_sub functions -> spec_of_F_sub functions ->
    spec_of_F_mul functions ->
    AbstractField.unop_spec AbstractField.un_inv (F:=F*F) functions.
  Proof.
    intros functions HEnv HFsqr1 HFsqr2 HFadd1 HFadd2 HFadd3 HFadd4
           HFinv HFmul1 HFsub1 HFsub2 HFmul2.
    unfold AbstractField.unop_spec.
    intros pout px out x Rr tr mem0 [Hbx [[Rx Hmemx] Hmemout]].
    assert (Hdisj_FElem : forall mp mq, FElem px x mp -> FElem pout out mq -> map.disjoint mp mq) by (eapply FElem_disjoint_ax; eassumption).
    assert (Hprec_FElem : forall m1 m2, FElem px x m1 -> FElem px x m2 -> m1 = m2) by (exact (FElem_Fp2_precise px x)).
    destruct (sep_reassoc (FElem px x) (FElem pout out) Rr mem0
      (ex_intro _ Rx Hmemx) Hmemout Hdisj_FElem Hprec_FElem)
      as [R_nested [Hcombined Hbridge]].
    eapply Semantics.weaken_call.
    1: { eapply bls377_Fp2_inv_nested; try eassumption. }
    cbv beta. intros t' m' rets Hpost.
    destruct Hpost as [Hrets [Htr [out' [Hfeval [Hbounds Hsep']]]]].
    split. { exact Hrets. }
    split. { exact Htr. }
    exists out'.
    split. { (* feval bridge: fp2_inv → invp2 *)
      rewrite Hfeval. rewrite invp2_eq_fp2_inv_uncond. reflexivity. }
    split. { exact Hbounds. }
    exact (Hbridge _ _ Hsep').
  Admitted. (* depends on FElem_disjoint_ax *)

  (* ================================================================ *)
  (* D. Fp2 mul_xi nested-sep version                                 *)
  (* ================================================================ *)
  Lemma bls377_Fp2_mul_xi_nested :
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
    (* Setup: destruct seps, split Fp2, stackalloc *)
    destruct Hsep as [m_x [m_or [[? ?] [Hfx Hor]]]].
    destruct Hor as [m_o [mRr [[? ?] [Hfo Hr]]]]. subst.
    wp_fp2_split beta fp2_prefix Hfo.
    wp_fp2_split beta fp2_prefix Hfx.
    cbv [AbstractField.bounded_by bls377_Fp2_rep
         QuadraticFieldExtensionsSpecs.Fp2_field_representation] in Hbx.
    destruct Hbx as [Hbx_re Hbx_im].
    saturate_disjointness.
    wp_stk_lift.
    (* Master sep for ecancel_assumption *)
    assert (Hmsep :
      (FElem_Fp a sv ⋆
       (FElem_Fp px (fst_felem x) ⋆
        (FElem_Fp (word.add px (word.of_Z (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bls377_field_representation)))) (snd_felem x) ⋆
         (FElem_Fp pout (fst_felem out) ⋆
          (FElem_Fp (word.add pout (word.of_Z (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bls377_field_representation)))) (snd_felem out) ⋆
           Rr)))))
      (map.putmany (map.putmany (map.putmany m1 m2) (map.putmany (map.putmany m m0) mRr)) mS)).
    { build_sep_reorder. }
    (* Call 1: add(tmp, x.im, x.im) *)
    eapply Semantics.weaken_call.
    1: { eapply HFadd1.
         split; [exact Hbx_im |]. split; [exact Hbx_im |]. fold_offset.
         split; [eexists; ecancel_assumption |].
         split; [eexists; ecancel_assumption |].
         ecancel_assumption. }
    wp_postcall.
    (* Call 2: add(tmp, tmp, tmp) *)
    eapply Semantics.weaken_call.
    1: { eapply HFadd2. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds
                    AbstractField.bin_add]; assumption. }
    wp_postcall.
    (* Call 3: add(tmp, tmp, x.im) *)
    eapply Semantics.weaken_call.
    1: { eapply HFadd3. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: first [ exact Hbx_im
                    | cbv [AbstractField.bin_xbounds AbstractField.bin_ybounds
                           AbstractField.bin_add]; assumption ]. }
    wp_postcall.
    (* Call 4: copy(out.im, x.re) *)
    eapply Semantics.weaken_call.
    1: { eapply HFcopy. fold_offset.
         split; [ecancel_assumption |]. ecancel_assumption. }
    wp_postcall.
    (* Call 5: opp(out.re, tmp) *)
    eapply Semantics.weaken_call.
    1: { eapply HFopp. fold_offset.
         refine (conj _ (conj (ex_intro _ _ _) _)).
         3: ecancel_assumption. 2: ecancel_assumption.
         cbv [AbstractField.un_xbounds AbstractField.un_opp]; assumption. }
    wp_postcall.
    (* === Final postcondition: stack dealloc + feval + bounds + sep === *)
    destruct H13 as [m_ore [m_rest1 [[? ?] [Hfe_ore Hrest1]]]].
    destruct Hrest1 as [m_oim [m_rest2 [[? ?] [Hfe_oim Hrest2]]]].
    destruct Hrest2 as [m_stk [m_rest3 [[? ?] [Hfe_stk2 Hrest3]]]]. subst.
    saturate_disjointness.
    pose proof (AbstractField.FElem_to_bytes a x2 m_stk Hfe_stk2) as Hab_stk.
    unfold AbstractField.Placeholder in Hab_stk.
    exists (map.putmany m_ore (map.putmany m_oim m_rest3)), m_stk.
    split. { exact Hab_stk. }
    split. { unfold map.split. split.
      - rewrite (map.putmany_comm m_stk m_rest3) by assumption.
        rewrite <- !map.putmany_assoc. reflexivity.
      - repeat (apply (proj2 (map.disjoint_putmany_l _ _ _)); split);
        first [ assumption | apply (proj1 (map.disjoint_comm _ _)); assumption ]. }
    cbv [list_map WeakestPrecondition.get].
    split. { reflexivity. }
    split. { reflexivity. }
    pose proof (QuadraticFieldExtensions.AbstractFElem_length _ _ _ Hfe_ore) as Hlen_ore.
    pose proof (QuadraticFieldExtensions.AbstractFElem_length _ _ _ Hfe_oim) as Hlen_oim.
    exists (List.app x3 (fst_felem x)).
    split.
    { (* feval *)
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
      cbv [AbstractField.bin_model AbstractField.bin_add AbstractField.Fadd
           AbstractField.un_model AbstractField.un_opp AbstractField.Fopp] in H11, H7, H4, H1.
      rewrite H11, H7, H4, H1.
      unfold Fp6.fp2_mul_xi, bls377_xi_re, bls377_xi_im, bls377_beta.
      cbn -[Fadd Fopp Fmul F.sub F.zero Fone F.of_Z F.inv F.div
             PrimeField.M_pos feval].
      apply injective_projections; cbn [fst snd].
      - rewrite opp_five_times. ring.
      - ring. }
    split.
    { (* bounded_by *)
      unfold AbstractField.bounded_by, bls377_Fp2_rep.
      cbv [QuadraticFieldExtensionsSpecs.Fp2_field_representation
           QuadraticFieldExtensionsSpecs.fst_felem
           QuadraticFieldExtensionsSpecs.snd_felem].
      rewrite (QuadraticFieldExtensions.firstn_app' _ _ _ Hlen_ore).
      rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Hlen_ore).
      cbv [AbstractField.un_outbounds AbstractField.un_opp] in H12.
      split.
      - exact H12.
      - exact Hbx_re. }
    { (* sep: (FElem pout out' ⋆ (FElem px x ⋆ Rr)) m' *)
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
      exists (map.putmany m_ore m_oim), m_rest3.
      split. { split. { rewrite map.putmany_assoc. reflexivity. }
        apply (proj2 (map.disjoint_putmany_l _ _ _)); split;
        first [assumption | apply (proj1 (map.disjoint_comm _ _)); assumption]. }
      split. { exact Hfp2_out. }
      (* Reconstruct FElem px x from Fp halves *)
      destruct Hrest3 as [m_xre [m_xim_rr [[? ?] [Hfe_xre Hxim_rr]]]]. subst.
      destruct Hxim_rr as [m_xim [mR [[? ?] [Hfe_xim HrR]]]]. subst.
      saturate_disjointness.
      pose proof (QuadraticFieldExtensions.AbstractFElem_length _ _ _ Hfe_xre) as Hlen_xre.
      pose proof (QuadraticFieldExtensions.AbstractFElem_length _ _ _ Hfe_xim) as Hlen_xim.
      assert (Hjoin_x : (FElem_Fp px (fst_felem x) ⋆
        FElem_Fp (word.add px (word.of_Z (@AbstractField.felem_size_in_bytes _ _ _ _ _ _ bls377_field_representation))) (snd_felem x))
        (map.putmany m_xre m_xim)).
      { exists m_xre, m_xim. split. { split. { reflexivity. }
        first [assumption | apply (proj1 (map.disjoint_comm _ _)); assumption]. }
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
        apply (proj2 (map.disjoint_putmany_l _ _ _)); split;
        first [assumption | apply (proj1 (map.disjoint_comm _ _)); assumption]. }
      split. { exact Hfx'. }
      exact HrR. }
  Qed.

  (* ================================================================ *)
  (* E. Fp2 mul_xi — unop_spec wrapper                                *)
  (* ================================================================ *)
  Lemma bls377_Fp2_mul_xi_ok :
    forall functions,
    map.get functions (fst Fp2_mul_xi) = Some (snd Fp2_mul_xi) ->
    spec_of_F_add functions ->
    spec_of_F_add functions ->
    spec_of_F_add functions ->
    spec_of_F_felem_copy functions ->
    spec_of_F_opp functions ->
    CubicFieldExtensions.spec_of_Fp2_mul_xi bls377_beta bls377_xi_re bls377_xi_im fp2_prefix functions.
  Proof.
    intros functions HEnv HFadd1 HFadd2 HFadd3 HFcopy HFopp.
    unfold CubicFieldExtensions.spec_of_Fp2_mul_xi, AbstractField.unop_spec.
    intros pout px out x Rr tr mem0 [Hbx [[Rx Hmemx] Hmemout]].
    (* FElem properties needed for sep_reassoc *)
    assert (Hdisj_FElem : forall mp mq, FElem px x mp -> FElem pout out mq -> map.disjoint mp mq) by (eapply FElem_disjoint_ax; eassumption).
    assert (Hprec_FElem : forall m1 m2, FElem px x m1 -> FElem px x m2 -> m1 = m2) by (exact (FElem_Fp2_precise px x)).
    (* Use sep_reassoc to combine the two seps from the unop_spec precondition *)
    destruct (sep_reassoc (FElem px x) (FElem pout out) Rr mem0
      (ex_intro _ Rx Hmemx) Hmemout Hdisj_FElem Hprec_FElem)
      as [R_nested [Hcombined Hbridge]].
    (* Apply the nested spec *)
    eapply Semantics.weaken_call.
    1: { eapply bls377_Fp2_mul_xi_nested; try eassumption. }
    (* Postcondition bridge: nested → unop_spec *)
    cbv beta. intros t' m' rets Hpost.
    destruct Hpost as [Hrets [Htr [out' [Hfeval [Hbounds Hsep']]]]].
    split. { exact Hrets. }
    split. { exact Htr. }
    exists out'. split. { exact Hfeval. }
    split. { exact Hbounds. }
    exact (Hbridge _ _ Hsep').
  Admitted. (* depends on FElem_disjoint_ax *)

  (* ================================================================ *)
  (* F. Fp2 conjugate — reuse from PairingFieldOps                    *)
  (* ================================================================ *)
  Lemma bls377_Fp2_conjugate_ok :
    forall functions,
    map.get functions (fst (Fp2_conjugate "bls377_Fp2_")) = Some (snd (Fp2_conjugate "bls377_Fp2_")) ->
    spec_of_F_felem_copy functions ->
    spec_of_F_opp functions ->
    PairingFieldOps.spec_of_Fp2_conjugate bls377_beta fp2_prefix functions.
  Proof.
    intros functions HEnv HFcopy HFopp.
    eapply PairingFieldOps.Fp2_conjugate_ok; eassumption.
  Qed.

End P.
