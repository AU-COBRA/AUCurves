(** Test file for bls377_Fp2_inv proof — compile to check. *)

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
Require Import Spec.BLS12Pairing.Fp6.
Require Import Bedrock.Field.FieldExtensions.PairingFieldOps.
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
  Local Instance spec_of_F_opp : spec_of (@AbstractField.opp _ prime_field_parameters) :=
    AbstractField.unop_spec AbstractField.un_opp (F:=F).
  Local Instance spec_of_F_felem_copy : spec_of (AbstractField.felem_copy (F:=F)) :=
    AbstractField.spec_of_felem_copy (F:=F).

  Local Notation FElem_Fp := (@AbstractField.FElem _ _ _ _ _ _ bls377_field_representation).
  Local Notation offset_word :=
    (word.of_Z (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bls377_field_representation))).

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
  Local Notation Fsub := (@F.sub PrimeField.M_pos).
  Local Notation Finv := (@F.inv PrimeField.M_pos).
  Local Notation Fone := (@F.one PrimeField.M_pos).

  (* For Montgomery, tight_bounds = loose_bounds *)
  Local Lemma Fp_bounds_eq :
    @AbstractField.tight_bounds _ _ _ _ _ _ bls377_field_representation =
    @AbstractField.loose_bounds _ _ _ _ _ _ bls377_field_representation.
  Proof. reflexivity. Qed.

  (* solve_bounds: for Montgomery, tight=loose so any bounded_by H works *)
  Local Ltac solve_bounds :=
    first
      [ assumption
      | (* Try to find a bounded_by hypothesis with the same felem but different bounds *)
        match goal with
        | H : @AbstractField.bounded_by _ _ _ _ _ _ bls377_field_representation ?b1 ?x
          |- @AbstractField.bounded_by _ _ _ _ _ _ bls377_field_representation ?b2 ?x =>
            rewrite Fp_bounds_eq in H |- *; exact H
        | H : @AbstractField.bounded_by _ _ _ _ _ _ bls377_field_representation ?b1 ?x
          |- @AbstractField.bounded_by _ _ _ _ _ _ bls377_field_representation ?b2 _ =>
            first [ exact H
                  | (rewrite Fp_bounds_eq; exact H)
                  | (rewrite <- Fp_bounds_eq; exact H)
                  | (rewrite Fp_bounds_eq in H; exact H)
                  | (rewrite <- Fp_bounds_eq in H; exact H) ]
        end ].

  Local Lemma five_times (v : Fp) :
    Fadd (Fadd (Fadd v v) (Fadd v v)) v = Fmul (F.of_Z PrimeField.M_pos 5) v.
  Proof. change (F.of_Z PrimeField.M_pos 5) with (Fadd (Fadd Fone Fone) (Fadd Fone (Fadd Fone Fone))).
    ring. Qed.

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
  (* Nested-sep version of Fp2 inv (like mul_xi_nested)                *)
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
            QuadraticExtensions.invp2 PrimeField.M_pos bls377_beta
              (@AbstractField.feval _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep x) /\
          @AbstractField.bounded_by _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep
            (@AbstractField.loose_bounds _ bls377_Fp2_params _ _ _ _ bls377_Fp2_rep) out' /\
          (FElem pout out' ⋆ (FElem px x ⋆ Rr)) mem').
  Proof.
    intros functions HEnv HFsqr1 HFsqr2 HFadd1 HFadd2 HFadd3 HFadd4
      HFinv1 HFmul1 HFsub1 HFsub2 HFmul2.
    intros pout px out x Rr tr mem0 Hbx Hsep.
    eapply start_func; [exact HEnv | clear HEnv].
    cbv match beta delta [WeakestPrecondition.func Fp2_inv
      bls12_377_Fp2.expr_2nd_felem bls12_377_Fp2.felem_offset].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* Setup: destruct seps, split Fp2 into Fp halves *)
    destruct Hsep as [m_x [m_or [[? ?] [Hfx Hor]]]].
    destruct Hor as [m_o [mRr [[? ?] [Hfo Hr]]]]. subst.
    wp_fp2_split bls377_beta fp2_prefix Hfo.
    wp_fp2_split bls377_beta fp2_prefix Hfx.
    cbv [AbstractField.bounded_by bls377_Fp2_rep
         QuadraticFieldExtensionsSpecs.Fp2_field_representation] in Hbx.
    destruct Hbx as [Hbx_re Hbx_im].
    (* Hbx_re/Hbx_im have the form:
       (let ... := bls377_field_representation in bounded_by) tight_bounds (fst/snd_felem x)
       This is definitionally equal to AbstractField.bounded_by tight_bounds (fst/snd_felem x).
       We unfold the let to make exact/change work. *)
    change ((let (_, _, _, _, _, _, _, _, _, _, bounded_by, _, _) as FieldRepresentation
      return (_ -> _ -> Prop) := bls377_field_representation in bounded_by))
      with (@AbstractField.bounded_by _ _ _ _ _ _ bls377_field_representation) in Hbx_re, Hbx_im.
    saturate_disjointness.
    (* 3 stackallocs *)
    wp_stk_lift. wp_stk_lift. wp_stk_lift.
    (* Build master sep for ecancel_assumption *)
    assert (Hmsep :
      (FElem_Fp a sv ⋆
       (FElem_Fp a0 sv0 ⋆
        (FElem_Fp a1 sv1 ⋆
         (FElem_Fp px (fst_felem x) ⋆
          (FElem_Fp (word.add px offset_word) (snd_felem x) ⋆
           (FElem_Fp pout (fst_felem out) ⋆
            (FElem_Fp (word.add pout offset_word) (snd_felem out) ⋆
             Rr)))))))
      (map.putmany (map.putmany (map.putmany (map.putmany (map.putmany m1 m2) (map.putmany (map.putmany m m0) mRr)) mS) mS0) mS1)).
    { build_sep_reorder. }
    (* === 11 Fp-level calls === *)
    (* Convert tight_bounds hypotheses to also work as loose_bounds *)
    pose proof (eq_rect _ (fun b => AbstractField.bounded_by b (fst_felem x)) Hbx_re _ Fp_bounds_eq) as Hbx_re_l.
    pose proof (eq_rect _ (fun b => AbstractField.bounded_by b (snd_felem x)) Hbx_im _ Fp_bounds_eq) as Hbx_im_l.
    (* === 11 Fp-level calls === *)
    (* Call 1: sqr(asq, x.re) — asq = a^2, sqr needs loose_bounds *)
    eapply Semantics.weaken_call.
    1: { eapply HFsqr1. fold_offset.
         split; [exact Hbx_re_l |].
         split; [eexists; ecancel_assumption |].
         ecancel_assumption. }
    wp_postcall.
    (* Call 2: sqr(bsq, x.im) — bsq = b^2 *)
    eapply Semantics.weaken_call.
    1: { eapply HFsqr2. fold_offset.
         split; [exact Hbx_im_l |].
         split; [eexists; ecancel_assumption |].
         ecancel_assumption. }
    wp_postcall.
    (* Call 3: add(norm, bsq, bsq) — norm = 2b^2, add needs tight_bounds *)
    eapply Semantics.weaken_call.
    1: { eapply HFadd1. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         (* add xbounds=tight, but sqr outbounds=tight. *)
         all: solve_bounds. }
    wp_postcall.
    (* Call 4: add(norm, norm, norm) — norm = 4b^2 *)
    eapply Semantics.weaken_call.
    1: { eapply HFadd2. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: solve_bounds. }
    wp_postcall.
    (* Call 5: add(norm, norm, bsq) — norm = 5b^2 *)
    eapply Semantics.weaken_call.
    1: { eapply HFadd3. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: solve_bounds. }
    wp_postcall.
    (* Call 6: add(norm, asq, norm) — norm = a^2 + 5b^2 *)
    eapply Semantics.weaken_call.
    1: { eapply HFadd4. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: solve_bounds. }
    wp_postcall.
    (* Call 7: inv(norm, norm) — inv needs tight_bounds, add output is loose *)
    eapply Semantics.weaken_call.
    1: { eapply HFinv1. fold_offset.
         split; [solve_bounds |].
         split; [eexists; ecancel_assumption |].
         ecancel_assumption. }
    wp_postcall.
    (* Call 8: mul(out.re, x.re, norm) — mul needs loose_bounds *)
    eapply Semantics.weaken_call.
    1: { eapply HFmul1. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: first [exact Hbx_re_l | solve_bounds]. }
    wp_postcall.
    (* Call 9: sub(asq, bsq, bsq) — sub needs tight_bounds *)
    eapply Semantics.weaken_call.
    1: { eapply HFsub1. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: solve_bounds. }
    wp_postcall.
    (* Call 10: sub(asq, asq, x.im) — sub needs tight for y *)
    eapply Semantics.weaken_call.
    1: { eapply HFsub2. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: first [exact Hbx_im | solve_bounds]. }
    wp_postcall.
    (* Call 11: mul(out.im, asq, norm) — mul needs loose_bounds *)
    eapply Semantics.weaken_call.
    1: { eapply HFmul2. fold_offset.
         refine (conj _ (conj _ (conj (ex_intro _ _ _) (conj (ex_intro _ _ _) _)))).
         5: ecancel_assumption. 4: ecancel_assumption. 3: ecancel_assumption.
         all: solve_bounds. }
    wp_postcall.
    (* === Final postcondition: stack dealloc + feval + bounds + sep === *)
    (* The postcondition from the last wp_postcall should have left us in a state
       where we need to prove the stack dealloc + return values.
       Let's see what hypotheses contain feval info. *)
    (* After 11 calls, the feval hypotheses should be named H1, H4, H7, ... *)
    (* Actually, wp_postcall uses ? for names. Let me check what we have. *)
    (* The last wp_postcall for call 11 should have:
       - An feval equality for the last mul output
       - A bounds hypothesis
       - A sep hypothesis for the current memory

       We need to:
       1. Dealloc 3 stacks
       2. Show rets = [] /\ tr = tr'
       3. exists out', feval = invp2 ..., bounded_by, sep
    *)
    (* Try to inspect the hypotheses *)
    (* Destruct the final sep — find it by matching *)
    match goal with
    | H : (_ ⋆ _) ?m |- context [map.split ?m _ _] =>
      wp_destruct_sep H
    end.
    saturate_disjointness.
    (* Convert 3 stack FElems to anybytes for deallocation *)
    (* Find each stack FElem by address and convert *)
    let convert_stk addr :=
      match goal with
      | Hstk : FElem_Fp addr _ ?mstk |- _ =>
        pose proof (AbstractField.FElem_to_bytes addr _ mstk Hstk) as ?Hab;
        unfold AbstractField.Placeholder in * |- *
      end in
    convert_stk a1; convert_stk a0; convert_stk a.
    (* 3 stack deallocations *)
    (* Dealloc norm (a1) *)
    eexists _, _. split. { eassumption. }
    split. { unfold map.split. split.
      - rewrite !map.putmany_assoc. reflexivity.
      - map_disjoint_auto. }
    (* Dealloc bsq (a0) *)
    eexists _, _. split. { eassumption. }
    split. { unfold map.split. split.
      - rewrite !map.putmany_assoc. reflexivity.
      - map_disjoint_auto. }
    (* Dealloc asq (a) *)
    eexists _, _. split. { eassumption. }
    split. { unfold map.split. split.
      - rewrite !map.putmany_assoc. reflexivity.
      - map_disjoint_auto. }
    (* list_map simplification *)
    cbv [list_map WeakestPrecondition.get].
    split. { reflexivity. }
    split. { reflexivity. }
    (* exists out' with feval, bounds, sep *)
    (* TODO: needs feval proof, bounds proof, sep reconstruction *)
    Admitted.

End P.
