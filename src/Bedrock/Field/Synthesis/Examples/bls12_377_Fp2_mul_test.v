(** Test file for bls377_Fp2_mul proof — fast iteration.
    Adapts QuadraticFieldExtensionsMul.v generic proof pattern
    to BLS12-377 specific Fp2_mul body (Karatsuba with beta=-5). *)

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
  Local Notation Fone := (@F.one PrimeField.M_pos).

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

  (* Helper: split Fp2 FElem inside a sep *)
  Local Lemma fp2_sep_split px x Rx mem :
    (@AbstractField.FElem _ _ _ _ _ _ bls377_Fp2_rep px x ⋆ Rx) mem ->
    (FElem_Fp px (fst_felem x) ⋆
      (FElem_Fp (word.add px offset_word) (snd_felem x) ⋆ Rx)) mem.
  Proof.
    intros [m_fp2 [m_r [[Heq0 Hd0] [Hfp2 Hrr]]]].
    pose proof (QuadraticFieldExtensions.Fp2_raw_FElem_split
      beta fp2_prefix px x m_fp2 Hfp2)
      as [m_fst [m_snd [[Heq2 Hd2] [Hfst Hsnd]]]]. subst m_fp2.
    pose proof (proj1 (map.disjoint_putmany_l _ _ _) Hd0) as [Hd_fst_r Hd_snd_r].
    exists m_fst, (map.putmany m_snd m_r).
    split; [split |].
    { subst mem. rewrite map.putmany_assoc. reflexivity. }
    { apply (proj2 (map.disjoint_putmany_r _ _ _)). split; [exact Hd2 | exact Hd_fst_r]. }
    split; [exact Hfst |].
    exists m_snd, m_r.
    split; [split; [reflexivity | exact Hd_snd_r] |].
    split; [exact Hsnd | exact Hrr].
  Qed.

  Lemma bls377_Fp2_mul_ok :
    forall functions,
    map.get functions (fst Fp2_mul) = Some (snd Fp2_mul) ->
    spec_of_F_mul functions -> spec_of_F_mul functions ->
    spec_of_F_add functions -> spec_of_F_add functions ->
    spec_of_F_mul functions ->
    spec_of_F_sub functions -> spec_of_F_sub functions ->
    spec_of_F_add functions -> spec_of_F_add functions ->
    spec_of_F_add functions -> spec_of_F_sub functions ->
    AbstractField.binop_spec AbstractField.bin_mul (F:=F*F) functions.
  Proof.
    intros functions HEnv HFmul1 HFmul2 HFadd1 HFadd2 HFmul3
      HFsub1 HFsub2 HFadd3 HFadd4 HFadd5 HFsub3.
    unfold AbstractField.binop_spec.
    intros pout px py old_out x y Rr tr mem0
      [Hbx [Hby [[Rx Hmemx] [[Ry Hmemy] Hmemout]]]].
    destruct Hmemout as [m_o [m_r [[? Hd_or] [Hfo Hr]]]]. subst mem0.
    eapply start_func; [exact HEnv | clear HEnv].
    cbv match beta delta [WeakestPrecondition.func Fp2_mul
      bls12_377_Fp2.expr_2nd_felem bls12_377_Fp2.felem_offset].
    eexists. split. { exact eq_refl. }
    repeat straightline.
    (* Split bounds *)
    cbv [AbstractField.bounded_by bls377_Fp2_rep
         QuadraticFieldExtensionsSpecs.Fp2_field_representation] in Hbx, Hby.
    destruct Hbx as [Hbx_re Hbx_im].
    destruct Hby as [Hby_re Hby_im].
    (* Split out into Fp halves *)
    wp_fp2_split beta fp2_prefix Hfo.
    (* 3 stackallocs — Hmemx, Hmemy get lifted *)
    wp_stk_lift. wp_stk_lift. wp_stk_lift.
    (* Split Hmemx, Hmemy into Fp halves *)
    apply fp2_sep_split in Hmemx.
    apply fp2_sep_split in Hmemy.
    fold_offset.
    (* Build master sep from out-basis + stacks for output FElem access *)
    assert (Hmsep :
      (FElem_Fp pout (fst_felem old_out) ⋆
       (FElem_Fp (word.add pout (word.of_Z (@AbstractField.felem_size_in_bytes _ _ _ _ _ _ bls377_field_representation))) (snd_felem old_out) ⋆
        (Rr ⋆
         (FElem_Fp a sv ⋆
          (FElem_Fp a0 sv0 ⋆
           (FElem_Fp a1 sv1 ⋆ emp True))))))
      (map.putmany (map.putmany (map.putmany (map.putmany (map.putmany m m0) m_r) mS) mS0) mS1)).
    { build_sep_reorder. }
    (* === CALL 1: mul(v0, x.re, y.re) — v0 = ac === *)
    eapply Semantics.weaken_call.
    1: { eapply HFmul1.
         split; [exact Hbx_re |]. split; [exact Hby_re |].
         split; [eexists; ecancel_assumption |].
         split; [eexists; ecancel_assumption |].
         ecancel_assumption. }
    wp_postcall.
    (* === CALL 2: mul(v1, x.im, y.im) — v1 = bd === *)
    eapply Semantics.weaken_call.
    1: { eapply HFmul2.
         split; [exact Hbx_im |]. split; [exact Hby_im |].
         split; [eexists; ecancel_assumption |].
         split; [eexists; ecancel_assumption |].
         ecancel_assumption. }
    wp_postcall.
    (* === CALL 3: add(v2, x.re, x.im) — v2 = a+b === *)
    eapply Semantics.weaken_call.
    1: { eapply HFadd1.
         split; [exact Hbx_re |]. split; [exact Hbx_im |].
         split; [eexists; ecancel_assumption |].
         split; [eexists; ecancel_assumption |].
         ecancel_assumption. }
    wp_postcall.
    (* === CALL 4: add(out.im, y.re, y.im) — out.im = c+d === *)
    eapply Semantics.weaken_call.
    1: { eapply HFadd2.
         split; [exact Hby_re |]. split; [exact Hby_im |].
         split; [eexists; ecancel_assumption |].
         split; [eexists; ecancel_assumption |].
         ecancel_assumption. }
    wp_postcall.
    (* === CALL 5: mul(out.im, out.im, v2) — out.im = (c+d)(a+b) === *)
    eapply Semantics.weaken_call.
    1: { eapply HFmul3.
         split; [assumption |]. split; [assumption |].
         split; [eexists; ecancel_assumption |].
         split; [eexists; ecancel_assumption |].
         ecancel_assumption. }
    wp_postcall.
    (* === CALL 6: sub(out.im, out.im, v0) — out.im -= ac === *)
    eapply Semantics.weaken_call.
    1: { eapply HFsub1.
         split; [assumption |]. split; [assumption |].
         split; [eexists; ecancel_assumption |].
         split; [eexists; ecancel_assumption |].
         ecancel_assumption. }
    wp_postcall.
    (* === CALL 7: sub(out.im, out.im, v1) — out.im = ad+bc === *)
    eapply Semantics.weaken_call.
    1: { eapply HFsub2.
         split; [assumption |]. split; [assumption |].
         split; [eexists; ecancel_assumption |].
         split; [eexists; ecancel_assumption |].
         ecancel_assumption. }
    wp_postcall.
    (* === CALL 8: add(v2, v1, v1) — v2 = 2bd === *)
    eapply Semantics.weaken_call.
    1: { eapply HFadd3.
         split; [assumption |]. split; [assumption |].
         split; [eexists; ecancel_assumption |].
         split; [eexists; ecancel_assumption |].
         ecancel_assumption. }
    wp_postcall.
    (* === CALL 9: add(v2, v2, v2) — v2 = 4bd === *)
    eapply Semantics.weaken_call.
    1: { eapply HFadd4.
         split; [assumption |]. split; [assumption |].
         split; [eexists; ecancel_assumption |].
         split; [eexists; ecancel_assumption |].
         ecancel_assumption. }
    wp_postcall.
    (* === CALL 10: add(v2, v2, v1) — v2 = 5bd === *)
    eapply Semantics.weaken_call.
    1: { eapply HFadd5.
         split; [assumption |]. split; [assumption |].
         split; [eexists; ecancel_assumption |].
         split; [eexists; ecancel_assumption |].
         ecancel_assumption. }
    wp_postcall.
    (* === CALL 11: sub(out.re, v0, v2) — out.re = ac - 5bd === *)
    eapply Semantics.weaken_call.
    1: { eapply HFsub3.
         split; [assumption |]. split; [assumption |].
         split; [eexists; ecancel_assumption |].
         split; [eexists; ecancel_assumption |].
         ecancel_assumption. }
    wp_postcall.
  Admitted.

End P.
